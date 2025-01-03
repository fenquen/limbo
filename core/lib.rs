#![allow(non_snake_case)]

mod error;
mod function;
mod io;
#[cfg(feature = "json")]
mod json;
mod pseudo;
mod schema;
mod storage;
mod translate;
mod types;
mod util;
mod vdbe;

#[cfg(not(target_family = "wasm"))]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

use fallible_iterator::FallibleIterator;
use log::trace;
use schema::Schema;
use sqlite3_parser::ast;
use sqlite3_parser::{ast::Cmd, lexer::sql::Parser};
use std::cell::Cell;
use std::sync::Weak;
use std::sync::{Arc, OnceLock, RwLock};
use std::{cell::RefCell, rc::Rc};
#[cfg(feature = "fs")]
use storage::FileStorage;
use storage::page_cache::DumbLruPageCache;
use storage::sqlite3_ondisk::{DbHeader, DATABASE_HEADER_SIZE};
pub use storage::wal::WalFile;
pub use storage::wal::WalFileShared;
use util::parse_schema_rows;

use translate::optimizer::optimize_plan;
use translate::planner::prepareSelPlan;

pub use error::LimboError;
pub type Result<T> = std::result::Result<T, error::LimboError>;

pub use io::OpenFlags;
#[cfg(feature = "fs")]
pub use io::PlatformIO;
pub use io::{Buffer, CompletionEnum, File, MemoryIO, WriteCompletion, IO};
pub use storage::buffer_pool::BufferPool;
pub use storage::Storage;
pub use storage::page::Page;
pub use storage::page::Pager;
pub use storage::wal::CheckpointStatus;
pub use storage::wal::Wal;
pub use types::Value;
use crate::storage::{btree, page};
use crate::storage::sqlite3_ondisk::PageType;

pub static DATABASE_VERSION: OnceLock<String> = OnceLock::new();

#[derive(Clone)]
enum TransactionState {
    Write,
    Read,
    None,
}

pub struct Database {
    pager: Rc<Pager>,
    schema: Rc<RefCell<Schema>>,
    dbHeader: Rc<RefCell<DbHeader>>,
    transaction_state: RefCell<TransactionState>,
    // Shared structures of a Database are the parts that are common to multiple threads that might
    // create DB connections.
    shared_page_cache: Arc<RwLock<DumbLruPageCache>>,
    shared_wal: Arc<RwLock<WalFileShared>>,
}

impl Database {
    #[cfg(feature = "fs")]
    pub fn openFile(io: Arc<dyn IO>, dbFilePath: &str) -> Result<Arc<Database>> {
        let dbFile = io.openFile(dbFilePath, OpenFlags::Create, true)?;

        // 文件要是不存在的话会生成然后写入打头的100 byte的db header的
        maybeInitDatabaseFile(&dbFile, &io)?;

        let fileStorage = Rc::new(FileStorage::new(dbFile));

        let dbHeader = Pager::beginOpen(fileStorage.clone())?;
        // wait上边complete的
        io.runOnce()?;

        let pageSize = dbHeader.borrow().pageSize;
        let walFileShared = WalFileShared::open_shared(&io, format!("{}-wal", dbFilePath).as_str(), pageSize)?;
        let bufferPool = Rc::new(BufferPool::new(pageSize as usize));
        let walFile =
            Rc::new(RefCell::new(WalFile::new(io.clone(),
                                              pageSize as usize,
                                              walFileShared.clone(),
                                              bufferPool.clone())));

        DATABASE_VERSION.get_or_init(|| {
            let version = dbHeader.borrow().version_number;
            version.to_string()
        });

        let pageCache = Arc::new(RwLock::new(DumbLruPageCache::new(10)));

        let pager = Rc::new(
            Pager::finishOpen(dbHeader.clone(),
                              fileStorage,
                              walFile,
                              io.clone(),
                              pageCache.clone(),
                              bufferPool)?
        );

        let conn = Rc::new(Conn {
            pager: pager.clone(),
            schema: Rc::new(RefCell::new(Schema::new())),
            dbHeader: dbHeader.clone(),
            db: Weak::new(),
            last_insert_rowid: Cell::new(0),
        });

        let mut schema = Schema::new();
        let rows = conn.query("SELECT * FROM sqlite_schema")?;
        parse_schema_rows(rows, &mut schema, io)?;

        Ok(Arc::new(Database {
            pager,
            schema: Rc::new(RefCell::new(schema)),
            dbHeader,
            transaction_state: RefCell::new(TransactionState::None),
            shared_page_cache: pageCache,
            shared_wal: walFileShared,
        }))
    }

    pub fn connect(self: &Arc<Database>) -> Rc<Conn> {
        Rc::new(Conn {
            pager: self.pager.clone(),
            schema: self.schema.clone(),
            dbHeader: self.dbHeader.clone(),
            last_insert_rowid: Cell::new(0),
            db: Arc::downgrade(self),
        })
    }
}

pub fn maybeInitDatabaseFile(file: &Rc<dyn File>, io: &Arc<dyn IO>) -> Result<()> {
    // no init
    if file.size()? != 0 {
        return Ok(());
    };

    // sqlite文件的打头的100byte是database header
    let dbHeader = DbHeader::default();

    let firstPage =
        page::allocatePage(1, &Rc::new(BufferPool::new(dbHeader.pageSize as usize)), DATABASE_HEADER_SIZE);

    {
        // Create the sqlite_schema table, for this we just need to create the btree page
        // for the first page of the database which is basically like any other btree page
        // but with a 100 byte offset, so we just init the page so that sqlite understands
        // this is a correct page.
        btree::btreeInitPage(&firstPage, PageType::TableLeaf, &dbHeader, DATABASE_HEADER_SIZE);

        let pageContent = firstPage.getMutInner().pageContent.as_mut().unwrap();

        // dbHeader是打头的page的1部分
        pageContent.writeDbHeader(&dbHeader);

        // write the first page to disk synchronously 使用了iouring
        let write1stPageComplete = Rc::new(RefCell::new(false));
        {
            let write1stPageComplete = write1stPageComplete.clone();
            let completion = CompletionEnum::Write(WriteCompletion::new(Box::new(move |_| { *write1stPageComplete.borrow_mut() = true; })));
            file.pwrite(0, pageContent.buffer.clone(), Rc::new(completion))?;
        }

        let mut remainTry = 100;

        loop {
            io.runOnce()?;

            if *write1stPageComplete.borrow() {
                break;
            }

            remainTry -= 1;
            if remainTry == 0 {
                panic!("Database file couldn't be initialized, io loop run for {} iterations and write didn't finish", remainTry);
            }
        }
    }

    Ok(())
}

pub struct Conn {
    pager: Rc<Pager>,
    schema: Rc<RefCell<Schema>>,
    dbHeader: Rc<RefCell<DbHeader>>,
    db: Weak<Database>, // backpointer to the database holding this connection
    last_insert_rowid: Cell<u64>,
}

impl Conn {
    pub fn prepare(self: &Rc<Conn>, sql: impl Into<String>) -> Result<Statement> {
        let sql = sql.into();
        trace!("Preparing: {}", sql);
        let mut parser = Parser::new(sql.as_bytes());
        let cmd = parser.next()?;
        if let Some(cmd) = cmd {
            match cmd {
                Cmd::Stmt(stmt) => {
                    let program = Rc::new(translate::translate(
                        &self.schema.borrow(),
                        stmt,
                        self.dbHeader.clone(),
                        self.pager.clone(),
                        Rc::downgrade(self),
                    )?);
                    Ok(Statement::new(program, self.pager.clone()))
                }
                Cmd::Explain(_stmt) => todo!(),
                Cmd::ExplainQueryPlan(_stmt) => todo!(),
            }
        } else {
            todo!()
        }
    }

    pub fn query(self: &Rc<Conn>, sql: impl Into<String>) -> Result<Option<Rows>> {
        let sql = sql.into();
        trace!("Querying: {}", sql);

        let mut parser = Parser::new(sql.as_bytes());

        if let Some(cmd) = parser.next()? {
            match cmd {
                Cmd::Stmt(stmt) => {
                    let program = Rc::new(
                        translate::translate(&self.schema.borrow(),
                                             stmt,
                                             self.dbHeader.clone(),
                                             self.pager.clone(),
                                             Rc::downgrade(self))?
                    );

                    let stmt = Statement::new(program, self.pager.clone());

                    Ok(Some(Rows { stmt }))
                }
                Cmd::Explain(stmt) => {
                    let program = translate::translate(&self.schema.borrow(),
                                                       stmt,
                                                       self.dbHeader.clone(),
                                                       self.pager.clone(),
                                                       Rc::downgrade(self))?;

                    program.explain();

                    Ok(None)
                }
                Cmd::ExplainQueryPlan(stmt) => {
                    match stmt {
                        ast::Stmt::Select(select) => {
                            let plan = prepareSelPlan(&*self.schema.borrow(), select)?;
                            let plan = optimize_plan(plan)?;
                            println!("{}", plan);
                        }
                        _ => todo!(),
                    }
                    Ok(None)
                }
            }
        } else {
            Ok(None)
        }
    }

    pub fn execute(self: &Rc<Conn>, sql: impl Into<String>) -> Result<()> {
        let sql = sql.into();
        let mut parser = Parser::new(sql.as_bytes());
        let cmd = parser.next()?;
        if let Some(cmd) = cmd {
            match cmd {
                Cmd::Explain(stmt) => {
                    let program = translate::translate(
                        &self.schema.borrow(),
                        stmt,
                        self.dbHeader.clone(),
                        self.pager.clone(),
                        Rc::downgrade(self),
                    )?;
                    program.explain();
                }
                Cmd::ExplainQueryPlan(_stmt) => todo!(),
                Cmd::Stmt(stmt) => {
                    let program = translate::translate(
                        &self.schema.borrow(),
                        stmt,
                        self.dbHeader.clone(),
                        self.pager.clone(),
                        Rc::downgrade(self),
                    )?;
                    let mut state = vdbe::ProgramState::new(program.max_registers);
                    program.step(&mut state, self.pager.clone())?;
                }
            }
        }
        Ok(())
    }

    pub fn flushCache(&self) -> Result<CheckpointStatus> {
        self.pager.flushCache()
    }

    pub fn clear_page_cache(&self) -> Result<()> {
        self.pager.clear_page_cache();
        Ok(())
    }

    pub fn checkpoint(&self) -> Result<()> {
        self.pager.clear_page_cache();
        Ok(())
    }

    /// Close a connection and checkpoint.
    pub fn close(&self) -> Result<()> {
        loop {
            // TODO: make this async?
            match self.pager.checkpoint()? {
                CheckpointStatus::Done => {
                    return Ok(());
                }
                CheckpointStatus::IO => {
                    self.pager.io.runOnce()?;
                }
            };
        }
    }

    pub fn last_insert_rowid(&self) -> u64 {
        self.last_insert_rowid.get()
    }

    fn update_last_rowid(&self, rowid: u64) {
        self.last_insert_rowid.set(rowid);
    }
}

pub struct Statement {
    program: Rc<vdbe::Program>,
    state: vdbe::ProgramState,
    pager: Rc<Pager>,
}

impl Statement {
    pub fn new(program: Rc<vdbe::Program>, pager: Rc<Pager>) -> Self {
        let state = vdbe::ProgramState::new(program.max_registers);
        Self {
            program,
            state,
            pager,
        }
    }

    pub fn step(&mut self) -> Result<RowResult<'_>> {
        let result = self.program.step(&mut self.state, self.pager.clone())?;
        match result {
            vdbe::StepResult::Row(row) => Ok(RowResult::Row(Row { values: row.values })),
            vdbe::StepResult::IO => Ok(RowResult::IO),
            vdbe::StepResult::Done => Ok(RowResult::Done),
        }
    }

    pub fn query(&mut self) -> Result<Rows> {
        let stmt = Statement::new(self.program.clone(), self.pager.clone());
        Ok(Rows::new(stmt))
    }

    pub fn reset(&self) {}
}

pub enum RowResult<'a> {
    Row(Row<'a>),
    IO,
    Done,
}

pub struct Row<'a> {
    pub values: Vec<Value<'a>>,
}

impl<'a> Row<'a> {
    pub fn get<T: crate::types::FromValue<'a> + 'a>(&self, idx: usize) -> Result<T> {
        let value = &self.values[idx];
        T::from_value(value)
    }
}

pub struct Rows {
    stmt: Statement,
}

impl Rows {
    pub fn new(stmt: Statement) -> Self {
        Self { stmt }
    }

    pub fn next_row(&mut self) -> Result<RowResult<'_>> {
        self.stmt.step()
    }
}
