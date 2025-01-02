use crate::{util::normalize_ident, Result};
use core::fmt;
use fallible_iterator::FallibleIterator;
use log::trace;
use sqlite3_parser::ast::{Expr, Literal, TableOptions};
use sqlite3_parser::{
    ast::{Cmd, CreateTableBody, QualifiedName, ResultColumn, Stmt},
    lexer::sql::Parser,
};
use std::collections::HashMap;
use std::rc::Rc;

pub struct Schema {
    pub tables: HashMap<String, Rc<BTreeTable>>,

    /// table_name to list of indexes for the table
    pub indexes: HashMap<String, Vec<Rc<Index>>>,
}

impl Schema {
    pub fn new() -> Self {
        let mut tables: HashMap<String, Rc<BTreeTable>> = HashMap::new();
        tables.insert("sqlite_schema".to_string(), Rc::new(buildSqliteSchemaTable()));
        let indexes: HashMap<String, Vec<Rc<Index>>> = HashMap::new();
        Self { tables, indexes }
    }

    pub fn addTbl(&mut self, table: Rc<BTreeTable>) {
        let name = normalize_ident(&table.name);
        self.tables.insert(name, table);
    }

    pub fn getTbl(&self, name: &str) -> Option<Rc<BTreeTable>> {
        let name = normalize_ident(name);
        self.tables.get(&name).cloned()
    }

    pub fn add_index(&mut self, index: Rc<Index>) {
        let table_name = normalize_ident(&index.table_name);
        self.indexes.entry(table_name).or_default().push(index.clone())
    }
}

#[derive(Clone, Debug)]
pub enum Table {
    BTree(Rc<BTreeTable>),
    Index(Rc<Index>),
    Pseudo(Rc<PseudoTable>),
}

impl Table {
    pub fn is_pseudo(&self) -> bool {
        matches!(self, Table::Pseudo(_))
    }

    pub fn get_rowid_alias_column(&self) -> Option<(usize, &Column)> {
        match self {
            Table::BTree(table) => table.get_rowid_alias_column(),
            Table::Index(_) => None,
            Table::Pseudo(_) => None,
        }
    }

    pub fn column_is_rowid_alias(&self, col: &Column) -> bool {
        match self {
            Table::BTree(table) => table.column_is_rowid_alias(col),
            Table::Index(_) => false,
            Table::Pseudo(_) => false,
        }
    }

    pub fn get_name(&self) -> &str {
        match self {
            Table::BTree(table) => &table.name,
            Table::Index(index) => &index.name,
            Table::Pseudo(_) => "",
        }
    }

    pub fn column_index_to_name(&self, index: usize) -> Option<&str> {
        match self {
            Table::BTree(table) => match table.columns.get(index) {
                Some(column) => Some(&column.name),
                None => None,
            },
            Table::Index(i) => match i.columns.get(index) {
                Some(column) => Some(&column.name),
                None => None,
            },
            Table::Pseudo(table) => match table.columns.get(index) {
                Some(_) => None,
                None => None,
            },
        }
    }

    pub fn get_column(&self, name: &str) -> Option<(usize, &Column)> {
        match self {
            Table::BTree(table) => table.get_column(name),
            Table::Index(_) => unimplemented!(),
            Table::Pseudo(table) => table.get_column(name),
        }
    }

    pub fn get_column_at(&self, index: usize) -> &Column {
        match self {
            Table::BTree(table) => table.columns.get(index).unwrap(),
            Table::Index(_) => unimplemented!(),
            Table::Pseudo(table) => table.columns.get(index).unwrap(),
        }
    }

    pub fn columns(&self) -> &Vec<Column> {
        match self {
            Table::BTree(table) => &table.columns,
            Table::Index(_) => unimplemented!(),
            Table::Pseudo(table) => &table.columns,
        }
    }

    pub fn hasRowId(&self) -> bool {
        match self {
            Table::BTree(table) => table.has_rowid,
            Table::Index(_) => unimplemented!(),
            Table::Pseudo(_) => unimplemented!(),
        }
    }
}

impl PartialEq for Table {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Table::BTree(a), Table::BTree(b)) => Rc::ptr_eq(a, b),
            (Table::Pseudo(a), Table::Pseudo(b)) => Rc::ptr_eq(a, b),
            _ => false,
        }
    }
}

#[derive(Debug)]
pub struct BTreeTable {
    pub rootPage: usize,
    pub name: String,
    pub primary_key_column_names: Vec<String>,
    pub columns: Vec<Column>,
    pub has_rowid: bool,
}

impl BTreeTable {
    pub fn get_rowid_alias_column(&self) -> Option<(usize, &Column)> {
        if self.primary_key_column_names.len() == 1 {
            let (idx, col) = self.get_column(&self.primary_key_column_names[0]).unwrap();
            if self.column_is_rowid_alias(col) {
                return Some((idx, col));
            }
        }
        None
    }

    pub fn column_is_rowid_alias(&self, col: &Column) -> bool {
        col.is_rowid_alias
    }

    pub fn get_column(&self, name: &str) -> Option<(usize, &Column)> {
        let name = normalize_ident(name);
        for (i, column) in self.columns.iter().enumerate() {
            if column.name == name {
                return Some((i, column));
            }
        }
        None
    }

    pub fn from_sql(sql: &str, root_page: usize) -> Result<BTreeTable> {
        let mut parser = Parser::new(sql.as_bytes());
        let cmd = parser.next()?;
        match cmd {
            Some(Cmd::Stmt(Stmt::CreateTable { tbl_name, body, .. })) => {
                create_table(tbl_name, body, root_page)
            }
            _ => todo!("Expected CREATE TABLE statement"),
        }
    }

    #[cfg(test)]
    pub fn to_sql(&self) -> String {
        let mut sql = format!("CREATE TABLE {} (\n", self.name);
        for (i, column) in self.columns.iter().enumerate() {
            if i > 0 {
                sql.push_str(",\n");
            }
            sql.push_str("  ");
            sql.push_str(&column.name);
            sql.push(' ');
            sql.push_str(&column.columnType.to_string());
        }
        sql.push_str(");\n");
        sql
    }
}

#[derive(Debug)]
pub struct PseudoTable {
    pub columns: Vec<Column>,
}

impl PseudoTable {
    pub fn new() -> Self {
        Self { columns: vec![] }
    }

    pub fn add_column(&mut self, name: &str, ty: ColumnType, primary_key: bool) {
        self.columns.push(Column {
            name: normalize_ident(name),
            columnType: ty,
            primary_key,
            is_rowid_alias: false,
        });
    }
    pub fn get_column(&self, name: &str) -> Option<(usize, &Column)> {
        let name = normalize_ident(name);
        for (i, column) in self.columns.iter().enumerate() {
            if column.name == name {
                return Some((i, column));
            }
        }
        None
    }
}

impl Default for PseudoTable {
    fn default() -> Self {
        Self::new()
    }
}

fn create_table(tbl_name: QualifiedName,
                body: CreateTableBody,
                root_page: usize, ) -> Result<BTreeTable> {
    let table_name = normalize_ident(&tbl_name.name.0);
    trace!("creating table {}", table_name);
    let mut has_rowid = true;
    let mut primary_key_column_names = vec![];
    let mut cols = vec![];
    match body {
        CreateTableBody::ColumnsAndConstraints {
            columns,
            constraints,
            options,
        } => {
            if let Some(constraints) = constraints {
                for c in constraints {
                    if let sqlite3_parser::ast::TableConstraint::PrimaryKey { columns, .. } = c.constraint {
                        for column in columns {
                            primary_key_column_names.push(match column.expr {
                                Expr::Id(id) => normalize_ident(&id.0),
                                Expr::Literal(Literal::String(value)) => value.trim_matches('\'').to_owned(),
                                _ => todo!("Unsupported primary key expression"),
                            });
                        }
                    }
                }
            }

            for (col_name, col_def) in columns {
                let name = col_name.0.to_string();
                // Regular sqlite tables have an integer rowid that uniquely identifies a row.
                // Even if you create a table with a column e.g. 'id INT PRIMARY KEY', there will still
                // be a separate hidden rowid, and the 'id' column will have a separate index built for it.
                //
                // However:
                // A column defined as exactly INTEGER PRIMARY KEY is a rowid alias, meaning that the rowid
                // and the value of this column are the same.
                // https://www.sqlite.org/lang_createtable.html#rowids_and_the_integer_primary_key
                let mut typename_exactly_integer = false;
                let ty = match col_def.col_type {
                    Some(data_type) => {
                        // https://www.sqlite.org/datatype3.html
                        let type_name = data_type.name.as_str().to_uppercase();
                        if type_name.contains("INT") {
                            typename_exactly_integer = type_name == "INTEGER";
                            ColumnType::Integer
                        } else if type_name.contains("CHAR")
                            || type_name.contains("CLOB")
                            || type_name.contains("TEXT")
                        {
                            ColumnType::Text
                        } else if type_name.contains("BLOB") || type_name.is_empty() {
                            ColumnType::Blob
                        } else if type_name.contains("REAL")
                            || type_name.contains("FLOA")
                            || type_name.contains("DOUB")
                        {
                            ColumnType::Real
                        } else {
                            ColumnType::Numeric
                        }
                    }
                    None => ColumnType::Null,
                };
                let mut primary_key = col_def.constraints.iter().any(|c| {
                    matches!(
                        c.constraint,
                        sqlite3_parser::ast::ColumnConstraint::PrimaryKey { .. }
                    )
                });
                if primary_key {
                    primary_key_column_names.push(name.clone());
                } else if primary_key_column_names.contains(&name) {
                    primary_key = true;
                }
                cols.push(Column {
                    name: normalize_ident(&name),
                    columnType: ty,
                    primary_key,
                    is_rowid_alias: typename_exactly_integer && primary_key,
                });
            }
            if options.contains(TableOptions::WITHOUT_ROWID) {
                has_rowid = false;
            }
        }
        CreateTableBody::AsSelect(_) => todo!(),
    };
    // flip is_rowid_alias back to false if the table has multiple primary keys
    // or if the table has no rowid
    if !has_rowid || primary_key_column_names.len() > 1 {
        for col in cols.iter_mut() {
            col.is_rowid_alias = false;
        }
    }
    Ok(BTreeTable {
        rootPage: root_page,
        name: table_name,
        has_rowid,
        primary_key_column_names,
        columns: cols,
    })
}

pub fn _build_pseudo_table(columns: &[ResultColumn]) -> PseudoTable {
    let table = PseudoTable::new();
    for column in columns {
        match column {
            ResultColumn::Expr(expr, _as_name) => {
                todo!("unsupported expression {:?}", expr);
            }
            ResultColumn::Star => {
                todo!();
            }
            ResultColumn::TableStar(_) => {
                todo!();
            }
        }
    }
    table
}

#[derive(Debug, Clone)]
pub struct Column {
    pub name: String,
    pub columnType: ColumnType,
    pub primary_key: bool,
    pub is_rowid_alias: bool,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ColumnType {
    Null,
    Text,
    Numeric,
    Integer,
    Real,
    Blob,
}

impl fmt::Display for ColumnType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            ColumnType::Null => "NULL",
            ColumnType::Text => "TEXT",
            ColumnType::Numeric => "NUMERIC",
            ColumnType::Integer => "INTEGER",
            ColumnType::Real => "REAL",
            ColumnType::Blob => "BLOB",
        };
        write!(f, "{}", s)
    }
}

pub fn buildSqliteSchemaTable() -> BTreeTable {
    BTreeTable {
        rootPage: 1,
        name: "sqlite_schema".to_string(),
        has_rowid: true,
        primary_key_column_names: vec![],
        columns: vec![
            Column { // index table
                name: "type".to_string(),
                columnType: ColumnType::Text,
                primary_key: false,
                is_rowid_alias: false,
            },
            Column {
                name: "name".to_string(),
                columnType: ColumnType::Text,
                primary_key: false,
                is_rowid_alias: false,
            },
            Column {
                name: "tbl_name".to_string(),
                columnType: ColumnType::Text,
                primary_key: false,
                is_rowid_alias: false,
            },
            Column {
                name: "rootpage".to_string(),
                columnType: ColumnType::Integer,
                primary_key: false,
                is_rowid_alias: false,
            },
            Column {
                name: "sql".to_string(),
                columnType: ColumnType::Text,
                primary_key: false,
                is_rowid_alias: false,
            },
        ],
    }
}

#[allow(dead_code)]
#[derive(Debug)]
pub struct Index {
    pub name: String,
    pub table_name: String,
    pub rootPage: usize,
    pub columns: Vec<IndexColumn>,
    pub unique: bool,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct IndexColumn {
    pub name: String,
    pub order: Order,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Order {
    Ascending,
    Descending,
}

impl Index {
    pub fn from_sql(sql: &str, root_page: usize) -> Result<Index> {
        let mut parser = Parser::new(sql.as_bytes());
        let cmd = parser.next()?;
        match cmd {
            Some(Cmd::Stmt(Stmt::CreateIndex {
                               idx_name,
                               tbl_name,
                               columns,
                               unique,
                               ..
                           })) => {
                let index_name = normalize_ident(&idx_name.name.0);
                let index_columns =
                    columns.into_iter().map(|col| IndexColumn {
                        name: normalize_ident(&col.expr.to_string()),
                        order: match col.order {
                            Some(sqlite3_parser::ast::SortOrder::Asc) => Order::Ascending,
                            Some(sqlite3_parser::ast::SortOrder::Desc) => Order::Descending,
                            None => Order::Ascending,
                        },
                    }).collect();
                Ok(Index {
                    name: index_name,
                    table_name: normalize_ident(&tbl_name.0),
                    rootPage: root_page,
                    columns: index_columns,
                    unique,
                })
            }
            _ => todo!("Expected create index statement"),
        }
    }
}
