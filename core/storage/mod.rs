//! The storage layer.
//!
//! This module contains the storage layer for Limbo. The storage layer is
//! responsible for managing access to the database and its pages. The main
//! interface to the storage layer is the `Pager` struct, which is
//! responsible for managing the database file and the pages it contains.
//!
//! Pages in a database are stored in one of the following to data structures:
//! `DatabaseStorage` or `Wal`. The `DatabaseStorage` trait is responsible
//! for reading and writing pages to the database file, either local or
//! remote. The `Wal` struct is responsible for managing the write-ahead log
//! for the database, also either local or remote.

use std::rc::Rc;
use std::cell::RefCell;
use crate::{Buffer, CompletionEnum, File, LimboError};

pub(crate) mod btree;
pub(crate) mod buffer_pool;
pub(crate) mod page_cache;
pub(crate) mod page;
pub(crate) mod sqlite3_ondisk;
pub(crate) mod wal;

pub trait Storage {
    fn readPage(&self, pageIndex: usize, c: Rc<CompletionEnum>) -> crate::Result<()>;
    fn writePage(&self,
                 page_idx: usize,
                 buffer: Rc<RefCell<Buffer>>,
                 c: Rc<CompletionEnum>) -> crate::Result<()>;
    fn sync(&self, c: Rc<CompletionEnum>) -> crate::Result<()>;
}

#[cfg(feature = "fs")]
pub struct FileStorage {
    file: Rc<dyn File>,
}

#[cfg(feature = "fs")]
impl Storage for FileStorage {
    fn readPage(&self, pageIndex: usize, c: Rc<CompletionEnum>) -> crate::Result<()> {
        let readCompletion = match &(*c) {
            CompletionEnum::Read(r) => r,
            _ => unreachable!(),
        };

        let size = readCompletion.buf().len();

        assert!(pageIndex > 0);

        if !(512..=65536).contains(&size) || size & (size - 1) != 0 {
            return Err(LimboError::NotDbFile);
        }

        let pos = (pageIndex - 1) * size;

        self.file.pread(pos, c)?;

        Ok(())
    }

    fn writePage(&self,
                 page_idx: usize,
                 buffer: Rc<RefCell<Buffer>>,
                 c: Rc<CompletionEnum>) -> crate::Result<()> {
        let buffer_size = buffer.borrow().len();
        assert!(buffer_size >= 512);
        assert!(buffer_size <= 65536);
        assert_eq!((buffer_size & (buffer_size - 1)), 0);
        let pos = (page_idx - 1) * buffer_size;
        self.file.pwrite(pos, buffer, c)?;
        Ok(())
    }

    fn sync(&self, c: Rc<CompletionEnum>) -> crate::Result<()> {
        self.file.sync(c)
    }
}

#[cfg(feature = "fs")]
impl FileStorage {
    pub fn new(file: Rc<dyn crate::io::File>) -> Self {
        Self { file }
    }
}