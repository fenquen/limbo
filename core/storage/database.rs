use crate::{error::LimboError, io::CompletionEnum, Buffer, Result};
use std::{cell::RefCell, rc::Rc};

/// DatabaseStorage is an interface a database file that consists of pages.
///
/// The purpose of this trait is to abstract the upper layers of Limbo from
/// the storage medium. A database can either be a file on disk, like in SQLite,
/// or something like a remote page server service.
pub trait Storage {
    fn readPage(&self, pageIndex: usize, c: Rc<CompletionEnum>) -> Result<()>;
    fn write_page(&self,
                  page_idx: usize,
                  buffer: Rc<RefCell<Buffer>>,
                  c: Rc<CompletionEnum>) -> Result<()>;
    fn sync(&self, c: Rc<CompletionEnum>) -> Result<()>;
}

#[cfg(feature = "fs")]
pub struct FileStorage {
    file: Rc<dyn crate::io::File>,
}

#[cfg(feature = "fs")]
impl Storage for FileStorage {
    fn readPage(&self, pageIndex: usize, c: Rc<CompletionEnum>) -> Result<()> {
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

    fn write_page(&self,
                  page_idx: usize,
                  buffer: Rc<RefCell<Buffer>>,
                  c: Rc<CompletionEnum>) -> Result<()> {
        let buffer_size = buffer.borrow().len();
        assert!(buffer_size >= 512);
        assert!(buffer_size <= 65536);
        assert_eq!((buffer_size & (buffer_size - 1)), 0);
        let pos = (page_idx - 1) * buffer_size;
        self.file.pwrite(pos, buffer, c)?;
        Ok(())
    }

    fn sync(&self, c: Rc<CompletionEnum>) -> Result<()> {
        self.file.sync(c)
    }
}

#[cfg(feature = "fs")]
impl FileStorage {
    pub fn new(file: Rc<dyn crate::io::File>) -> Self {
        Self { file }
    }
}
