use crate::Result;
use cfg_block::cfg_block;
use std::fmt;
use std::{
    cell::{Ref, RefCell, RefMut},
    fmt::Debug,
    mem::ManuallyDrop,
    pin::Pin,
    rc::Rc,
};

pub trait IO {
    fn openFile(&self, path: &str, flags: OpenFlags, direct: bool) -> Result<Rc<dyn File>>;
    fn runOnce(&self) -> Result<()>;
    fn generate_random_number(&self) -> i64;
    fn get_current_time(&self) -> String;
}

pub trait File {
    fn lock_file(&self, exclusive: bool) -> Result<()>;
    fn unlock_file(&self) -> Result<()>;
    fn pread(&self, pos: usize, c: Rc<CompletionEnum>) -> Result<()>;
    fn pwrite(&self, pos: usize, buffer: Rc<RefCell<Buffer>>, c: Rc<CompletionEnum>) -> Result<()>;
    fn sync(&self, c: Rc<CompletionEnum>) -> Result<()>;
    fn size(&self) -> Result<u64>;
}

pub enum OpenFlags {
    None,
    Create,
}

pub type Complete = dyn Fn(Rc<RefCell<Buffer>>);

/// 含有对应各个action的当complete时候调用的fn
pub enum CompletionEnum {
    Read(ReadCompletion),
    Write(WriteCompletion),
    Sync(SyncCompletion),
}

impl CompletionEnum {
    pub fn complete(&self, result: i32) {
        match self {
            CompletionEnum::Read(r) => r.complete(),
            CompletionEnum::Write(w) => w.complete(result),
            CompletionEnum::Sync(s) => s.complete(result), // fix
        }
    }
}

pub struct ReadCompletion {
    pub buf: Rc<RefCell<Buffer>>,
    pub complete: Box<Complete>,
}

impl ReadCompletion {
    pub fn new(buf: Rc<RefCell<Buffer>>, complete: Box<Complete>) -> Self {
        Self { buf, complete }
    }

    pub fn buf(&self) -> Ref<'_, Buffer> {
        self.buf.borrow()
    }

    pub fn buf_mut(&self) -> RefMut<'_, Buffer> {
        self.buf.borrow_mut()
    }

    pub fn complete(&self) {
        (self.complete)(self.buf.clone());
    }
}

pub type WriteCompleteFn = dyn Fn(i32);

pub struct WriteCompletion {
    pub writeCompleteFn: Box<WriteCompleteFn>,
}

impl WriteCompletion {
    pub fn new(writeCompleteFn: Box<WriteCompleteFn>) -> Self {
        Self { writeCompleteFn }
    }

    pub fn complete(&self, bytes_written: i32) {
        (self.writeCompleteFn)(bytes_written);
    }
}

pub type SyncCompleteFn = dyn Fn(i32);

pub struct SyncCompletion {
    pub complete: Box<SyncCompleteFn>,
}

impl SyncCompletion {
    pub fn new(complete: Box<SyncCompleteFn>) -> Self {
        Self { complete }
    }

    pub fn complete(&self, res: i32) {
        (self.complete)(res);
    }
}

pub type BufferData = Pin<Vec<u8>>;
pub type BufferDataDropFn = Rc<dyn Fn(BufferData)>;

#[derive(Clone)]
pub struct Buffer {
    bufferData: ManuallyDrop<BufferData>,
    bufferDataDropFn: BufferDataDropFn,
}

impl Debug for Buffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self.bufferData)
    }
}

impl Drop for Buffer {
    fn drop(&mut self) {
        let data = unsafe { ManuallyDrop::take(&mut self.bufferData) };
        (self.bufferDataDropFn)(data);
    }
}

impl Buffer {
    pub fn allocate(size: usize, drop: BufferDataDropFn) -> Self {
        let data = ManuallyDrop::new(Pin::new(vec![0; size]));
        Self { bufferData: data, bufferDataDropFn: drop }
    }

    pub fn new(data: BufferData, drop: BufferDataDropFn) -> Self {
        let data = ManuallyDrop::new(data);
        Self { bufferData: data, bufferDataDropFn: drop }
    }

    pub fn len(&self) -> usize {
        self.bufferData.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bufferData.is_empty()
    }

    pub fn as_slice(&self) -> &[u8] {
        &self.bufferData
    }

    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.bufferData
    }

    pub fn as_ptr(&self) -> *const u8 {
        self.bufferData.as_ptr()
    }

    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.bufferData.as_mut_ptr()
    }
}

cfg_block! {
   // #[cfg(target_os = "linux")] {
  //      mod linux;
  //      pub use linux::LinuxIO as PlatformIO;
  //  }

    #[cfg(not(any(target_os = "windows")))] {
        mod generic;
        pub use generic::GenericIO as PlatformIO;
    }
}

mod memory;
pub use memory::MemoryIO;

pub const ENV_DISABLE_FILE_LOCK: &str = "LIMBO_DISABLE_FILE_LOCK";