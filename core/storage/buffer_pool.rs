use crate::io::BufferData;
use std::cell::RefCell;
use std::pin::Pin;

/// 以page的大小为粒度的
pub struct BufferPool {
    pub availBuffers: RefCell<Vec<BufferData>>,
    /// bufferSize用的是page大小相同
    bufferSize: usize,
}

impl BufferPool {
    pub fn new(bufferSize: usize) -> Self {
        Self {
            availBuffers: RefCell::new(Vec::new()),
            bufferSize,
        }
    }

    pub fn get(&self) -> BufferData {
        let mut freeBufferDatas = self.availBuffers.borrow_mut();
        if let Some(buffer) = freeBufferDatas.pop() {
            buffer
        } else {
            Pin::new(vec![0; self.bufferSize])
        }
    }

    pub fn put(&self, buffer: BufferData) {
        let mut free_buffers = self.availBuffers.borrow_mut();
        free_buffers.push(buffer);
    }
}
