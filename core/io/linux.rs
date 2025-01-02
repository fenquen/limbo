use super::{CompletionEnum, File, OpenFlags, IO};
use crate::{io, LimboError, Result};
use libc::{c_short, flock, iovec, F_SETLK};
use log::{debug, trace};
use nix::fcntl::{FcntlArg, OFlag};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::os::unix::io::AsRawFd;
use std::rc::Rc;
use thiserror::Error;

const MAX_IOVECS: usize = 128;

#[derive(Debug, Error)]
enum LinuxIOError {
    IOUringCQError(i32),
}

// Implement the Display trait to customize error messages
impl fmt::Display for LinuxIOError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LinuxIOError::IOUringCQError(code) => write!(f, "IOUring completion queue error occurred with code {}", code),
        }
    }
}

pub struct LinuxIO {
    inner: Rc<RefCell<InnerLinuxIO>>,
}

impl IO for LinuxIO {
    fn openFile(&self, path: &str, flags: OpenFlags, direct: bool) -> Result<Rc<dyn File>> {
        let file = std::fs::File::options().read(true).write(true).create(matches!(flags, OpenFlags::Create)).open(path)?;

        // direct io
        if direct {
            match nix::fcntl::fcntl(file.as_raw_fd(), FcntlArg::F_SETFL(OFlag::O_DIRECT)) {
                Ok(_) => {}
                Err(error) => debug!("Error {error:?} returned when setting O_DIRECT flag to read file. The performance of the system may be affected"),
            };
        }

        let linux_file = Rc::new(LinuxFile {
            innerLinuxIo: self.inner.clone(),
            file,
        });

        if std::env::var(io::ENV_DISABLE_FILE_LOCK).is_err() {
            linux_file.lock_file(true)?;
        }

        Ok(linux_file)
    }

    fn runOnce(&self) -> Result<()> {
        let mut inner = self.inner.borrow_mut();
        let ioUringWrapper = &mut inner.ioUringWrapper;

        if ioUringWrapper.idle() {
            return Ok(());
        }

        ioUringWrapper.wait_for_completion()?;

        // cqe : completion queue entry
        while let Some(cqe) = ioUringWrapper.get_completion() {
            // 对read 和 sync 来说 它是 -1,0
            // 对write来说它是written byte数量
            let result = cqe.result();

            if result < 0 {
                return Err(LimboError::LinuxIOError(format!("{} cqe: {:?}", LinuxIOError::IOUringCQError(result), cqe)));
            }

            if let Some(c) = ioUringWrapper.pending.remove(&cqe.user_data()) {
                c.complete(result);
            }
        }

        Ok(())
    }

    fn generate_random_number(&self) -> i64 {
        let mut buf = [0u8; 8];
        getrandom::getrandom(&mut buf).unwrap();
        i64::from_ne_bytes(buf)
    }

    fn get_current_time(&self) -> String {
        chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string()
    }
}

impl LinuxIO {
    pub fn new() -> Result<Self> {
        let ring = io_uring::IoUring::new(MAX_IOVECS as u32)?;
        let inner = InnerLinuxIO {
            ioUringWrapper: IoUringWrapper {
                ioUring: ring,
                pending_ops: 0,
                pending: HashMap::new(),
                key: 0,
            },
            iovecs: [iovec {
                iov_base: std::ptr::null_mut(),
                iov_len: 0,
            }; MAX_IOVECS],
            next_iovec: 0,
        };

        Ok(Self {
            inner: Rc::new(RefCell::new(inner)),
        })
    }
}

struct InnerLinuxIO {
    ioUringWrapper: IoUringWrapper,
    iovecs: [iovec; MAX_IOVECS],
    next_iovec: usize,
}

impl InnerLinuxIO {
    pub fn get_iovec(&mut self, buf: *const u8, len: usize) -> &iovec {
        let iovec = &mut self.iovecs[self.next_iovec];
        iovec.iov_base = buf as *mut std::ffi::c_void;
        iovec.iov_len = len;
        self.next_iovec = (self.next_iovec + 1) % MAX_IOVECS;
        iovec
    }
}

///sqe: submit queue entry
// cqe: completion queue entry
struct IoUringWrapper {
    ioUring: io_uring::IoUring,
    pending_ops: usize,
    pub pending: HashMap<u64, Rc<CompletionEnum>>,
    key: u64,
}

impl IoUringWrapper {
    fn pushToSubmitQueue(&mut self, entry: &io_uring::squeue::Entry, c: Rc<CompletionEnum>) {
        trace!("submit_entry({:?})", entry);

        // userData是1个标识是key用途
        self.pending.insert(entry.get_user_data(), c);

        // entry 提交到 submission queue
        unsafe { self.ioUring.submission().push(entry).expect("submission queue is full"); }
        self.pending_ops += 1;
    }

    fn wait_for_completion(&mut self) -> Result<()> {
        // submission queue 的内容提交到内核 然后wait需要的数量
        self.ioUring.submit_and_wait(1)?;

        Ok(())
    }

    fn get_completion(&mut self) -> Option<io_uring::cqueue::Entry> {
        // NOTE: This works because CompletionQueue's next function pops the head of the queue. This is not normal behaviour of iterators
        self.ioUring.completion().next().map(|e| {
            self.pending_ops -= 1;
            e
        })
    }

    fn idle(&self) -> bool {
        self.pending_ops == 0
    }

    fn get_key(&mut self) -> u64 {
        self.key += 1;
        self.key
    }
}

pub struct LinuxFile {
    innerLinuxIo: Rc<RefCell<InnerLinuxIO>>,
    file: std::fs::File,
}

impl File for LinuxFile {
    fn lock_file(&self, exclusive: bool) -> Result<()> {
        let fd = self.file.as_raw_fd();
        let flock = flock {
            l_type: if exclusive {
                libc::F_WRLCK as c_short
            } else {
                libc::F_RDLCK as c_short
            },
            l_whence: libc::SEEK_SET as c_short,
            l_start: 0,
            l_len: 0, // Lock entire file
            l_pid: 0,
        };

        // F_SETLK is a non-blocking lock. The lock will be released when the file is closed
        // or the process exits or after an explicit unlock.

        if unsafe { libc::fcntl(fd, F_SETLK, &flock) } == -1 {
            let err = std::io::Error::last_os_error();
            return if err.kind() == std::io::ErrorKind::WouldBlock {
                Err(LimboError::LockingError("File is locked by another process".into()))
            } else {
                Err(LimboError::IOError(err))
            };
        }

        Ok(())
    }

    fn unlock_file(&self) -> Result<()> {
        let fd = self.file.as_raw_fd();
        let flock = flock {
            l_type: libc::F_UNLCK as c_short,
            l_whence: libc::SEEK_SET as c_short,
            l_start: 0,
            l_len: 0,
            l_pid: 0,
        };

        if unsafe { libc::fcntl(fd, F_SETLK, &flock) } == -1 {
            return Err(LimboError::LockingError(format!("Failed to release file lock: {}", std::io::Error::last_os_error())));
        }

        Ok(())
    }

    fn pread(&self, pos: usize, c: Rc<CompletionEnum>) -> Result<()> {
        let readCompletion = match &(*c) {
            CompletionEnum::Read(r) => r,
            _ => unreachable!(),
        };

        let fd = io_uring::types::Fd(self.file.as_raw_fd());
        let mut io = self.innerLinuxIo.borrow_mut();

        let entry = {
            let mut buf = readCompletion.buf_mut();
            let iovec = io.get_iovec(buf.as_mut_ptr(), buf.len());
            io_uring::opcode::Readv::new(fd, iovec, 1).offset(pos as u64).build().user_data(io.ioUringWrapper.get_key())
        };

        io.ioUringWrapper.pushToSubmitQueue(&entry, c);

        Ok(())
    }

    fn pwrite(&self,
              pos: usize,
              buffer: Rc<RefCell<crate::Buffer>>,
              c: Rc<CompletionEnum>) -> Result<()> {
        let mut innerLinuxIo = self.innerLinuxIo.borrow_mut();

        let fd = io_uring::types::Fd(self.file.as_raw_fd());

        let writeEntry = {
            let buf = buffer.borrow();
            let iovec = innerLinuxIo.get_iovec(buf.as_ptr(), buf.len());
            // userData是1个标识
            io_uring::opcode::Writev::new(fd, iovec, 1).offset(pos as u64).build().user_data(innerLinuxIo.ioUringWrapper.get_key())
        };

        innerLinuxIo.ioUringWrapper.pushToSubmitQueue(&writeEntry, c);

        Ok(())
    }

    fn sync(&self, c: Rc<CompletionEnum>) -> Result<()> {
        let fd = io_uring::types::Fd(self.file.as_raw_fd());
        let mut io = self.innerLinuxIo.borrow_mut();
        trace!("sync()");
        let sync = io_uring::opcode::Fsync::new(fd)
            .build()
            .user_data(io.ioUringWrapper.get_key());
        io.ioUringWrapper.pushToSubmitQueue(&sync, c);
        Ok(())
    }

    fn size(&self) -> Result<u64> {
        Ok(self.file.metadata().unwrap().len())
    }
}

impl Drop for LinuxFile {
    fn drop(&mut self) {
        self.unlock_file().expect("Failed to unlock file");
    }
}