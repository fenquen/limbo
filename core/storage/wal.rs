use std::collections::{HashMap, HashSet};
use std::sync::RwLock;
use std::{cell::RefCell, rc::Rc, sync::Arc};

use log::{debug, trace};

use crate::io::{File, SyncCompletion, IO};
use crate::storage::sqlite3_ondisk::{
    begin_read_wal_frame, begin_write_wal_frame,
};
use crate::{Buffer, Result};
use crate::{CompletionEnum, Page};

use self::sqlite3_ondisk::{checksum_wal, PageContent};

use super::buffer_pool::BufferPool;
use super::page_cache::PageCacheKey;
use super::page::{PageArc, Pager};
use super::sqlite3_ondisk::{self, begin_write_btree_page, WalHeader};


pub const WAL_HEADER_SIZE: usize = 32;
pub const WAL_FRAME_HEADER_SIZE: usize = 24;
/// magic is a single number represented as WAL_MAGIC_LE but the big endian counterpart is just the same number with LSB set to 1.
pub const WAL_MAGIC_LE: u32 = 0x377f0682;
pub const WAL_MAGIC_BE: u32 = 0x377f0683;

/// Write-ahead log (WAL).
pub trait Wal {
    fn beginReadTx(&mut self) -> Result<()>;
    fn endReadTx(&self) -> Result<()>;

    fn beginWriteTx(&mut self) -> Result<()>;
    fn endWriteTx(&self) -> Result<()>;

    /// Find the latest frame containing a page.
    fn getLatestFrameIdContainsPageId(&self, pageId: u64) -> Result<Option<u64>>;

    /// Read a frame from the WAL.
    fn readFrame(&self,
                 frameId: u64,
                 page: PageArc,
                 bufferPool: Rc<BufferPool>) -> Result<()>;

    /// Write a frame to the WAL.
    fn appendFrame(&mut self,
                   page: PageArc,
                   db_size: u32,
                   write_counter: Rc<RefCell<usize>>) -> Result<()>;

    fn shouldCheckPoint(&self) -> bool;

    fn checkpoint(&mut self,
                  pager: &Pager,
                  writeCounter: Rc<RefCell<usize>>) -> Result<CheckpointStatus>;

    fn sync(&mut self) -> Result<CheckpointStatus>;

    fn getMaxFrameId(&self) -> u64;
    fn getMinFrameId(&self) -> u64;
}

// Syncing requires a state machine because we need to schedule a sync and then wait until it is
// finished. If we don't wait there will be undefined behaviour that no one wants to debug.
#[derive(Copy, Clone)]
enum SyncState {
    NotSyncing,
    Syncing,
}

#[derive(Debug, Copy, Clone)]
pub enum CheckpointState {
    Start,
    ReadFrame,
    WaitReadFrame,
    WritePage,
    WaitWritePage,
    Done,
}

pub enum CheckpointStatus {
    Done,
    IO,
}

// Checkpointing is a state machine that has multiple steps. Since there are multiple steps we save
// in flight information of the checkpoint in OngoingCheckpoint. page is just a helper Page to do
// page operations like reading a frame to a page, and writing a page to disk. This page should not
// be placed back in pager page cache or anything, it's just a helper.
// min_frame and max_frame is the range of frames that can be safely transferred from WAL to db
// file.
// current_page is a helper to iterate through all the pages that might have a frame in the safe
// range. This is inneficient for now.
struct OngoingCheckpoint {
    page: PageArc,
    state: CheckpointState,
    min_frame: u64,
    max_frame: u64,
    current_page: u64,
}

pub struct WalFile {
    io: Arc<dyn IO>,
    buffer_pool: Rc<BufferPool>,

    sync_state: RefCell<SyncState>,
    syncing: Rc<RefCell<bool>>,
    page_size: usize,

    walFileShared: Arc<RwLock<WalFileShared>>,
    ongoing_checkpoint: OngoingCheckpoint,
    checkpoint_threshold: usize,
    // min and max frames for this connection
    max_frame: u64,
    min_frame: u64,
}

/// part of a WAL that will be shared between threads. A wal has information
/// that needs to be communicated between threads so this struct does
pub struct WalFileShared {
    walHeader: Arc<RwLock<WalHeader>>,
    minFrame: u64,
    maxFrame: u64,
    nbackfills: u64,
    // Frame cache maps a Page to all the frames it has stored in WAL in ascending order.
    // This is do to easily find the frame it must checkpoint each connection if a checkpoint is
    // necessary.
    // One difference between SQLite and limbo is that we will never support multi process, meaning
    // we don't need WAL's index file. So we can do stuff like this without shared memory.
    // TODO: this will need refactoring because this is incredible memory inneficient.
    frameCache: HashMap<u64, Vec<u64>>,
    // Another memory inneficient array made to just keep track of pages that are in frame_cache.
    pageIdsInFrame: Vec<u64>,
    lastChecksum: (u32, u32), // Check of last frame in WAL, this is a cumulative checksum over all frames in the WAL
    file: Rc<dyn File>,
}

impl Wal for WalFile {
    /// Begin a read transaction.
    fn beginReadTx(&mut self) -> Result<()> {
        let shared = self.walFileShared.read().unwrap();
        self.min_frame = shared.nbackfills + 1;
        self.max_frame = shared.maxFrame;
        Ok(())
    }

    /// End a read transaction.
    fn endReadTx(&self) -> Result<()> {
        Ok(())
    }

    /// Begin a write transaction
    fn beginWriteTx(&mut self) -> Result<()> {
        Ok(())
    }

    /// End a write transaction
    fn endWriteTx(&self) -> Result<()> {
        Ok(())
    }

    fn getLatestFrameIdContainsPageId(&self, pageId: u64) -> Result<Option<u64>> {
        let walFileShared = self.walFileShared.read().unwrap();
        let frames = walFileShared.frameCache.get(&pageId);
        if frames.is_none() {
            return Ok(None);
        }
        let frames = frames.unwrap();
        for frame in frames.iter().rev() {
            if *frame <= self.max_frame {
                return Ok(Some(*frame));
            }
        }
        Ok(None)
    }

    /// Read a frame from the WAL.
    fn readFrame(&self, frame_id: u64, page: PageArc, buffer_pool: Rc<BufferPool>) -> Result<()> {
        debug!("read_frame({})", frame_id);
        let offset = self.frame_offset(frame_id);
        let shared = self.walFileShared.read().unwrap();
        page.setLocked();
        begin_read_wal_frame(
            &shared.file,
            offset + WAL_FRAME_HEADER_SIZE,
            buffer_pool,
            page,
        )?;
        Ok(())
    }

    /// Write a frame to the WAL.
    fn appendFrame(&mut self,
                   page: PageArc,
                   db_size: u32,
                   write_counter: Rc<RefCell<usize>>) -> Result<()> {
        let page_id = page.getMutInner().pageId;
        let mut shared = self.walFileShared.write().unwrap();
        let frame_id = shared.maxFrame;
        let offset = self.frame_offset(frame_id);

        let header = shared.walHeader.clone();
        let header = header.read().unwrap();
        let checksums = shared.lastChecksum;
        let checksums = begin_write_wal_frame(
            &shared.file,
            offset,
            &page,
            db_size,
            write_counter,
            &header,
            checksums,
        )?;
        shared.lastChecksum = checksums;
        shared.maxFrame = frame_id + 1;
        {
            let frames = shared.frameCache.get_mut(&(page_id as u64));
            match frames {
                Some(frames) => frames.push(frame_id),
                None => {
                    shared.frameCache.insert(page_id as u64, vec![frame_id]);
                    shared.pageIdsInFrame.push(page_id as u64);
                }
            }
        }
        Ok(())
    }

    fn shouldCheckPoint(&self) -> bool {
        let shared = self.walFileShared.read().unwrap();
        let frame_id = shared.maxFrame as usize;
        frame_id >= self.checkpoint_threshold
    }

    fn checkpoint(&mut self, pager: &Pager, write_counter: Rc<RefCell<usize>>) -> Result<CheckpointStatus> {
        'checkpoint_loop: loop {
            let state = self.ongoing_checkpoint.state;
            log::debug!("checkpoint(state={:?})", state);
            match state {
                CheckpointState::Start => {
                    // TODO(pere): check what frames are safe to checkpoint between many readers!
                    self.ongoing_checkpoint.min_frame = self.min_frame;
                    self.ongoing_checkpoint.max_frame = self.max_frame;
                    self.ongoing_checkpoint.current_page = 0;
                    self.ongoing_checkpoint.state = CheckpointState::ReadFrame;
                }
                CheckpointState::ReadFrame => {
                    let shared = self.walFileShared.read().unwrap();
                    assert!(
                        self.ongoing_checkpoint.current_page as usize
                            <= shared.pageIdsInFrame.len()
                    );
                    if self.ongoing_checkpoint.current_page as usize == shared.pageIdsInFrame.len()
                    {
                        self.ongoing_checkpoint.state = CheckpointState::Done;
                        continue 'checkpoint_loop;
                    }
                    let page =
                        shared.pageIdsInFrame[self.ongoing_checkpoint.current_page as usize];
                    let frames = shared
                        .frameCache
                        .get(&page)
                        .expect("page must be in frame cache if it's in list");

                    for frame in frames.iter().rev() {
                        // TODO: do proper selection of frames to checkpoint
                        if *frame >= self.ongoing_checkpoint.min_frame {
                            self.ongoing_checkpoint.page.getMutInner().pageId = page as usize;

                            self.readFrame(
                                *frame,
                                self.ongoing_checkpoint.page.clone(),
                                self.buffer_pool.clone(),
                            )?;
                            self.ongoing_checkpoint.state = CheckpointState::WaitReadFrame;
                            self.ongoing_checkpoint.current_page += 1;
                            continue 'checkpoint_loop;
                        }
                    }
                    self.ongoing_checkpoint.current_page += 1;
                }
                CheckpointState::WaitReadFrame => {
                    if self.ongoing_checkpoint.page.is_locked() {
                        return Ok(CheckpointStatus::IO);
                    } else {
                        self.ongoing_checkpoint.state = CheckpointState::WritePage;
                    }
                }
                CheckpointState::WritePage => {
                    self.ongoing_checkpoint.page.setDirty();
                    begin_write_btree_page(
                        pager,
                        &self.ongoing_checkpoint.page,
                        write_counter.clone(),
                    )?;
                    self.ongoing_checkpoint.state = CheckpointState::WaitWritePage;
                }
                CheckpointState::WaitWritePage => {
                    if *write_counter.borrow() > 0 {
                        return Ok(CheckpointStatus::IO);
                    }
                    let shared = self.walFileShared.read().unwrap();
                    if (self.ongoing_checkpoint.current_page as usize)
                        < shared.pageIdsInFrame.len()
                    {
                        self.ongoing_checkpoint.state = CheckpointState::ReadFrame;
                    } else {
                        self.ongoing_checkpoint.state = CheckpointState::Done;
                    }
                }
                CheckpointState::Done => {
                    if *write_counter.borrow() > 0 {
                        return Ok(CheckpointStatus::IO);
                    }
                    let mut shared = self.walFileShared.write().unwrap();
                    shared.frameCache.clear();
                    shared.pageIdsInFrame.clear();
                    shared.maxFrame = 0;
                    shared.nbackfills = 0;
                    self.ongoing_checkpoint.state = CheckpointState::Start;
                    return Ok(CheckpointStatus::Done);
                }
            }
        }
    }

    fn sync(&mut self) -> Result<CheckpointStatus> {
        let state = *self.sync_state.borrow();
        match state {
            SyncState::NotSyncing => {
                let shared = self.walFileShared.write().unwrap();
                log::debug!("wal_sync");
                {
                    let syncing = self.syncing.clone();
                    *syncing.borrow_mut() = true;
                    let completion = CompletionEnum::Sync(SyncCompletion {
                        complete: Box::new(move |_| {
                            log::debug!("wal_sync finish");
                            *syncing.borrow_mut() = false;
                        }),
                    });
                    shared.file.sync(Rc::new(completion))?;
                }
                self.sync_state.replace(SyncState::Syncing);
                Ok(CheckpointStatus::IO)
            }
            SyncState::Syncing => {
                if *self.syncing.borrow() {
                    Ok(CheckpointStatus::IO)
                } else {
                    self.sync_state.replace(SyncState::NotSyncing);
                    Ok(CheckpointStatus::Done)
                }
            }
        }
    }

    fn getMaxFrameId(&self) -> u64 {
        self.max_frame
    }

    fn getMinFrameId(&self) -> u64 {
        self.min_frame
    }
}

impl WalFile {
    pub fn new(io: Arc<dyn IO>,
               page_size: usize,
               shared: Arc<RwLock<WalFileShared>>,
               buffer_pool: Rc<BufferPool>) -> Self {
        let checkpoint_page = Arc::new(Page::new(0));
        let buffer = buffer_pool.get();
        {
            let buffer_pool = buffer_pool.clone();
            let drop_fn = Rc::new(move |buf| {
                buffer_pool.put(buf);
            });
            checkpoint_page.getMutInner().pageContent = Some(PageContent {
                offset: 0,
                buffer: Rc::new(RefCell::new(Buffer::new(buffer, drop_fn))),
                overflowCells: Vec::new(),
            });
        }
        Self {
            io,
            walFileShared: shared,
            ongoing_checkpoint: OngoingCheckpoint {
                page: checkpoint_page,
                state: CheckpointState::Start,
                min_frame: 0,
                max_frame: 0,
                current_page: 0,
            },
            syncing: Rc::new(RefCell::new(false)),
            checkpoint_threshold: 1,
            page_size,
            max_frame: 0,
            min_frame: 0,
            buffer_pool,
            sync_state: RefCell::new(SyncState::NotSyncing),
        }
    }

    fn frame_offset(&self, frame_id: u64) -> usize {
        let page_size = self.page_size;
        let page_offset = frame_id * (page_size as u64 + WAL_FRAME_HEADER_SIZE as u64);
        let offset = WAL_HEADER_SIZE as u64 + page_offset;
        offset as usize
    }
}

impl WalFileShared {
    pub fn open_shared(io: &Arc<dyn IO>,
                       path: &str,
                       page_size: u16) -> Result<Arc<RwLock<WalFileShared>>> {
        let file = io.openFile(path, crate::io::OpenFlags::Create, false)?;

        let header = if file.size()? > 0 {
            let wal_header = match sqlite3_ondisk::begin_read_wal_header(&file) {
                Ok(header) => header,
                Err(err) => panic!("Couldn't read header page: {:?}", err),
            };

            // TODO: Return a completion instead.
            io.runOnce()?;
            wal_header
        } else {
            let magic = if cfg!(target_endian = "big") { WAL_MAGIC_BE } else { WAL_MAGIC_LE };

            let mut wal_header = WalHeader {
                magic,
                file_format: 3007000,
                page_size: page_size as u32,
                checkpoint_seq: 0, // TODO implement sequence number
                salt_1: 0,         // TODO implement salt
                salt_2: 0,
                checksum_1: 0,
                checksum_2: 0,
            };
            let native = cfg!(target_endian = "big"); // if target_endian is
            // already big then we don't care but if isn't, header hasn't yet been
            // encoded to big endian, therefore we wan't to swap bytes to compute this
            // checksum.
            let checksums = (0, 0);
            let checksums = checksum_wal(
                &wal_header.as_bytes()[..WAL_HEADER_SIZE - 2 * 4], // first 24 bytes
                &wal_header,
                checksums,
                native, // this is false because we haven't encoded the wal header yet
            );
            wal_header.checksum_1 = checksums.0;
            wal_header.checksum_2 = checksums.1;
            sqlite3_ondisk::begin_write_wal_header(&file, &wal_header)?;
            Arc::new(RwLock::new(wal_header))
        };

        let checksum = {
            let checksum = header.read().unwrap();
            (checksum.checksum_1, checksum.checksum_2)
        };

        let shared = WalFileShared {
            walHeader: header,
            minFrame: 0,
            maxFrame: 0,
            nbackfills: 0,
            frameCache: HashMap::new(),
            lastChecksum: checksum,
            file,
            pageIdsInFrame: Vec::new(),
        };

        Ok(Arc::new(RwLock::new(shared)))
    }
}
