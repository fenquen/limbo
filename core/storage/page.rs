use crate::storage::buffer_pool::BufferPool;
use crate::storage::Storage;
use crate::storage::sqlite3_ondisk::{self, DbHeader, PageContent};
use crate::storage::wal::Wal;
use crate::{Buffer, Result};
use log::{debug, trace};
use std::cell::{RefCell, UnsafeCell};
use std::collections::HashSet;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, RwLock};

use super::page_cache::{DumbLruPageCache, PageCacheKey};
use super::wal::CheckpointStatus;

pub struct Page {
    pub pageInner: UnsafeCell<PageInner>,
}

pub struct PageInner {
    pub flags: AtomicUsize,
    pub pageContent: Option<PageContent>,
    pub pageId: usize,
}

// Concurrency control of pages will be handled by the pager, we won't wrap Page with RwLock because that is bad bad.
pub type PageArc = Arc<Page>;

/// Page is up-to-date.
const PAGE_UPTODATE: usize = 0b001;
/// Page is locked for I/O to prevent concurrent access.
const PAGE_LOCKED: usize = 0b010;
/// Page had an I/O error.
const PAGE_ERROR: usize = 0b100;
/// Page is dirty. Flush needed.
const PAGE_DIRTY: usize = 0b1000;
/// Page's contents are loaded in memory.
const PAGE_LOADED: usize = 0b10000;

impl Page {
    pub fn new(pageId: usize) -> Page {
        Page {
            pageInner: UnsafeCell::new(
                PageInner {
                    flags: AtomicUsize::new(0),
                    pageContent: None,
                    pageId,
                }),
        }
    }

    pub fn getMutInner(&self) -> &mut PageInner {
        unsafe { &mut *self.pageInner.get() }
    }

    pub fn is_uptodate(&self) -> bool {
        self.getMutInner().flags.load(Ordering::SeqCst) & PAGE_UPTODATE != 0
    }

    pub fn set_uptodate(&self) {
        self.getMutInner().flags.fetch_or(PAGE_UPTODATE, Ordering::SeqCst);
    }

    pub fn clear_uptodate(&self) {
        self.getMutInner().flags.fetch_and(!PAGE_UPTODATE, Ordering::SeqCst);
    }

    pub fn is_locked(&self) -> bool {
        self.getMutInner().flags.load(Ordering::SeqCst) & PAGE_LOCKED != 0
    }

    pub fn setLocked(&self) {
        self.getMutInner().flags.fetch_or(PAGE_LOCKED, Ordering::SeqCst);
    }

    pub fn clear_locked(&self) {
        self.getMutInner().flags.fetch_and(!PAGE_LOCKED, Ordering::SeqCst);
    }

    pub fn is_error(&self) -> bool {
        self.getMutInner().flags.load(Ordering::SeqCst) & PAGE_ERROR != 0
    }

    pub fn set_error(&self) {
        self.getMutInner().flags.fetch_or(PAGE_ERROR, Ordering::SeqCst);
    }

    pub fn clear_error(&self) {
        self.getMutInner().flags.fetch_and(!PAGE_ERROR, Ordering::SeqCst);
    }

    pub fn is_dirty(&self) -> bool {
        self.getMutInner().flags.load(Ordering::SeqCst) & PAGE_DIRTY != 0
    }

    pub fn set_dirty(&self) {
        self.getMutInner().flags.fetch_or(PAGE_DIRTY, Ordering::SeqCst);
    }

    pub fn clear_dirty(&self) {
        self.getMutInner().flags.fetch_and(!PAGE_DIRTY, Ordering::SeqCst);
    }

    pub fn is_loaded(&self) -> bool {
        self.getMutInner().flags.load(Ordering::SeqCst) & PAGE_LOADED != 0
    }

    pub fn set_loaded(&self) {
        self.getMutInner().flags.fetch_or(PAGE_LOADED, Ordering::SeqCst);
    }

    pub fn clear_loaded(&self) {
        log::debug!("clear loaded {}", self.getMutInner().pageId);
        self.getMutInner().flags.fetch_and(!PAGE_LOADED, Ordering::SeqCst);
    }
}

#[derive(Clone)]
enum FlushState {
    Start,
    WaitAppendFrames,
    SyncWal,
    Checkpoint,
    SyncDbFile,
    WaitSyncDbFile,
}

#[derive(Clone, Debug)]
enum CheckpointState {
    Checkpoint,
    SyncDbFile,
    WaitSyncDbFile,
    CheckpointDone,
}

/// This will keep track of the state of current cache flush in order to not repeat work
struct FlushInfo {
    state: FlushState,
    /// Number of writes taking place. When in_flight gets to 0 we can schedule a fsync.
    in_flight_writes: Rc<RefCell<usize>>,
}

/// The pager interface implements the persistence layer by providing access
/// to pages of the database file, including caching, concurrency control, and
/// transaction management.
pub struct Pager {
    pub storage: Rc<dyn Storage>,
    wal: Rc<RefCell<dyn Wal>>,
    pageCache: Arc<RwLock<DumbLruPageCache>>,
    bufferPool: Rc<BufferPool>,
    pub io: Arc<dyn crate::io::IO>,
    dirtyPageIds: Rc<RefCell<HashSet<usize>>>,
    db_header: Rc<RefCell<DbHeader>>,
    flush_info: RefCell<FlushInfo>,
    checkpoint_state: RefCell<CheckpointState>,
    checkpoint_inflight: Rc<RefCell<usize>>,
    syncing: Rc<RefCell<bool>>,
}

impl Pager {
    /// begins opening a database by reading the database header.
    pub fn beginOpen(dbStorage: Rc<dyn Storage>) -> Result<Rc<RefCell<DbHeader>>> {
        sqlite3_ondisk::begin_read_database_header(dbStorage)
    }

    /// Completes opening a database by initializing the Pager with the database header.
    pub fn finishOpen(dbHeader: Rc<RefCell<DbHeader>>,
                      storage: Rc<dyn Storage>,
                      wal: Rc<RefCell<dyn Wal>>,
                      io: Arc<dyn crate::io::IO>,
                      pageCache: Arc<RwLock<DumbLruPageCache>>,
                      buffer_pool: Rc<BufferPool>) -> Result<Pager> {
        Ok(Pager {
            storage,
            wal,
            pageCache,
            io,
            dirtyPageIds: Rc::new(RefCell::new(HashSet::new())),
            db_header: dbHeader.clone(),
            flush_info: RefCell::new(FlushInfo {
                state: FlushState::Start,
                in_flight_writes: Rc::new(RefCell::new(0)),
            }),
            syncing: Rc::new(RefCell::new(false)),
            checkpoint_state: RefCell::new(CheckpointState::Checkpoint),
            checkpoint_inflight: Rc::new(RefCell::new(0)),
            bufferPool: buffer_pool,
        })
    }

    pub fn begin_read_tx(&self) -> Result<()> {
        self.wal.borrow_mut().beginReadTx()?;
        Ok(())
    }

    pub fn begin_write_tx(&self) -> Result<()> {
        self.wal.borrow_mut().beginWriteTx()?;
        Ok(())
    }

    pub fn end_tx(&self) -> Result<CheckpointStatus> {
        match self.flushCache()? {
            CheckpointStatus::Done => {}
            CheckpointStatus::IO => return Ok(CheckpointStatus::IO),
        };
        self.wal.borrow().endReadTx()?;
        Ok(CheckpointStatus::Done)
    }

    pub fn readPage(&self, pageId: usize) -> crate::Result<PageArc> {
        let mut pageCache = self.pageCache.write().unwrap();

        let pageCacheKey = PageCacheKey::new(pageId, Some(self.wal.borrow().getMaxFrameId()));


        let page = Arc::new(Page::new(pageId));

        page.setLocked();

        // 到wal读取
        if let Some(frameId) = self.wal.borrow().getLatestFrameIdContainsPageId(pageId as u64)? {
            self.wal.borrow().readFrame(frameId, page.clone(), self.bufferPool.clone())?;

            page.set_uptodate();

            // TODO(pere) ensure page is inserted, we should probably first insert to page cache and if successful, read frame or page
            pageCache.insert(pageCacheKey, page.clone());

            return Ok(page);
        }

        if let Some(page) = pageCache.get(&pageCacheKey) {
            page.clear_locked();
            return Ok(page.clone());
        }

        sqlite3_ondisk::beginReadPage(self.storage.clone(),
                                      self.bufferPool.clone(),
                                      page.clone(),
                                      pageId)?;

        // TODO(pere) ensure page is inserted
        pageCache.insert(pageCacheKey, page.clone());

        Ok(page)
    }

    /// Loads pages if not loaded
    pub fn load_page(&self, page: PageArc) -> Result<()> {
        let id = page.getMutInner().pageId;
        trace!("load_page(page_idx = {})", id);
        let mut page_cache = self.pageCache.write().unwrap();
        page.setLocked();
        let page_key = PageCacheKey::new(id, Some(self.wal.borrow().getMaxFrameId()));
        if let Some(frame_id) = self.wal.borrow().getLatestFrameIdContainsPageId(id as u64)? {
            self.wal
                .borrow()
                .readFrame(frame_id, page.clone(), self.bufferPool.clone())?;
            {
                page.set_uptodate();
            }
            // TODO(pere) ensure page is inserted
            if !page_cache.contains_key(&page_key) {
                page_cache.insert(page_key, page.clone());
            }
            return Ok(());
        }
        sqlite3_ondisk::beginReadPage(
            self.storage.clone(),
            self.bufferPool.clone(),
            page.clone(),
            id,
        )?;
        // TODO(pere) ensure page is inserted
        if !page_cache.contains_key(&page_key) {
            page_cache.insert(page_key, page.clone());
        }
        Ok(())
    }

    /// Writes the database header.
    pub fn write_database_header(&self, header: &DbHeader) {
        sqlite3_ondisk::begin_write_database_header(header, self).expect("failed to write header");
    }

    /// Changes the size of the page cache.
    pub fn change_page_cache_size(&self, capacity: usize) {
        let mut page_cache = self.pageCache.write().unwrap();
        page_cache.resize(capacity);
    }

    pub fn addDirtyPageId(&self, page_id: usize) {
        // TODO: check duplicates?
        RefCell::borrow_mut(&self.dirtyPageIds).insert(page_id);
    }

    pub fn flushCache(&self) -> Result<CheckpointStatus> {
        loop {
            let state = self.flush_info.borrow().state.clone();
            match state {
                FlushState::Start => {
                    let db_size = self.db_header.borrow().dbSize;
                    for page_id in self.dirtyPageIds.borrow().iter() {
                        let mut cache = self.pageCache.write().unwrap();
                        let page_key = PageCacheKey::new(*page_id, Some(self.wal.borrow().getMaxFrameId()));
                        let page = cache.get(&page_key).expect("we somehow added a page to dirty list but we didn't mark it as dirty, causing cache to drop it.");

                        self.wal.borrow_mut().appendFrame(page.clone(),
                                                          db_size,
                                                          self.flush_info.borrow().in_flight_writes.clone())?;
                    }
                    self.dirtyPageIds.borrow_mut().clear();
                    self.flush_info.borrow_mut().state = FlushState::WaitAppendFrames;
                    return Ok(CheckpointStatus::IO);
                }
                FlushState::WaitAppendFrames => {
                    if *self.flush_info.borrow().in_flight_writes.borrow() == 0 {
                        self.flush_info.borrow_mut().state = FlushState::SyncWal;
                    } else {
                        return Ok(CheckpointStatus::IO);
                    }
                }
                FlushState::SyncWal => {
                    match self.wal.borrow_mut().sync() {
                        Ok(CheckpointStatus::IO) => return Ok(CheckpointStatus::IO),
                        Ok(CheckpointStatus::Done) => {}
                        Err(e) => return Err(e),
                    }

                    let should_checkpoint = self.wal.borrow().shouldCheckPoint();
                    if should_checkpoint {
                        self.flush_info.borrow_mut().state = FlushState::Checkpoint;
                    } else {
                        self.flush_info.borrow_mut().state = FlushState::Start;
                        break;
                    }
                }
                FlushState::Checkpoint => {
                    match self.checkpoint()? {
                        CheckpointStatus::Done => {
                            self.flush_info.borrow_mut().state = FlushState::SyncDbFile;
                        }
                        CheckpointStatus::IO => return Ok(CheckpointStatus::IO),
                    };
                }
                FlushState::SyncDbFile => {
                    sqlite3_ondisk::begin_sync(self.storage.clone(), self.syncing.clone())?;
                    self.flush_info.borrow_mut().state = FlushState::WaitSyncDbFile;
                }
                FlushState::WaitSyncDbFile => {
                    if *self.syncing.borrow() {
                        return Ok(CheckpointStatus::IO);
                    }

                    self.flush_info.borrow_mut().state = FlushState::Start;
                    break;
                }
            }
        }

        Ok(CheckpointStatus::Done)
    }

    pub fn checkpoint(&self) -> Result<CheckpointStatus> {
        loop {
            let state = self.checkpoint_state.borrow().clone();
            trace!("pager_checkpoint(state={:?})", state);
            match state {
                CheckpointState::Checkpoint => {
                    let in_flight = self.checkpoint_inflight.clone();
                    match self.wal.borrow_mut().checkpoint(self, in_flight)? {
                        CheckpointStatus::IO => return Ok(CheckpointStatus::IO),
                        CheckpointStatus::Done => {
                            self.checkpoint_state.replace(CheckpointState::SyncDbFile);
                        }
                    };
                }
                CheckpointState::SyncDbFile => {
                    sqlite3_ondisk::begin_sync(self.storage.clone(), self.syncing.clone())?;
                    self.checkpoint_state
                        .replace(CheckpointState::WaitSyncDbFile);
                }
                CheckpointState::WaitSyncDbFile => {
                    if *self.syncing.borrow() {
                        return Ok(CheckpointStatus::IO);
                    } else {
                        self.checkpoint_state
                            .replace(CheckpointState::CheckpointDone);
                    }
                }
                CheckpointState::CheckpointDone => {
                    let in_flight = self.checkpoint_inflight.clone();
                    if *in_flight.borrow() > 0 {
                        return Ok(CheckpointStatus::IO);
                    } else {
                        self.checkpoint_state.replace(CheckpointState::Checkpoint);
                        return Ok(CheckpointStatus::Done);
                    }
                }
            }
        }
    }

    // WARN: used for testing purposes
    pub fn clear_page_cache(&self) {
        loop {
            match self
                .wal
                .borrow_mut()
                .checkpoint(self, Rc::new(RefCell::new(0)))
            {
                Ok(CheckpointStatus::IO) => {
                    self.io.runOnce();
                }
                Ok(CheckpointStatus::Done) => {
                    break;
                }
                Err(err) => panic!("error while clearing cache {}", err),
            }
        }
        // TODO: only clear cache of things that are really invalidated
        self.pageCache.write().unwrap().clear();
    }

    /*
        Get's a new page that increasing the size of the page or uses a free page.
        Currently free list pages are not yet supported.
    */
    #[allow(clippy::readonly_write_lock)]
    pub fn allocate_page(&self) -> Result<PageArc> {
        let header = &self.db_header;
        let mut header = RefCell::borrow_mut(header);
        header.dbSize += 1;
        {
            // update database size
            // read sync for now
            loop {
                let first_page_ref = self.readPage(1)?;
                if first_page_ref.is_locked() {
                    self.io.runOnce()?;
                    continue;
                }
                first_page_ref.set_dirty();
                self.addDirtyPageId(1);

                let contents = first_page_ref.getMutInner().pageContent.as_ref().unwrap();
                contents.writeDbHeader(&header);
                break;
            }
        }

        let page = allocatePage(header.dbSize as usize, &self.bufferPool, 0);
        {
            // setup page and add to cache
            page.set_dirty();
            self.addDirtyPageId(page.getMutInner().pageId);
            let mut cache = self.pageCache.write().unwrap();
            let page_key =
                PageCacheKey::new(page.getMutInner().pageId, Some(self.wal.borrow().getMaxFrameId()));
            cache.insert(page_key, page.clone());
        }
        Ok(page)
    }

    pub fn put_loaded_page(&self, id: usize, page: PageArc) {
        let mut cache = self.pageCache.write().unwrap();
        // cache insert invalidates previous page
        let page_key = PageCacheKey::new(id, Some(self.wal.borrow().getMaxFrameId()));
        cache.insert(page_key, page.clone());
        page.set_loaded();
    }

    pub fn usable_size(&self) -> usize {
        let db_header = self.db_header.borrow();
        (db_header.pageSize - db_header.pageUnusedSpace as u16) as usize
    }
}

// db文件的头个的page的id是1,它的前面有100 byte的database header
pub fn allocatePage(pageId: usize, bufferPool: &Rc<BufferPool>, offset: usize) -> PageArc {
    let page = Arc::new(Page::new(pageId));

    let bufferData = bufferPool.get();

    let bp = bufferPool.clone();
    let drop_fn = Rc::new(move |buf| { bp.put(buf); });
    let buffer = Rc::new(RefCell::new(Buffer::new(bufferData, drop_fn)));

    page.set_loaded();

    page.getMutInner().pageContent =
        Some(
            PageContent {
                offset,
                buffer,
                overflowCells: Vec::new(),
            }
        );

    page
}