//! SQLite on-disk file format.
//!
//! SQLite stores data in a single database file, which is divided into fixed-size
//! pages:
//!
//! The 1st page is special because it contains a 100 byte header at the beginning
//!
//! ```text
//! +----------+----------+----------+-----------------------------+----------+
//! |          |          |          |                             |          |
//! |  Page 1  |  Page 2  |  Page 3  |           ...               |  Page N  |
//! |          |          |          |                             |          |
//! +----------+----------+----------+-----------------------------+----------+
//! ```
//!
//!
//! Each page consists of a page header and N cells, which contain the records.
//!
//! ```text
//! +-----------------+----------------+---------------------+----------------+
//! |                 |                |                     |                |
//! |   Page header   |  Cell pointer  |     Unallocated     |  Cell content  |
//! | (8 or 12 bytes) |     array      |        space        |      area      |
//! |                 |                |                     |                |
//! +-----------------+----------------+---------------------+----------------+
//! ```
//!
//! The write-ahead log (WAL) is a separate file that contains the physical
//! log of changes to a database file. The file starts with a WAL header and
//! is followed by a sequence of WAL frames, which are database pages with
//! additional metadata.
//!
//! ```text
//! +-----------------+-----------------+-----------------+-----------------+
//! |                 |                 |                 |                 |
//! |    WAL header   |    WAL frame 1  |    WAL frame 2  |    WAL frame N  |
//! |                 |                 |                 |                 |
//! +-----------------+-----------------+-----------------+-----------------+
//! ```
//!
//! For more information, see the SQLite file format specification:
//!
//! https://www.sqlite.org/fileformat.html

use crate::error::LimboError;
use crate::io::{Buffer, CompletionEnum, ReadCompletion, SyncCompletion, WriteCompletion};
use crate::storage::buffer_pool::BufferPool;
use crate::storage::{page, wal, Storage};
use crate::storage::page::Pager;
use crate::types::{OwnedRecord, OwnedValue};
use crate::{File, Result};
use log::trace;
use std::cell::{Ref, RefCell};
use std::pin::Pin;
use std::rc::Rc;
use std::sync::{Arc, RwLock};

use super::page::PageArc;

/// The size of the database header in bytes.
pub const DB_HEADER_SIZE: usize = 100;

// DEFAULT_CACHE_SIZE negative values mean that we store the amount of pages a XKiB of memory can hold.
// We can calculate "real" cache size by diving by page size.
const DEFAULT_CACHE_SIZE: i32 = -2000;

// Minimum number of pages that cache can hold.
pub const MIN_PAGE_CACHE_SIZE: usize = 10;

/// The first 100 bytes of the database file
/// https://www.sqlite.org/fileformat.html
#[derive(Debug, Clone)]
pub struct DbHeader {
    magic: [u8; 16],
    /// sqlite在dbHeader中便明确了各个page大小
    pub pageSize: u16,
    write_version: u8,
    read_version: u8,
    /// unused "reserved" space at the end of each page usually 0
    pub pageReservedSpace: u8,
    max_embed_frac: u8,
    min_embed_frac: u8,
    min_leaf_frac: u8,
    change_counter: u32,
    /// 含有的page数量
    pub pageCount: u32,
    freelist_trunk_page: u32,
    freelist_pages: u32,
    schema_cookie: u32,
    schema_format: u32,
    pub default_cache_size: i32,
    vacuum: u32,
    text_encoding: u32,
    user_version: u32,
    incremental_vacuum: u32,
    application_id: u32,
    reserved: [u8; 20],
    version_valid_for: u32,
    pub version_number: u32,
}

impl Default for DbHeader {
    fn default() -> Self {
        Self {
            magic: *b"SQLite format 3\0",
            pageSize: 4096,
            write_version: 2,
            read_version: 2,
            pageReservedSpace: 0,
            max_embed_frac: 64,
            min_embed_frac: 32,
            min_leaf_frac: 32,
            change_counter: 1,
            pageCount: 1,
            freelist_trunk_page: 0,
            freelist_pages: 0,
            schema_cookie: 0,
            schema_format: 4, // latest format, new sqlite3 databases use this format
            default_cache_size: 500, // pages
            vacuum: 0,
            text_encoding: 1, // utf-8
            user_version: 1,
            incremental_vacuum: 0,
            application_id: 0,
            reserved: [0; 20],
            version_valid_for: 3047000,
            version_number: 3047000,
        }
    }
}

impl DbHeader {
    #[inline]
    pub fn pageUsableSpace(&self) -> usize {
        (self.pageSize - self.pageReservedSpace as u16) as usize
    }
}

#[derive(Debug, Default, Clone)]
#[repr(C)]
/// This helps with encoding because rust does not respect the order in structs, so in this case we want to keep the order
pub struct WalHeader {
    pub magic: u32,
    pub file_format: u32,
    pub page_size: u32,
    pub checkpoint_seq: u32,
    pub salt_1: u32,
    pub salt_2: u32,
    pub checksum_1: u32,
    pub checksum_2: u32,
}

#[allow(dead_code)]
#[derive(Debug, Default)]
pub struct WalFrameHeader {
    page_number: u32,
    db_size: u32,
    salt_1: u32,
    salt_2: u32,
    checksum_1: u32,
    checksum_2: u32,
}

pub fn begin_read_database_header(dbStorage: Rc<dyn Storage>) -> Result<Rc<RefCell<DbHeader>>> {
    let dbHeader = Rc::new(RefCell::new(DbHeader::default()));

    let header = dbHeader.clone();

    let complete = Box::new(move |buf: Rc<RefCell<Buffer>>| {
        let header = header.clone();
        finish_read_database_header(buf, header).unwrap();
    });

    let buffer = Rc::new(RefCell::new(Buffer::allocate(512, Rc::new(|_buf| {}))));
    dbStorage.readPage(1, Rc::new(CompletionEnum::Read(ReadCompletion::new(buffer, complete))))?;

    Ok(dbHeader)
}

/// 读取到的文件中的dbHeader原始data还原到struct
fn finish_read_database_header(buf: Rc<RefCell<Buffer>>, header: Rc<RefCell<DbHeader>>) -> Result<()> {
    // 读到的文件的data落地到了data
    let buf = buf.borrow();
    let buf = buf.as_slice();

    let mut dbHeader = RefCell::borrow_mut(&header);

    dbHeader.magic.copy_from_slice(&buf[0..16]);
    dbHeader.pageSize = u16::from_be_bytes([buf[16], buf[17]]);
    dbHeader.write_version = buf[18];
    dbHeader.read_version = buf[19];
    dbHeader.pageReservedSpace = buf[20];
    dbHeader.max_embed_frac = buf[21];
    dbHeader.min_embed_frac = buf[22];
    dbHeader.min_leaf_frac = buf[23];
    dbHeader.change_counter = u32::from_be_bytes([buf[24], buf[25], buf[26], buf[27]]);
    dbHeader.pageCount = u32::from_be_bytes([buf[28], buf[29], buf[30], buf[31]]);
    dbHeader.freelist_trunk_page = u32::from_be_bytes([buf[32], buf[33], buf[34], buf[35]]);
    dbHeader.freelist_pages = u32::from_be_bytes([buf[36], buf[37], buf[38], buf[39]]);
    dbHeader.schema_cookie = u32::from_be_bytes([buf[40], buf[41], buf[42], buf[43]]);
    dbHeader.schema_format = u32::from_be_bytes([buf[44], buf[45], buf[46], buf[47]]);
    dbHeader.default_cache_size = i32::from_be_bytes([buf[48], buf[49], buf[50], buf[51]]);
    if dbHeader.default_cache_size == 0 {
        dbHeader.default_cache_size = DEFAULT_CACHE_SIZE;
    }
    dbHeader.vacuum = u32::from_be_bytes([buf[52], buf[53], buf[54], buf[55]]);
    dbHeader.text_encoding = u32::from_be_bytes([buf[56], buf[57], buf[58], buf[59]]);
    dbHeader.user_version = u32::from_be_bytes([buf[60], buf[61], buf[62], buf[63]]);
    dbHeader.incremental_vacuum = u32::from_be_bytes([buf[64], buf[65], buf[66], buf[67]]);
    dbHeader.application_id = u32::from_be_bytes([buf[68], buf[69], buf[70], buf[71]]);
    dbHeader.reserved.copy_from_slice(&buf[72..92]);
    dbHeader.version_valid_for = u32::from_be_bytes([buf[92], buf[93], buf[94], buf[95]]);
    dbHeader.version_number = u32::from_be_bytes([buf[96], buf[97], buf[98], buf[99]]);

    Ok(())
}

pub fn begin_write_database_header(header: &DbHeader, pager: &Pager) -> Result<()> {
    let header = Rc::new(header.clone());
    let page_source = pager.storage.clone();

    let drop_fn = Rc::new(|_buf| {});
    let buffer_to_copy = Rc::new(RefCell::new(Buffer::allocate(512, drop_fn)));
    let buffer_to_copy_in_cb = buffer_to_copy.clone();

    let header_cb = header.clone();
    let complete = Box::new(move |buffer: Rc<RefCell<Buffer>>| {
        let header = header_cb.clone();
        let buffer: Buffer = buffer.borrow().clone();
        let buffer = Rc::new(RefCell::new(buffer));
        {
            let mut buf_mut = std::cell::RefCell::borrow_mut(&buffer);
            let buf = buf_mut.as_mut_slice();
            writeDbHeader2Buf(buf, &header);
            let mut buffer_to_copy = std::cell::RefCell::borrow_mut(&buffer_to_copy_in_cb);
            let buffer_to_copy_slice = buffer_to_copy.as_mut_slice();

            buffer_to_copy_slice.copy_from_slice(buf);
        }
    });

    let drop_fn = Rc::new(|_buf| {});
    let buf = Rc::new(RefCell::new(Buffer::allocate(512, drop_fn)));
    let c = Rc::new(CompletionEnum::Read(ReadCompletion::new(buf.clone(), complete)));
    page_source.readPage(1, c.clone())?;
    // run get header block
    pager.io.runOnce()?;

    let buffer_in_cb = buffer_to_copy.clone();
    let write_complete = Box::new(move |bytes_written: i32| {
        let buf = buffer_in_cb.clone();
        let buf_len = std::cell::RefCell::borrow(&buf).len();
        if bytes_written < buf_len as i32 {
            log::error!("wrote({bytes_written}) less than expected({buf_len})");
        }
        // finish_read_database_header(buf, header).unwrap();
    });
    let c = Rc::new(CompletionEnum::Write(WriteCompletion::new(write_complete)));
    page_source.writePage(0, buffer_to_copy.clone(), c)?;

    Ok(())
}

fn writeDbHeader2Buf(buf: &mut [u8], header: &DbHeader) {
    buf[0..16].copy_from_slice(&header.magic);
    buf[16..18].copy_from_slice(&header.pageSize.to_be_bytes());
    buf[18] = header.write_version;
    buf[19] = header.read_version;
    buf[20] = header.pageReservedSpace;
    buf[21] = header.max_embed_frac;
    buf[22] = header.min_embed_frac;
    buf[23] = header.min_leaf_frac;
    buf[24..28].copy_from_slice(&header.change_counter.to_be_bytes());
    buf[28..32].copy_from_slice(&header.pageCount.to_be_bytes());
    buf[32..36].copy_from_slice(&header.freelist_trunk_page.to_be_bytes());
    buf[36..40].copy_from_slice(&header.freelist_pages.to_be_bytes());
    buf[40..44].copy_from_slice(&header.schema_cookie.to_be_bytes());
    buf[44..48].copy_from_slice(&header.schema_format.to_be_bytes());
    buf[48..52].copy_from_slice(&header.default_cache_size.to_be_bytes());

    buf[52..56].copy_from_slice(&header.vacuum.to_be_bytes());
    buf[56..60].copy_from_slice(&header.text_encoding.to_be_bytes());
    buf[60..64].copy_from_slice(&header.user_version.to_be_bytes());
    buf[64..68].copy_from_slice(&header.incremental_vacuum.to_be_bytes());

    buf[68..72].copy_from_slice(&header.application_id.to_be_bytes());
    buf[72..92].copy_from_slice(&header.reserved);
    buf[92..96].copy_from_slice(&header.version_valid_for.to_be_bytes());
    buf[96..100].copy_from_slice(&header.version_number.to_be_bytes());
}

#[repr(u8)]
#[derive(Debug, PartialEq, Clone)]
pub enum PageType {
    IndexInterior = 2,
    TableInterior = 5,
    IndexLeaf = 10,
    TableLeaf = 13,
}

impl TryFrom<u8> for PageType {
    type Error = LimboError;

    fn try_from(value: u8) -> Result<Self> {
        match value {
            2 => Ok(Self::IndexInterior),
            5 => Ok(Self::TableInterior),
            10 => Ok(Self::IndexLeaf),
            13 => Ok(Self::TableLeaf),
            _ => Err(LimboError::Corrupt(format!("Invalid page type: {}", value))),
        }
    }
}

#[derive(Debug, Clone)]
pub struct OverflowCell {
    pub index: usize,
    pub payload: Pin<Vec<u8>>,
}

#[derive(Debug)]
pub struct PageContent {
    /// 如果是打头的page那么它是DB_HEADER_SIZE,不然的话是0
    pub offset: usize,
    /// 大小和page相同,因为bufferPool生成的时候配置的参数是dbHeader的pageSize
    pub buffer: Rc<RefCell<Buffer>>,
    pub overflowCells: Vec<OverflowCell>,
}

impl PageContent {
    pub fn getPageType(&self) -> PageType {
        self.read_u8(0).try_into().unwrap()
    }

    pub fn maybe_page_type(&self) -> Option<PageType> {
        match self.read_u8(0).try_into() {
            Ok(v) => Some(v),
            Err(_) => None, // this could be an overflow page
        }
    }

    #[allow(clippy::mut_from_ref)]
    pub fn asMutSlice(&self) -> &mut [u8] {
        unsafe {
            let buffer = &self.buffer.as_ptr();
            (*buffer).as_mut().unwrap().as_mut_slice()
        }
    }

    fn read_u8(&self, pos: usize) -> u8 {
        let buf = self.asMutSlice();
        buf[self.offset + pos]
    }

    pub fn read_u16(&self, pos: usize) -> u16 {
        let buf = self.asMutSlice();
        u16::from_be_bytes([buf[self.offset + pos], buf[self.offset + pos + 1]])
    }

    fn read_u32(&self, pos: usize) -> u32 {
        let buf = self.asMutSlice();
        u32::from_be_bytes([
            buf[self.offset + pos],
            buf[self.offset + pos + 1],
            buf[self.offset + pos + 2],
            buf[self.offset + pos + 3],
        ])
    }

    pub fn writeDyn<const N: usize>(&self, pos: usize, slice: &[u8; N]) {
        let buf = self.asMutSlice();
        buf[self.offset + pos..self.offset + pos + N].copy_from_slice(slice);
    }

    pub fn write_u8(&self, pos: usize, value: u8) {
        let buf = self.asMutSlice();
        buf[self.offset + pos] = value;
    }

    pub fn write_u16(&self, pos: usize, value: u16) {
        log::debug!("write_u16(pos={}, value={})", pos, value);
        let buf = self.asMutSlice();
        buf[self.offset + pos..self.offset + pos + 2].copy_from_slice(&value.to_be_bytes());
    }

    pub fn write_u32(&self, pos: usize, value: u32) {
        log::debug!("write_u32(pos={}, value={})", pos, value);
        let buf = self.asMutSlice();
        buf[self.offset + pos..self.offset + pos + 4].copy_from_slice(&value.to_be_bytes());
    }

    pub fn firstFreeBlockPos(&self) -> u16 {
        self.read_u16(1)
    }

    pub fn cellCount(&self) -> usize {
        self.read_u16(3) as usize
    }

    pub fn cellContentAreaStartPos(&self) -> u16 {
        self.read_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT_START_POS)
    }

    pub fn fragFreeByteCount(&self) -> u8 {
        self.read_u8(7)
    }

    pub fn rightmostChildPageIndex(&self) -> Option<u32> {
        match self.getPageType() {
            PageType::IndexInterior => Some(self.read_u32(8)),
            PageType::TableInterior => Some(self.read_u32(8)),
            PageType::IndexLeaf => None,
            PageType::TableLeaf => None,
        }
    }

    pub fn getCell(&self,
                   cellIndex: usize,
                   pager: Rc<Pager>,
                   maxLocal: usize,
                   minLocal: usize,
                   pageUsableSpace: usize) -> Result<BTreeCell> {
        assert!(cellIndex < self.cellCount(), "cell_get: idx out of bounds");

        // https://www.sqlite.org/fileformat.html#b_tree_pages
        // 叶子的page的header是8 不然是12
        let cellStartPos = match self.getPageType() {
            PageType::IndexInterior => 12,
            PageType::TableInterior => 12,
            PageType::IndexLeaf => 8,
            PageType::TableLeaf => 8,
        };

        // 乘以2的原因是 pageHeader后边存的是各个cell的2个字节大小的pos的
        let cellDataPos = self.read_u16(cellStartPos + (cellIndex * 2)) as usize;

        readBtreeCell(self.asMutSlice(),
                      &self.getPageType(),
                      cellDataPos,
                      pager,
                      maxLocal,
                      minLocal,
                      pageUsableSpace)
    }

    pub fn getPointerCellsStartPos(&self) -> (usize, usize) {
        let headerSize = match self.getPageType() {
            PageType::IndexInterior => 12,
            PageType::TableInterior => 12,
            PageType::IndexLeaf => 8,
            PageType::TableLeaf => 8,
        };

        (self.offset + headerSize, self.cellCount() * page::POINTER_CELL_BYTE_LEN)
    }

    pub fn getCellPayloadStartPos(&self,
                                  cellIndex: usize,
                                  max_local: usize,
                                  min_local: usize,
                                  usable_size: usize) -> (usize, usize) {
        let buf = self.asMutSlice();
        let ncells = self.cellCount();
        let cell_start = match self.getPageType() {
            PageType::IndexInterior => 12,
            PageType::TableInterior => 12,
            PageType::IndexLeaf => 8,
            PageType::TableLeaf => 8,
        };
        assert!(cellIndex < ncells, "cell_get: idx out of bounds");
        let cell_pointer = cell_start + (cellIndex * page::POINTER_CELL_BYTE_LEN);
        let cell_pointer = self.read_u16(cell_pointer) as usize;
        let start = cell_pointer;
        let len = match self.getPageType() {
            PageType::IndexInterior => {
                let (len_payload, n_payload) = readVarInt(&buf[cell_pointer + 4..]).unwrap();
                let (overflows, to_read) =
                    payload_overflows(len_payload as usize, max_local, min_local, usable_size);
                if overflows {
                    4 + to_read + n_payload + 4
                } else {
                    4 + len_payload as usize + n_payload + 4
                }
            }
            PageType::TableInterior => {
                let (_, n_rowid) = readVarInt(&buf[cell_pointer + 4..]).unwrap();
                4 + n_rowid
            }
            PageType::IndexLeaf => {
                let (len_payload, n_payload) = readVarInt(&buf[cell_pointer..]).unwrap();
                let (overflows, to_read) =
                    payload_overflows(len_payload as usize, max_local, min_local, usable_size);
                if overflows {
                    to_read + n_payload + 4
                } else {
                    len_payload as usize + n_payload + 4
                }
            }
            PageType::TableLeaf => {
                let (len_payload, n_payload) = readVarInt(&buf[cell_pointer..]).unwrap();
                let (_, n_rowid) = readVarInt(&buf[cell_pointer + n_payload..]).unwrap();
                let (overflows, to_read) =
                    payload_overflows(len_payload as usize, max_local, min_local, usable_size);
                if overflows {
                    to_read + n_payload + n_rowid
                } else {
                    len_payload as usize + n_payload + n_rowid
                }
            }
        };
        (start, len)
    }

    pub fn isLeaf(&self) -> bool {
        match self.getPageType() {
            PageType::IndexInterior => false,
            PageType::TableInterior => false,
            PageType::IndexLeaf => true,
            PageType::TableLeaf => true,
        }
    }

    pub fn writeDbHeader(&self, header: &DbHeader) {
        writeDbHeader2Buf(self.asMutSlice(), header);
    }

    /// Free blocks can be zero, meaning the "real free space" that can be used to allocate is expected to be between first cell byte and end of cell pointer area
    pub fn computeFreeSpace(&self, dbHeader: Ref<DbHeader>) -> u16 {
        // TODO(pere): maybe free space is not calculated correctly with offset
        let pageContentSlice = self.asMutSlice();

        let pageUsableSpace = (dbHeader.pageSize - dbHeader.pageReservedSpace as u16) as usize;

        let cellContentAreaPos = {
            let mut cellContentAreaPos = self.cellContentAreaStartPos();
            if cellContentAreaPos == 0 {
                cellContentAreaPos = u16::MAX;
            }

            cellContentAreaPos
        };

        let fragFreeByteCount = self.fragFreeByteCount();
        let firstFreeBlockPos = self.firstFreeBlockPos();
        let cellCount = self.cellCount();
        let rightmostChildPageIndexByteLen = if self.isLeaf() { 0 } else { page::RIGHTMOST_CHILD_PAGE_INDEX_BYTE_LEN };

        let freeAreaStartPos = (self.offset + 8 + rightmostChildPageIndexByteLen + (page::POINTER_CELL_BYTE_LEN * cellCount)) as u16;

        let mut freeSpace = fragFreeByteCount as usize + cellContentAreaPos as usize;

        let mut freeBlockPos = firstFreeBlockPos as usize;
        if freeBlockPos > 0 {
            if freeBlockPos < cellContentAreaPos as usize {
                todo!("corrupted page");
            }

            let mut nextFreeBlockPos = 0;
            let mut freeBlockSize = 0;

            loop {
                // free block 第1,2 byte 是下个free block的pos
                nextFreeBlockPos = u16::from_be_bytes(pageContentSlice[freeBlockPos..freeBlockPos + 2].try_into().unwrap()) as usize;

                // 第3,4 byte 是 freeBlock总长度包含头4字节的
                freeBlockSize = u16::from_be_bytes(pageContentSlice[freeBlockPos + 2..freeBlockPos + 4].try_into().unwrap()) as usize;

                freeSpace += freeBlockSize;

                // nextFreeBlockPos <=0 能达到同样效果
                // 构成1个的free block 至少要4个byte 要是free的大小不够4的话 便称为 fragment  它顶大3 byte
                if nextFreeBlockPos <= freeBlockPos + freeBlockSize + page::FRAGMENT_MAX_BYTE_LEN {
                    break;
                }

                freeBlockPos = nextFreeBlockPos;
            }

            // 末尾的free block指向的是0
            if nextFreeBlockPos > 0 {
                todo!("corrupted page ascending order");
            }

            if freeBlockPos + freeBlockSize > pageUsableSpace {
                todo!("corrupted page last freeblock extends last page end");
            }
        }

        // don't count header and cell pointers?
        freeSpace -= freeAreaStartPos as usize;
        freeSpace as u16
    }


    /// 分配data cell是从page的末尾开始,函数返回末尾减去size后的pos
    pub fn allocateCellSpace(&self, dbHeader: &Rc<RefCell<DbHeader>>, expectSize: usize) -> u16 {
        let (cellStartPos, _) = self.getPointerCellsStartPos();
        let gapStartPos = cellStartPos + page::POINTER_CELL_BYTE_LEN * self.cellCount();

        let mut dataCellsStartPos = self.cellContentAreaStartPos() as usize;

        // there are free blocks and enough space
        // 为什么说有enough space 单看这个表达式确实看不出来,因为这个函数allocateCellSpace 是在 确认了pageFreeSpace够了后调用的
        if self.firstFreeBlockPos() != 0 && gapStartPos + page::POINTER_CELL_BYTE_LEN <= dataCellsStartPos {
            // 搜寻是不是有足够大的free block
            let (cellPos, found) = self.findFreeCell(dbHeader.borrow(), expectSize);
            if found {
                return cellPos as u16;
            }
        }

        // [header][pointerCells][gap][dataCells]
        // 意味着gap本身容不下 page::POINTER_CELL_BYTE_LEN + expectSize  需要dataCells部分defragment
        if gapStartPos + page::POINTER_CELL_BYTE_LEN + expectSize > dataCellsStartPos {
            self.defragment(dbHeader.borrow());
            dataCellsStartPos = self.cellContentAreaStartPos() as usize;
        }

        dataCellsStartPos -= expectSize;

        self.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT_START_POS, dataCellsStartPos as u16);

        assert!(dataCellsStartPos + expectSize <= dbHeader.borrow().pageUsableSpace());

        dataCellsStartPos as u16
    }

    fn findFreeCell(&self, dbHeader: Ref<DbHeader>, amount: usize) -> (usize, bool) {
        let mut pos = self.firstFreeBlockPos() as usize;

        let buf = self.asMutSlice();

        let maxPos = dbHeader.pageUsableSpace() - amount;

        let mut found = false;
        while pos <= maxPos {
            let nextFreeBlockPos = u16::from_be_bytes(buf[pos..pos + 2].try_into().unwrap());
            let freeBlockSize = u16::from_be_bytes(buf[pos + 2..pos + 4].try_into().unwrap());

            if amount <= freeBlockSize as usize {
                found = true;
                break;
            }

            pos = nextFreeBlockPos as usize;
        }

        if !found {
            (0, false)
        } else {
            (pos, true)
        }
    }

    /// 对page的dataCellRegion(cellContent)全量的重梳理排布
    fn defragment(&self, dbHeader: Ref<DbHeader>) {
        let pageContentOld = self.clone();

        // TODO(pere): usable space should include offset probably
        let pageUsableSpace = dbHeader.pageUsableSpace() as u64;
        let mut dataCellsStartPosNew = pageUsableSpace;

        let last_cell = pageUsableSpace - 4;

        let gapStartPos = {
            let (pointerCellRegionStartPos, pointerCellRegionByteLen) = pageContentOld.getPointerCellsStartPos();
            pointerCellRegionStartPos + pointerCellRegionByteLen
        };

        let bufNew = self.asMutSlice();

        if pageContentOld.cellCount() > 0 {
            let pageType = self.getPageType();
            let bufOld = pageContentOld.asMutSlice();

            for i in 0..pageContentOld.cellCount() {
                let pointerCellPos = self.offset + page::LEAF_PAGE_HEADER_BYTE_LEN + i * page::POINTER_CELL_BYTE_LEN;

                let dataCellPos = u16::from_be_bytes([bufOld[pointerCellPos], bufOld[pointerCellPos + 1]]) as u64;
                assert!(dataCellPos <= last_cell);

                let size = match pageType {
                    PageType::TableInterior => {
                        // fenquen 感觉它写错了 原来是readVarInt(&read_buf[pc as usize..])
                        let (_, rowIdByteLen) = match readVarInt(&bufOld[dataCellPos as usize + page::LEAF_PAGE_HEADER_BYTE_LEN..]) {
                            Ok(v) => v,
                            Err(_) => todo!("error while parsing varint from cell, probably treat this as corruption?"),
                        };
                        page::LEAF_PAGE_HEADER_BYTE_LEN as u64 + rowIdByteLen as u64
                    }
                    PageType::TableLeaf => {
                        let (payloadSize, payloadSizeByteLen) = match readVarInt(&bufOld[dataCellPos as usize..]) {
                            Ok(v) => v,
                            Err(_) => todo!("error while parsing varint from cell, probably treat this as corruption?"),
                        };

                        let (_, rowIdByteLen) = match readVarInt(&bufOld[dataCellPos as usize + payloadSizeByteLen..]) {
                            Ok(v) => v,
                            Err(_) => todo!("error while parsing varint from cell, probably treat this as corruption?"),
                        };

                        // TODO: add overflow page calculation
                        payloadSizeByteLen as u64 + rowIdByteLen as u64 + payloadSize
                    }
                    _ => todo!(),
                };

                // 它是不断的减少的,读应了data cell是从page的末尾倒序排步的
                dataCellsStartPosNew -= size;
                if dataCellsStartPosNew < gapStartPos as u64 || dataCellPos + size > pageUsableSpace {
                    todo!("corrupt");
                }

                assert!(dataCellsStartPosNew + size <= pageUsableSpace && dataCellsStartPosNew >= gapStartPos as u64);

                // set new pointer
                bufNew[pointerCellPos..pointerCellPos + page::POINTER_CELL_BYTE_LEN].copy_from_slice(&(dataCellsStartPosNew as u16).to_be_bytes());

                // copy payload
                bufNew[dataCellsStartPosNew as usize..dataCellsStartPosNew as usize + size as usize].copy_from_slice(&bufOld[dataCellPos as usize..dataCellPos as usize + size as usize]);
            }
        }

        assert!(dataCellsStartPosNew >= gapStartPos as u64);

        // 变更 dataCellRegion(cellContentArea)的start pos
        self.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT_START_POS, dataCellsStartPosNew as u16);

        // set free block to 0, unused spaced can be retrieved from gap between cell pointer end and content start
        self.write_u16(page::PAGE_HEADER_OFFSET_FREE_BLOCK, 0);

        let dataCellsStartPosOld = pageContentOld.cellContentAreaStartPos() as u64;
        assert!(dataCellsStartPosOld <= dataCellsStartPosNew);

        bufNew[dataCellsStartPosOld as usize..dataCellsStartPosNew as usize].fill(0);
    }
}

impl Clone for PageContent {
    fn clone(&self) -> Self {
        Self {
            offset: self.offset,
            buffer: Rc::new(RefCell::new((*self.buffer.borrow()).clone())),
            overflowCells: self.overflowCells.clone(),
        }
    }
}

pub fn beginReadPage(storage: Rc<dyn Storage>,
                     bufferPool: Rc<BufferPool>,
                     page: PageArc,
                     pageId: usize) -> Result<()> {
    let bufferData = bufferPool.get();

    let drop_fn = Rc::new(move |buf| {
        let buffer_pool = bufferPool.clone();
        buffer_pool.put(buf);
    });

    let buffer = Rc::new(RefCell::new(Buffer::new(bufferData, drop_fn)));

    let complete = Box::new(move |buf: Rc<RefCell<Buffer>>| {
        let page = page.clone();
        if finish_read_page(pageId, buf, page.clone()).is_err() {
            page.set_error();
        }
    });

    storage.readPage(pageId, Rc::new(CompletionEnum::Read(ReadCompletion::new(buffer, complete))))?;

    Ok(())
}

fn finish_read_page(page_idx: usize, buffer_ref: Rc<RefCell<Buffer>>, page: PageArc) -> Result<()> {
    let pos = if page_idx == 1 { DB_HEADER_SIZE } else { 0 };

    let inner = PageContent {
        offset: pos,
        buffer: buffer_ref.clone(),
        overflowCells: Vec::new(),
    };

    {
        page.getMutInner().pageContent.replace(inner);
        page.set_uptodate();
        page.clear_locked();
        page.set_loaded();
    }
    Ok(())
}

pub fn begin_write_btree_page(pager: &Pager,
                              page: &PageArc,
                              write_counter: Rc<RefCell<usize>>) -> Result<()> {
    let page_source = &pager.storage;
    let page_finish = page.clone();

    let page_id = page.getMutInner().pageId;

    let buffer = {
        let page = page.getMutInner();
        let contents = page.pageContent.as_ref().unwrap();
        contents.buffer.clone()
    };

    *write_counter.borrow_mut() += 1;
    let write_complete = {
        let buf_copy = buffer.clone();
        Box::new(move |bytes_written: i32| {
            let buf_copy = buf_copy.clone();
            let buf_len = buf_copy.borrow().len();
            *write_counter.borrow_mut() -= 1;

            page_finish.clear_dirty();
            if bytes_written < buf_len as i32 {
                log::error!("wrote({bytes_written}) less than expected({buf_len})");
            }
        })
    };
    let c = Rc::new(CompletionEnum::Write(WriteCompletion::new(write_complete)));
    page_source.writePage(page_id, buffer.clone(), c)?;
    Ok(())
}

pub fn begin_sync(page_io: Rc<dyn Storage>, syncing: Rc<RefCell<bool>>) -> Result<()> {
    assert!(!*syncing.borrow());
    *syncing.borrow_mut() = true;
    page_io.sync(Rc::new(CompletionEnum::Sync(SyncCompletion { complete: Box::new(move |_| { *syncing.borrow_mut() = false; }) })))?;
    Ok(())
}

#[allow(clippy::enum_variant_names)]
#[derive(Debug, Clone)]
pub enum BTreeCell {
    TableInteriorCell(TableInteriorCell),
    TableLeafCell(TableLeafCell),
    IndexInteriorCell(IndexInteriorCell),
    IndexLeafCell(IndexLeafCell),
}

#[derive(Debug, Clone)]
pub struct TableInteriorCell {
    pub leftChildPageIndex: u32,
    pub rowId: u64,
}

#[derive(Debug, Clone)]
pub struct TableLeafCell {
    pub rowId: u64,
    pub payload: Vec<u8>,
    pub firstOverflowPageIndex: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct IndexInteriorCell {
    pub left_child_page: u32,
    pub payload: Vec<u8>,
    pub first_overflow_page: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct IndexLeafCell {
    pub payload: Vec<u8>,
    pub first_overflow_page: Option<u32>,
}

pub fn readBtreeCell(pageData: &[u8],
                     pageType: &PageType,
                     pageDataPos: usize,
                     pager: Rc<Pager>,
                     maxLocal: usize,
                     minLocal: usize,
                     pageUsableSpace: usize) -> Result<BTreeCell> {
    let mut pos = pageDataPos;

    match pageType {
        PageType::TableInterior => {
            // https://www.sqlite.org/fileformat.html#b_tree_pages
            // A 4-byte big-endian page number which is the left child pointer
            let leftChildPageIndex = u32::from_be_bytes([pageData[pos], pageData[pos + 1], pageData[pos + 2], pageData[pos + 3]]);
            pos += 4;

            // A varint which is the integer key
            let (rowId, _) = readVarInt(&pageData[pos..])?;

            Ok(BTreeCell::TableInteriorCell(TableInteriorCell {
                leftChildPageIndex,
                rowId,
            }))
        }
        PageType::TableLeaf => {
            let (payloadSize, nr) = readVarInt(&pageData[pos..])?;
            pos += nr;

            let (rowid, nr) = readVarInt(&pageData[pos..])?;
            pos += nr;

            let (overflows, to_read) = payload_overflows(payloadSize as usize, maxLocal, minLocal, pageUsableSpace);
            let to_read = if overflows { to_read } else { pageData.len() - pos };

            let (payload, first_overflow_page) = read_payload(&pageData[pos..pos + to_read], payloadSize as usize, pager);

            Ok(BTreeCell::TableLeafCell(TableLeafCell {
                rowId: rowid,
                payload: payload,
                firstOverflowPageIndex: first_overflow_page,
            }))
        }
        PageType::IndexInterior => {
            // https://www.sqlite.org/fileformat.html#b_tree_pages
            // A 4-byte big-endian page number which is the left child pointer
            let leftChildPageIndex = u32::from_be_bytes([pageData[pos], pageData[pos + 1], pageData[pos + 2], pageData[pos + 3]]);
            pos += 4;

            let (payload_size, nr) = readVarInt(&pageData[pos..])?;
            pos += nr;

            let (overflows, to_read) = payload_overflows(payload_size as usize, maxLocal, minLocal, pageUsableSpace);

            let to_read =
                if overflows {
                    to_read
                } else {
                    pageData.len() - pos
                };

            let (payload, first_overflow_page) = read_payload(&pageData[pos..pos + to_read], payload_size as usize, pager);

            Ok(BTreeCell::IndexInteriorCell(IndexInteriorCell {
                left_child_page: leftChildPageIndex,
                payload,
                first_overflow_page,
            }))
        }
        PageType::IndexLeaf => {
            let (payload_size, nr) = readVarInt(&pageData[pos..])?;
            pos += nr;

            let (overflows, to_read) = payload_overflows(payload_size as usize, maxLocal, minLocal, pageUsableSpace);

            let to_read = if overflows {
                to_read
            } else {
                pageData.len() - pos
            };

            let (payload, first_overflow_page) = read_payload(&pageData[pos..pos + to_read], payload_size as usize, pager);

            Ok(BTreeCell::IndexLeafCell(IndexLeafCell {
                payload,
                first_overflow_page,
            }))
        }
    }
}

/// read_payload takes in the unread bytearray with the payload size
/// and returns the payload on the page, and optionally the first overflow page number.
#[allow(clippy::readonly_write_lock)]
fn read_payload(unread: &[u8], payload_size: usize, pager: Rc<Pager>) -> (Vec<u8>, Option<u32>) {
    let cell_len = unread.len();
    if payload_size <= cell_len {
        // fit within 1 page
        (unread[..payload_size].to_vec(), None)
    } else {
        // overflow
        let first_overflow_page = u32::from_be_bytes([
            unread[cell_len - 4],
            unread[cell_len - 3],
            unread[cell_len - 2],
            unread[cell_len - 1],
        ]);
        let usable_size = pager.usable_size();
        let mut next_overflow = first_overflow_page;
        let mut payload = unread[..cell_len - 4].to_vec();
        let mut left_to_read = payload_size - (cell_len - 4); // minus four because last for bytes of a payload cell are the overflow pointer
        while next_overflow != 0 {
            assert!(left_to_read > 0);
            let page;
            loop {
                let page_ref = pager.readPage(next_overflow as usize);
                if let Ok(p) = page_ref {
                    page = p;
                    break;
                }
            }
            let page = page.getMutInner();
            let pageContent = page.pageContent.as_mut().unwrap();

            let to_read = left_to_read.min(usable_size - 4);
            let buf = pageContent.asMutSlice();
            payload.extend_from_slice(&buf[4..4 + to_read]);

            next_overflow = pageContent.read_u32(0);
            left_to_read -= to_read;
        }
        assert_eq!(left_to_read, 0);

        (payload, Some(first_overflow_page))
    }
}

#[derive(Debug, PartialEq)]
pub enum SerialType {
    Null,
    UInt8,
    BEInt16,
    BEInt24,
    BEInt32,
    BEInt48,
    BEInt64,
    BEFloat64,
    ConstInt0,
    ConstInt1,
    Blob(usize),
    String(usize),
}

impl TryFrom<u64> for SerialType {
    type Error = crate::error::LimboError;

    fn try_from(value: u64) -> Result<Self> {
        match value {
            0 => Ok(Self::Null),
            1 => Ok(Self::UInt8),
            2 => Ok(Self::BEInt16),
            3 => Ok(Self::BEInt24),
            4 => Ok(Self::BEInt32),
            5 => Ok(Self::BEInt48),
            6 => Ok(Self::BEInt64),
            7 => Ok(Self::BEFloat64),
            8 => Ok(Self::ConstInt0),
            9 => Ok(Self::ConstInt1),
            n if value >= 12 && value % 2 == 0 => Ok(Self::Blob(((n - 12) / 2) as usize)),
            n if value >= 13 && value % 2 == 1 => Ok(Self::String(((n - 13) / 2) as usize)),
            _ => crate::bail_corrupt_error!("Invalid serial type: {}", value),
        }
    }
}

pub fn read_record(payload: &[u8]) -> Result<OwnedRecord> {
    let mut pos = 0;
    let (header_size, nr) = readVarInt(payload)?;
    assert!((header_size as usize) >= nr);
    let mut header_size = (header_size as usize) - nr;
    pos += nr;
    let mut serial_types = Vec::with_capacity(header_size);
    while header_size > 0 {
        let (serial_type, nr) = readVarInt(&payload[pos..])?;
        let serial_type = SerialType::try_from(serial_type)?;
        serial_types.push(serial_type);
        pos += nr;
        assert!(header_size >= nr);
        header_size -= nr;
    }
    let mut values = Vec::with_capacity(serial_types.len());
    for serial_type in &serial_types {
        let (value, n) = read_value(&payload[pos..], serial_type)?;
        pos += n;
        values.push(value);
    }
    Ok(OwnedRecord::new(values))
}

pub fn read_value(buf: &[u8], serial_type: &SerialType) -> Result<(OwnedValue, usize)> {
    match *serial_type {
        SerialType::Null => Ok((OwnedValue::Null, 0)),
        SerialType::UInt8 => {
            if buf.is_empty() {
                crate::bail_corrupt_error!("Invalid UInt8 value");
            }
            Ok((OwnedValue::Integer(buf[0] as i64), 1))
        }
        SerialType::BEInt16 => {
            if buf.len() < 2 {
                crate::bail_corrupt_error!("Invalid BEInt16 value");
            }

            Ok((OwnedValue::Integer(i16::from_be_bytes([buf[0], buf[1]]) as i64), 2))
        }
        SerialType::BEInt24 => {
            if buf.len() < 3 {
                crate::bail_corrupt_error!("Invalid BEInt24 value");
            }

            Ok((OwnedValue::Integer(i32::from_be_bytes([0, buf[0], buf[1], buf[2]]) as i64), 3))
        }
        SerialType::BEInt32 => {
            if buf.len() < 4 {
                crate::bail_corrupt_error!("Invalid BEInt32 value");
            }

            Ok((OwnedValue::Integer(i32::from_be_bytes([buf[0], buf[1], buf[2], buf[3]]) as i64), 4))
        }
        SerialType::BEInt48 => {
            if buf.len() < 6 {
                crate::bail_corrupt_error!("Invalid BEInt48 value");
            }

            Ok((OwnedValue::Integer(i64::from_be_bytes([0, 0, buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], ])), 6))
        }
        SerialType::BEInt64 => {
            if buf.len() < 8 {
                crate::bail_corrupt_error!("Invalid BEInt64 value");
            }

            Ok((OwnedValue::Integer(i64::from_be_bytes([buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7], ])), 8))
        }
        SerialType::BEFloat64 => {
            if buf.len() < 8 {
                crate::bail_corrupt_error!("Invalid BEFloat64 value");
            }

            Ok((OwnedValue::Float(f64::from_be_bytes([buf[0], buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7], ])), 8))
        }
        SerialType::ConstInt0 => Ok((OwnedValue::Integer(0), 0)),
        SerialType::ConstInt1 => Ok((OwnedValue::Integer(1), 0)),
        SerialType::Blob(n) => {
            if buf.len() < n {
                crate::bail_corrupt_error!("Invalid Blob value");
            }

            Ok((OwnedValue::Blob(buf[0..n].to_vec().into()), n))
        }
        SerialType::String(n) => {
            if buf.len() < n {
                crate::bail_corrupt_error!("Invalid String value, length {} < expected length {}",buf.len(),n);
            }

            let bytes = buf[0..n].to_vec();
            let value = unsafe { String::from_utf8_unchecked(bytes) };
            Ok((OwnedValue::Text(value.into()), n))
        }
    }
}

pub fn readVarInt(buf: &[u8]) -> Result<(u64, usize)> {
    let mut v: u64 = 0;
    for i in 0..8 {
        match buf.get(i) {
            Some(c) => {
                v = (v << 7) + (c & 0x7f) as u64;
                if (c & 0x80) == 0 {
                    return Ok((v, i + 1));
                }
            }
            None => crate::bail_corrupt_error!("Invalid varint"),
        }
    }
    v = (v << 8) + buf[8] as u64;
    Ok((v, 9))
}

pub fn write_varint(buf: &mut [u8], value: u64) -> usize {
    if value <= 0x7f {
        buf[0] = (value & 0x7f) as u8;
        return 1;
    }

    if value <= 0x3fff {
        buf[0] = (((value >> 7) & 0x7f) | 0x80) as u8;
        buf[1] = (value & 0x7f) as u8;
        return 2;
    }

    let mut value = value;
    if (value & ((0xff000000_u64) << 32)) > 0 {
        buf[8] = value as u8;
        value >>= 8;
        for i in (0..8).rev() {
            buf[i] = ((value & 0x7f) | 0x80) as u8;
            value >>= 7;
        }
        return 9;
    }

    let mut encoded: [u8; 10] = [0; 10];
    let mut bytes = value;
    let mut n = 0;
    while bytes != 0 {
        let v = 0x80 | (bytes & 0x7f);
        encoded[n] = v as u8;
        bytes >>= 7;
        n += 1;
    }
    encoded[0] &= 0x7f;
    for i in 0..n {
        buf[i] = encoded[n - 1 - i];
    }
    n
}

pub fn writeVarInt2Vec(value: u64, destVec: &mut Vec<u8>) {
    let mut varint: Vec<u8> = vec![0; 9];
    let n = write_varint(&mut varint.as_mut_slice()[0..9], value);
    varint.truncate(n);
    destVec.extend_from_slice(&varint);
}

pub fn begin_read_wal_header(io: &Rc<dyn File>) -> Result<Arc<RwLock<WalHeader>>> {
    let drop_fn = Rc::new(|_buf| {});
    let buf = Rc::new(RefCell::new(Buffer::allocate(512, drop_fn)));
    let result = Arc::new(RwLock::new(WalHeader::default()));
    let header = result.clone();
    let complete = Box::new(move |buf: Rc<RefCell<Buffer>>| {
        let header = header.clone();
        finish_read_wal_header(buf, header).unwrap();
    });
    let c = Rc::new(CompletionEnum::Read(ReadCompletion::new(buf, complete)));
    io.pread(0, c)?;
    Ok(result)
}

fn finish_read_wal_header(buf: Rc<RefCell<Buffer>>, header: Arc<RwLock<WalHeader>>) -> Result<()> {
    let buf = buf.borrow();
    let buf = buf.as_slice();
    let mut header = header.write().unwrap();
    header.magic = u32::from_be_bytes([buf[0], buf[1], buf[2], buf[3]]);
    header.file_format = u32::from_be_bytes([buf[4], buf[5], buf[6], buf[7]]);
    header.page_size = u32::from_be_bytes([buf[8], buf[9], buf[10], buf[11]]);
    header.checkpoint_seq = u32::from_be_bytes([buf[12], buf[13], buf[14], buf[15]]);
    header.salt_1 = u32::from_be_bytes([buf[16], buf[17], buf[18], buf[19]]);
    header.salt_2 = u32::from_be_bytes([buf[20], buf[21], buf[22], buf[23]]);
    header.checksum_1 = u32::from_be_bytes([buf[24], buf[25], buf[26], buf[27]]);
    header.checksum_2 = u32::from_be_bytes([buf[28], buf[29], buf[30], buf[31]]);
    Ok(())
}

pub fn begin_read_wal_frame(io: &Rc<dyn File>,
                            offset: usize,
                            buffer_pool: Rc<BufferPool>,
                            page: PageArc) -> Result<()> {
    let buf = buffer_pool.get();
    let drop_fn = Rc::new(move |buf| {
        let buffer_pool = buffer_pool.clone();
        buffer_pool.put(buf);
    });
    let buf = Rc::new(RefCell::new(Buffer::new(buf, drop_fn)));
    let frame = page.clone();
    let complete = Box::new(move |buf: Rc<RefCell<Buffer>>| {
        let frame = frame.clone();
        finish_read_page(2, buf, frame).unwrap();
    });
    let c = Rc::new(CompletionEnum::Read(ReadCompletion::new(buf, complete)));
    io.pread(offset, c)?;
    Ok(())
}

pub fn begin_write_wal_frame(io: &Rc<dyn File>,
                             offset: usize,
                             page: &PageArc,
                             db_size: u32,
                             write_counter: Rc<RefCell<usize>>,
                             wal_header: &WalHeader,
                             checksums: (u32, u32)) -> Result<(u32, u32)> {
    let page_finish = page.clone();
    let page_id = page.getMutInner().pageId;
    trace!("begin_write_wal_frame(offset={}, page={})", offset, page_id);

    let mut header = WalFrameHeader {
        page_number: page_id as u32,
        db_size,
        salt_1: 0,
        salt_2: 0,
        checksum_1: 0,
        checksum_2: 0,
    };
    let (buffer, checksums) = {
        let page = page.getMutInner();
        let contents = page.pageContent.as_ref().unwrap();
        let drop_fn = Rc::new(|_buf| {});

        let mut buffer = Buffer::allocate(
            contents.buffer.borrow().len() + wal::WAL_FRAME_HEADER_SIZE,
            drop_fn,
        );
        let buf = buffer.as_mut_slice();
        buf[0..4].copy_from_slice(&header.page_number.to_be_bytes());
        buf[4..8].copy_from_slice(&header.db_size.to_be_bytes());

        {
            let contents_buf = contents.asMutSlice();
            let expects_be = wal_header.magic & 1; // LSB is set on big endian checksums
            let use_native_endian = cfg!(target_endian = "big") as u32 == expects_be; // check if checksum
            // type and native type is the same so that we know when to swap bytes
            let checksums = checksum_wal(&buf[0..8], wal_header, checksums, use_native_endian);
            let checksums = checksum_wal(contents_buf, wal_header, checksums, use_native_endian);
            header.checksum_1 = checksums.0;
            header.checksum_2 = checksums.1;
            header.salt_1 = wal_header.salt_1;
            header.salt_2 = wal_header.salt_2;
        }

        buf[8..12].copy_from_slice(&header.salt_1.to_be_bytes());
        buf[12..16].copy_from_slice(&header.salt_2.to_be_bytes());
        buf[16..20].copy_from_slice(&header.checksum_1.to_be_bytes());
        buf[20..24].copy_from_slice(&header.checksum_2.to_be_bytes());
        buf[wal::WAL_FRAME_HEADER_SIZE..].copy_from_slice(contents.asMutSlice());

        (Rc::new(RefCell::new(buffer)), checksums)
    };

    *write_counter.borrow_mut() += 1;
    let write_complete = {
        let buf_copy = buffer.clone();
        Box::new(move |bytes_written: i32| {
            let buf_copy = buf_copy.clone();
            let buf_len = buf_copy.borrow().len();
            *write_counter.borrow_mut() -= 1;

            page_finish.clear_dirty();
            if bytes_written < buf_len as i32 {
                log::error!("wrote({bytes_written}) less than expected({buf_len})");
            }
        })
    };
    let c = Rc::new(CompletionEnum::Write(WriteCompletion::new(write_complete)));
    io.pwrite(offset, buffer.clone(), c)?;
    Ok(checksums)
}

pub fn begin_write_wal_header(io: &Rc<dyn File>, header: &WalHeader) -> Result<()> {
    let buffer = {
        let drop_fn = Rc::new(|_buf| {});

        let mut buffer = Buffer::allocate(512, drop_fn);
        let buf = buffer.as_mut_slice();

        buf[0..4].copy_from_slice(&header.magic.to_be_bytes());
        buf[4..8].copy_from_slice(&header.file_format.to_be_bytes());
        buf[8..12].copy_from_slice(&header.page_size.to_be_bytes());
        buf[12..16].copy_from_slice(&header.checkpoint_seq.to_be_bytes());
        buf[16..20].copy_from_slice(&header.salt_1.to_be_bytes());
        buf[20..24].copy_from_slice(&header.salt_2.to_be_bytes());
        buf[24..28].copy_from_slice(&header.checksum_1.to_be_bytes());
        buf[28..32].copy_from_slice(&header.checksum_2.to_be_bytes());

        Rc::new(RefCell::new(buffer))
    };

    let write_complete = {
        Box::new(move |bytes_written: i32| {
            if bytes_written < wal::WAL_HEADER_SIZE as i32 {
                log::error!("wal header wrote({bytes_written}) less than expected({})",wal::WAL_FRAME_HEADER_SIZE);
            }
        })
    };
    let c = Rc::new(CompletionEnum::Write(WriteCompletion::new(write_complete)));
    io.pwrite(0, buffer.clone(), c)?;
    Ok(())
}


/// Checks if payload will overflow a cell based on max local and
/// it will return the min size that will be stored in that case,
/// including overflow pointer
pub fn payload_overflows(payloadSize: usize,
                         maxLocal: usize,
                         minLocal: usize,
                         usableSize: usize) -> (bool, usize) {
    if payloadSize <= maxLocal {
        return (false, 0);
    }

    let mut space_left = minLocal + (payloadSize - minLocal) % (usableSize - 4);

    if space_left > maxLocal {
        space_left = minLocal;
    }

    (true, space_left + 4)
}

pub fn checksum_wal(buf: &[u8],
                    _wal_header: &WalHeader,
                    input: (u32, u32),
                    useBigEndian: bool) -> (u32, u32) {
    assert_eq!(buf.len() % 8, 0, "buffer must be a multiple of 8");
    let mut s0: u32 = input.0;
    let mut s1: u32 = input.1;
    let mut i = 0;
    if useBigEndian {
        while i < buf.len() {
            let v0 = u32::from_ne_bytes(buf[i..i + 4].try_into().unwrap());
            let v1 = u32::from_ne_bytes(buf[i + 4..i + 8].try_into().unwrap());
            s0 = s0.wrapping_add(v0.wrapping_add(s1));
            s1 = s1.wrapping_add(v1.wrapping_add(s0));
            i += 8;
        }
    } else {
        while i < buf.len() {
            let v0 = u32::from_ne_bytes(buf[i..i + 4].try_into().unwrap()).swap_bytes();
            let v1 = u32::from_ne_bytes(buf[i + 4..i + 8].try_into().unwrap()).swap_bytes();
            s0 = s0.wrapping_add(v0.wrapping_add(s1));
            s1 = s1.wrapping_add(v1.wrapping_add(s0));
            i += 8;
        }
    }
    (s0, s1)
}

impl WalHeader {
    pub fn as_bytes(&self) -> &[u8] {
        unsafe { std::mem::transmute::<&WalHeader, &[u8; size_of::<WalHeader>()]>(self) }
    }
}