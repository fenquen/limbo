use log::debug;
use crate::storage::page::Pager;
use crate::storage::sqlite3_ondisk::{
    readBtreeCell, readVarInt, write_varint, BTreeCell, DbHeader, PageContent, PageType,
    TableInteriorCell, TableLeafCell,
};
use crate::types::{Cursor, CursorResult, OwnedRecord, OwnedValue, SeekKey, SeekOp};
use crate::Result;
use std::cell::{Ref, RefCell};
use std::pin::Pin;
use std::rc::Rc;
use crate::storage::sqlite3_ondisk;
use super::page::PageArc;
use super::sqlite3_ondisk::{write_varint_to_vec, IndexInteriorCell, IndexLeafCell, OverflowCell, DATABASE_HEADER_SIZE};

/// type of btree page -> u8
const BTREE_HEADER_OFFSET_TYPE: usize = 0;

/// pointer to first freeblock -> u16
const BTREE_HEADER_OFFSET_FREE_BLOCK: usize = 1;

/// number of cells in the page -> u16
const BTREE_HEADER_OFFSET_CELL_COUNT: usize = 3;

/// pointer to first byte of cell allocated content from top -> u16
const BTREE_HEADER_OFFSET_CELL_CONTENT: usize = 5;

/// number of fragmented bytes -> u8
const BTREE_HEADER_OFFSET_FRAGMENTED: usize = 7;

/// if internal node, pointer right most pointer (saved separately from cells) -> u32
const BTREE_HEADER_OFFSET_RIGHTMOST: usize = 8;

/*
** Maximum depth of an SQLite B-Tree structure. Any B-Tree deeper than
** this will be declared corrupt. This value is calculated based on a
** maximum database size of 2^31 pages a minimum fanout of 2 for a
** root-node and 3 for all other internal nodes.
**
** If a tree that appears to be taller than this is encountered, it is
** assumed that the database is corrupt.
*/
pub const BT_CURSOR_MAX_DEPTH: usize = 20;

/// Evaluate a Result<CursorResult<T>>, if IO return IO.
macro_rules! return_if_io {
    ($expr:expr) => {
        match $expr? {
            CursorResult::Ok(v) => v,
            CursorResult::IO => return Ok(CursorResult::IO),
        }
    };
}

/// Check if the page is unlocked, if not return IO.
macro_rules! return_if_locked {
    ($expr:expr) => {{
        if $expr.is_locked() {
            return Ok(CursorResult::IO);
        }
    }};
}

pub struct BTreeCursor {
    pager: Rc<Pager>,

    /// Page id of the root page used to go back up fast.
    rootPageId: usize,

    /// Rowid and record are stored before being consumed.
    rowid: RefCell<Option<u64>>,
    record: RefCell<Option<OwnedRecord>>,

    null_flag: bool,
    dbHeader: Rc<RefCell<DbHeader>>,

    /// Index internal pages are consumed on the way up, so we store going upwards flag in case
    /// we just moved to a parent page and the parent page is an internal index page which requires to be consumed
    going_upwards: bool,

    writeInfo: WriteInfo,

    /// Page stack used to traverse the btree.
    /// Each cursor has a stack because each cursor traverses the btree independently
    pageStack: PageStack,
}

impl Cursor for BTreeCursor {
    fn is_empty(&self) -> bool {
        self.record.borrow().is_none()
    }

    fn root_page(&self) -> usize {
        self.rootPageId
    }

    fn rewind(&mut self) -> Result<CursorResult<()>> {
        self.move2Root();

        let (rowid, record) = return_if_io!(self.get_next_record(None));
        self.rowid.replace(rowid);
        self.record.replace(record);
        Ok(CursorResult::Ok(()))
    }

    fn last(&mut self) -> Result<CursorResult<()>> {
        match self.move2Rightmost()? {
            CursorResult::Ok(_) => self.prev(),
            CursorResult::IO => Ok(CursorResult::IO),
        }
    }

    fn next(&mut self) -> Result<CursorResult<()>> {
        let (rowid, record) = return_if_io!(self.get_next_record(None));
        self.rowid.replace(rowid);
        self.record.replace(record);
        Ok(CursorResult::Ok(()))
    }

    fn prev(&mut self) -> Result<CursorResult<()>> {
        match self.get_prev_record()? {
            CursorResult::Ok((rowid, record)) => {
                self.rowid.replace(rowid);
                self.record.replace(record);
                Ok(CursorResult::Ok(()))
            }
            CursorResult::IO => Ok(CursorResult::IO),
        }
    }

    fn wait_for_completion(&mut self) -> Result<()> {
        // TODO: Wait for pager I/O to complete
        Ok(())
    }

    fn rowid(&self) -> Result<Option<u64>> {
        Ok(*self.rowid.borrow())
    }

    fn seek(&mut self, key: SeekKey<'_>, op: SeekOp) -> Result<CursorResult<bool>> {
        let (rowid, record) = return_if_io!(self.seek(key, op));
        self.rowid.replace(rowid);
        self.record.replace(record);
        Ok(CursorResult::Ok(rowid.is_some()))
    }

    fn seek_to_last(&mut self) -> Result<CursorResult<()>> {
        return_if_io!(self.move2Rightmost());
        let (rowid, record) = return_if_io!(self.get_next_record(None));
        if rowid.is_none() {
            let is_empty = return_if_io!(self.is_empty_table());
            assert!(is_empty);
            return Ok(CursorResult::Ok(()));
        }
        self.rowid.replace(rowid);
        self.record.replace(record);
        Ok(CursorResult::Ok(()))
    }

    fn record(&self) -> Result<Ref<Option<OwnedRecord>>> {
        Ok(self.record.borrow())
    }

    fn insert(&mut self,
              key: &OwnedValue,
              rec: &OwnedRecord,
              movedBefore: bool) -> Result<CursorResult<()>> {
        let intKey = match key {
            OwnedValue::Integer(i) => i,
            _ => unreachable!("btree tables are indexed by integers!"),
        };

        if !movedBefore {
            return_if_io!(self.moveTo(SeekKey::TableRowId(*intKey as u64), SeekOp::EQ));
        }

        return_if_io!(self.insertIntoPage(key, rec));

        self.rowid.replace(Some(*intKey as u64));

        Ok(CursorResult::Ok(()))
    }

    fn exists(&mut self, key: &OwnedValue) -> Result<CursorResult<bool>> {
        let int_key = match key {
            OwnedValue::Integer(i) => i,
            _ => unreachable!("btree tables are indexed by integers!"),
        };
        return_if_io!(self.moveTo(SeekKey::TableRowId(*int_key as u64), SeekOp::EQ));
        let page = self.pageStack.top();
        // TODO(pere): request load
        return_if_locked!(page);

        let contents = page.getMutInner().pageContent.as_ref().unwrap();

        // find cell
        let int_key = match key {
            OwnedValue::Integer(i) => *i as u64,
            _ => unreachable!("btree tables are indexed by integers!"),
        };

        let cell_idx = self.find_cell(contents, int_key);
        if cell_idx >= contents.cellCount() {
            Ok(CursorResult::Ok(false))
        } else {
            let equals = match &contents.getCell(cell_idx,
                                                 self.pager.clone(),
                                                 self.max_local(contents.getPageType()),
                                                 self.min_local(),
                                                 self.pageUsableSpace())? {
                BTreeCell::TableLeafCell(l) => l._rowid == int_key,
                _ => unreachable!(),
            };

            Ok(CursorResult::Ok(equals))
        }
    }

    fn set_null_flag(&mut self, flag: bool) {
        self.null_flag = flag;
    }

    fn get_null_flag(&self) -> bool {
        self.null_flag
    }

    fn btree_create(&mut self, flags: usize) -> u32 {
        let page_type = match flags {
            1 => PageType::TableLeaf,
            2 => PageType::IndexLeaf,
            _ => unreachable!("wrong create table falgs, should be 1 for table and 2 for index, got {}", flags, ),
        };

        let page = self.allocate_page(page_type, 0);
        let id = page.getMutInner().pageId;
        id as u32
    }
}

impl BTreeCursor {
    pub fn new(pager: Rc<Pager>,
               rootPageId: usize,
               dbHeader: Rc<RefCell<DbHeader>>) -> BTreeCursor {
        BTreeCursor {
            pager,
            rootPageId,
            rowid: RefCell::new(None),
            record: RefCell::new(None),
            null_flag: false,
            dbHeader,
            going_upwards: false,
            writeInfo: WriteInfo {
                writeState: WriteState::Start,
                new_pages: RefCell::new(Vec::with_capacity(4)),
                scratch_cells: RefCell::new(Vec::new()),
                rightmost_pointer: RefCell::new(None),
                page_copy: RefCell::new(None),
            },
            pageStack: PageStack {
                curPageIndexInStack: RefCell::new(-1),
                cell_indices: RefCell::new([0; BT_CURSOR_MAX_DEPTH + 1]),
                pageStack: RefCell::new([const { None }; BT_CURSOR_MAX_DEPTH + 1]),
            },
        }
    }

    fn is_empty_table(&self) -> Result<CursorResult<bool>> {
        let page = self.pager.readPage(self.rootPageId)?;
        return_if_locked!(page);

        let cell_count = page.getMutInner().pageContent.as_ref().unwrap().cellCount();
        Ok(CursorResult::Ok(cell_count == 0))
    }

    fn get_prev_record(&mut self) -> Result<CursorResult<(Option<u64>, Option<OwnedRecord>)>> {
        loop {
            let page = self.pageStack.top();
            let cell_idx = self.pageStack.current_index();

            // moved to current page begin
            // todo: find a better way to flag moved to end or begin of page
            if self.pageStack.curr_idx_out_of_begin() {
                loop {
                    if self.pageStack.current_index() > 0 {
                        self.pageStack.retreat();
                        break;
                    }
                    if self.pageStack.has_parent() {
                        self.pageStack.pop();
                    } else {
                        // moved to begin of btree
                        return Ok(CursorResult::Ok((None, None)));
                    }
                }
                // continue to next loop to get record from the new page
                continue;
            }

            let cell_idx = cell_idx as usize;
            debug!(
                "get_prev_record current id={} cell={}",
                page.getMutInner().pageId,
                cell_idx
            );
            return_if_locked!(page);
            if !page.is_loaded() {
                self.pager.load_page(page.clone())?;
                return Ok(CursorResult::IO);
            }
            let contents = page.getMutInner().pageContent.as_ref().unwrap();

            let cell_count = contents.cellCount();
            let cell_idx = if cell_idx >= cell_count {
                self.pageStack.set_cell_index(cell_count as i32 - 1);
                cell_count - 1
            } else {
                cell_idx
            };

            let cell = contents.getCell(
                cell_idx,
                self.pager.clone(),
                self.max_local(contents.getPageType()),
                self.min_local(),
                self.pageUsableSpace(),
            )?;

            match cell {
                BTreeCell::TableInteriorCell(TableInteriorCell {
                                                 leftChildPageIndex: _left_child_page,
                                                 rowId: _rowid,
                                             }) => {
                    let mem_page = self.pager.readPage(_left_child_page as usize)?;
                    self.pageStack.push(mem_page);
                    // use cell_index = i32::MAX to tell next loop to go to the end of the current page
                    self.pageStack.set_cell_index(i32::MAX);
                    continue;
                }
                BTreeCell::TableLeafCell(TableLeafCell {
                                             _rowid, _payload, ..
                                         }) => {
                    self.pageStack.retreat();
                    let record: OwnedRecord =
                        crate::storage::sqlite3_ondisk::read_record(&_payload)?;
                    return Ok(CursorResult::Ok((Some(_rowid), Some(record))));
                }
                BTreeCell::IndexInteriorCell(_) => todo!(),
                BTreeCell::IndexLeafCell(_) => todo!(),
            }
        }
    }

    fn get_next_record(
        &mut self,
        predicate: Option<(SeekKey<'_>, SeekOp)>,
    ) -> Result<CursorResult<(Option<u64>, Option<OwnedRecord>)>> {
        loop {
            let mem_page_rc = self.pageStack.top();
            let cell_idx = self.pageStack.current_index() as usize;

            debug!("current id={} cell={}", mem_page_rc.getMutInner().pageId, cell_idx);
            return_if_locked!(mem_page_rc);
            if !mem_page_rc.is_loaded() {
                self.pager.load_page(mem_page_rc.clone())?;
                return Ok(CursorResult::IO);
            }
            let mem_page = mem_page_rc.getMutInner();

            let contents = mem_page.pageContent.as_ref().unwrap();

            if cell_idx == contents.cellCount() {
                // do rightmost
                let has_parent = self.pageStack.has_parent();
                match contents.rightmostPtr() {
                    Some(right_most_pointer) => {
                        self.pageStack.advance();
                        let mem_page = self.pager.readPage(right_most_pointer as usize)?;
                        self.pageStack.push(mem_page);
                        continue;
                    }
                    None => {
                        if has_parent {
                            debug!("moving simple upwards");
                            self.going_upwards = true;
                            self.pageStack.pop();
                            continue;
                        } else {
                            return Ok(CursorResult::Ok((None, None)));
                        }
                    }
                }
            }

            if cell_idx > contents.cellCount() {
                // end
                let has_parent = self.pageStack.current() > 0;
                if has_parent {
                    debug!("moving upwards");
                    self.going_upwards = true;
                    self.pageStack.pop();
                    continue;
                } else {
                    return Ok(CursorResult::Ok((None, None)));
                }
            }
            assert!(cell_idx < contents.cellCount());

            let cell = contents.getCell(
                cell_idx,
                self.pager.clone(),
                self.max_local(contents.getPageType()),
                self.min_local(),
                self.pageUsableSpace(),
            )?;
            match &cell {
                BTreeCell::TableInteriorCell(TableInteriorCell {
                                                 leftChildPageIndex: _left_child_page,
                                                 rowId: _rowid,
                                             }) => {
                    assert!(predicate.is_none());
                    self.pageStack.advance();
                    let mem_page = self.pager.readPage(*_left_child_page as usize)?;
                    self.pageStack.push(mem_page);
                    continue;
                }
                BTreeCell::TableLeafCell(TableLeafCell {
                                             _rowid,
                                             _payload,
                                             first_overflow_page: _,
                                         }) => {
                    assert!(predicate.is_none());
                    self.pageStack.advance();
                    let record = crate::storage::sqlite3_ondisk::read_record(_payload)?;
                    return Ok(CursorResult::Ok((Some(*_rowid), Some(record))));
                }
                BTreeCell::IndexInteriorCell(IndexInteriorCell {
                                                 payload,
                                                 left_child_page,
                                                 ..
                                             }) => {
                    if !self.going_upwards {
                        let mem_page = self.pager.readPage(*left_child_page as usize)?;
                        self.pageStack.push(mem_page);
                        continue;
                    }

                    self.going_upwards = false;
                    self.pageStack.advance();

                    let record = crate::storage::sqlite3_ondisk::read_record(payload)?;
                    if predicate.is_none() {
                        let rowid = match record.values.last() {
                            Some(OwnedValue::Integer(rowid)) => *rowid as u64,
                            _ => unreachable!("index cells should have an integer rowid"),
                        };
                        return Ok(CursorResult::Ok((Some(rowid), Some(record))));
                    }

                    let (key, op) = predicate.as_ref().unwrap();
                    let SeekKey::IndexKey(index_key) = key else {
                        unreachable!("index seek key should be a record");
                    };
                    let found = match op {
                        SeekOp::GT => &record > *index_key,
                        SeekOp::GE => &record >= *index_key,
                        SeekOp::EQ => &record == *index_key,
                    };
                    if found {
                        let rowid = match record.values.last() {
                            Some(OwnedValue::Integer(rowid)) => *rowid as u64,
                            _ => unreachable!("index cells should have an integer rowid"),
                        };
                        return Ok(CursorResult::Ok((Some(rowid), Some(record))));
                    } else {
                        continue;
                    }
                }
                BTreeCell::IndexLeafCell(IndexLeafCell { payload, .. }) => {
                    self.pageStack.advance();
                    let record = crate::storage::sqlite3_ondisk::read_record(payload)?;
                    if predicate.is_none() {
                        let rowid = match record.values.last() {
                            Some(OwnedValue::Integer(rowid)) => *rowid as u64,
                            _ => unreachable!("index cells should have an integer rowid"),
                        };
                        return Ok(CursorResult::Ok((Some(rowid), Some(record))));
                    }
                    let (key, op) = predicate.as_ref().unwrap();
                    let SeekKey::IndexKey(index_key) = key else {
                        unreachable!("index seek key should be a record");
                    };
                    let found = match op {
                        SeekOp::GT => &record > *index_key,
                        SeekOp::GE => &record >= *index_key,
                        SeekOp::EQ => &record == *index_key,
                    };
                    if found {
                        let rowid = match record.values.last() {
                            Some(OwnedValue::Integer(rowid)) => *rowid as u64,
                            _ => unreachable!("index cells should have an integer rowid"),
                        };
                        return Ok(CursorResult::Ok((Some(rowid), Some(record))));
                    } else {
                        continue;
                    }
                }
            }
        }
    }

    fn seek(&mut self, key: SeekKey<'_>, op: SeekOp, ) -> Result<CursorResult<(Option<u64>, Option<OwnedRecord>)>> {
        return_if_io!(self.moveTo(key.clone(), op.clone()));

        {
            let page = self.pageStack.top();
            return_if_locked!(page);

            let contents = page.getMutInner().pageContent.as_ref().unwrap();

            for cell_idx in 0..contents.cellCount() {
                let cell = contents.getCell(
                    cell_idx,
                    self.pager.clone(),
                    self.max_local(contents.getPageType()),
                    self.min_local(),
                    self.pageUsableSpace(),
                )?;
                match &cell {
                    BTreeCell::TableLeafCell(TableLeafCell {
                                                 _rowid: cell_rowid,
                                                 _payload: payload,
                                                 first_overflow_page: _,
                                             }) => {
                        let SeekKey::TableRowId(rowid_key) = key else {
                            unreachable!("table seek key should be a rowid");
                        };
                        let found = match op {
                            SeekOp::GT => *cell_rowid > rowid_key,
                            SeekOp::GE => *cell_rowid >= rowid_key,
                            SeekOp::EQ => *cell_rowid == rowid_key,
                        };
                        self.pageStack.advance();
                        if found {
                            let record = crate::storage::sqlite3_ondisk::read_record(payload)?;
                            return Ok(CursorResult::Ok((Some(*cell_rowid), Some(record))));
                        }
                    }
                    BTreeCell::IndexLeafCell(IndexLeafCell { payload, .. }) => {
                        let SeekKey::IndexKey(index_key) = key else {
                            unreachable!("index seek key should be a record");
                        };
                        let record = crate::storage::sqlite3_ondisk::read_record(payload)?;
                        let found = match op {
                            SeekOp::GT => record > *index_key,
                            SeekOp::GE => record >= *index_key,
                            SeekOp::EQ => record == *index_key,
                        };
                        self.pageStack.advance();
                        if found {
                            let rowid = match record.values.last() {
                                Some(OwnedValue::Integer(rowid)) => *rowid as u64,
                                _ => unreachable!("index cells should have an integer rowid"),
                            };
                            return Ok(CursorResult::Ok((Some(rowid), Some(record))));
                        }
                    }
                    cell_type => {
                        unreachable!("unexpected cell type: {:?}", cell_type);
                    }
                }
            }
        }

        // We have now iterated over all cells in the leaf page and found no match.
        let is_index = matches!(key, SeekKey::IndexKey(_));
        if is_index {
            // Unlike tables, indexes store payloads in interior cells as well. self.move_to() always moves to a leaf page, so there are cases where we need to
            // move back up to the parent interior cell and get the next record from there to perform a correct seek.
            // an example of how this can occur:
            //
            // we do an index seek for key K with cmp = SeekOp::GT, meaning we want to seek to the first key that is greater than K.
            // in self.move_to(), we encounter an interior cell with key K' = K+2, and move the left child page, which is a leaf page.
            // the reason we move to the left child page is that we know that in an index, all keys in the left child page are less than K' i.e. less than K+2,
            // meaning that the left subtree may contain a key greater than K, e.g. K+1. however, it is possible that it doesn't, in which case the correct
            // next key is K+2, which is in the parent interior cell.
            //
            // In the seek() method, once we have landed in the leaf page and find that there is no cell with a key greater than K,
            // if we were to return Ok(CursorResult::Ok((None, None))), self.record would be None, which is incorrect, because we already know
            // that there is a record with a key greater than K (K' = K+2) in the parent interior cell. Hence, we need to move back up the tree
            // and get the next matching record from there.
            return self.get_next_record(Some((key, op)));
        }

        Ok(CursorResult::Ok((None, None)))
    }

    /// 会读取rootPageId对应的page
    fn move2Root(&mut self) {
        let page = self.pager.readPage(self.rootPageId).unwrap();
        self.pageStack.clear();
        self.pageStack.push(page);
    }

    fn move2Rightmost(&mut self) -> Result<CursorResult<()>> {
        self.move2Root();

        loop {
            let mem_page = self.pageStack.top();
            let page_idx = mem_page.getMutInner().pageId;
            let page = self.pager.readPage(page_idx)?;
            return_if_locked!(page);
            let contents = page.getMutInner().pageContent.as_ref().unwrap();
            if contents.isLeaf() {
                if contents.cellCount() > 0 {
                    self.pageStack.set_cell_index(contents.cellCount() as i32 - 1);
                }
                return Ok(CursorResult::Ok(()));
            }

            match contents.rightmostPtr() {
                Some(right_most_pointer) => {
                    self.pageStack.set_cell_index(contents.cellCount() as i32 + 1);
                    let mem_page = self.pager.readPage(right_most_pointer as usize).unwrap();
                    self.pageStack.push(mem_page);
                    continue;
                }
                None => unreachable!("interior page should have a rightmost pointer"),
            }
        }
    }

    // For a table with N rows, we can find any row by row id in O(log(N)) time by starting at the root page and following the B-tree pointers.
    // B-trees consist of interior pages and leaf pages. Interior pages contain pointers to other pages, while leaf pages contain the actual row data.
    //
    // Conceptually, each Interior Cell in a interior page has a rowid and a left child node, and the page itself has a right-most child node.
    // Example: consider an interior page that contains cells C1(rowid=10), C2(rowid=20), C3(rowid=30).
    // - All rows with rowids <= 10 are in the left child node of C1.
    // - All rows with rowids > 10 and <= 20 are in the left child node of C2.
    // - All rows with rowids > 20 and <= 30 are in the left child node of C3.
    // - All rows with rowids > 30 are in the right-most child node of the page.
    //
    // There will generally be multiple levels of interior pages before we reach a leaf page,
    // so we need to follow the interior page pointers until we reach the leaf page that contains the row we are looking for (if it exists).
    //
    // Here's a high-level overview of the algorithm:
    // 1. Since we start at the root page, its cells are all interior cells.
    // 2. We scan the interior cells until we find a cell whose rowid is greater than or equal to the rowid we are looking for.
    // 3. Follow the left child pointer of the cell we found in step 2.
    //    a. In case none of the cells in the page have a rowid greater than or equal to the rowid we are looking for,
    //       we follow the right-most child pointer of the page instead (since all rows with rowids greater than the rowid we are looking for are in the right-most child node).
    // 4. We are now at a new page. If it's another interior page, we repeat the process from step 2. If it's a leaf page, we continue to step 5.
    // 5. We scan the leaf cells in the leaf page until we find the cell whose rowid is equal to the rowid we are looking for.
    //    This cell contains the actual data we are looking for.
    // 6. If we find the cell, we return the record. Otherwise, we return an empty result.
    pub fn moveTo(&mut self, seekKey: SeekKey<'_>, seekOp: SeekOp) -> Result<CursorResult<()>> {
        self.move2Root();

        loop {
            let page = self.pageStack.top();
            return_if_locked!(page);

            let pageContent = page.getMutInner().pageContent.as_ref().unwrap();
            if pageContent.isLeaf() {
                return Ok(CursorResult::Ok(()));
            }

            let mut foundCell = false;

            'a:
            for cellIndex in 0..pageContent.cellCount() {
                match &pageContent.getCell(cellIndex,
                                           self.pager.clone(),
                                           self.max_local(pageContent.getPageType()),
                                           self.min_local(),
                                           self.pageUsableSpace())? {
                    BTreeCell::TableInteriorCell(TableInteriorCell { leftChildPageIndex, rowId }) => {
                        let SeekKey::TableRowId(rowId2Seek) = seekKey else {
                            unreachable!("table seek key should be a rowid");
                        };

                        let targetLeafPageInLeftSubTree = match seekOp {
                            SeekOp::GT => rowId2Seek < *rowId,
                            SeekOp::GE | SeekOp::EQ => rowId2Seek <= *rowId,
                        };

                        self.pageStack.advance();

                        if targetLeafPageInLeftSubTree {
                            let page = self.pager.readPage(*leftChildPageIndex as usize)?;
                            self.pageStack.push(page);
                            foundCell = true;
                            break 'a;
                        }
                    }
                    BTreeCell::TableLeafCell(TableLeafCell { .. }) => unreachable!("we don't iterate leaf cells while trying to move to a leaf cell"),
                    BTreeCell::IndexInteriorCell(IndexInteriorCell { left_child_page, payload, .. }) => {
                        let SeekKey::IndexKey(index_key) = seekKey else {
                            unreachable!("index seek key should be a record");
                        };

                        let record = sqlite3_ondisk::read_record(payload)?;
                        let target_leaf_page_is_in_the_left_subtree = match seekOp {
                            SeekOp::GT => index_key < &record,
                            SeekOp::GE => index_key <= &record,
                            SeekOp::EQ => index_key <= &record,
                        };

                        if target_leaf_page_is_in_the_left_subtree {
                            // we don't advance in case of index tree internal nodes because we will visit this node going up
                            let mem_page = self.pager.readPage(*left_child_page as usize).unwrap();
                            self.pageStack.push(mem_page);
                            foundCell = true;
                            break 'a;
                        } else {
                            self.pageStack.advance();
                        }
                    }
                    BTreeCell::IndexLeafCell(_) => unreachable!("we don't iterate leaf cells while trying to move to a leaf cell"),
                }
            }

            if !foundCell {
                match pageContent.rightmostPtr() {
                    Some(right_most_pointer) => {
                        self.pageStack.advance();
                        let mem_page = self.pager.readPage(right_most_pointer as usize)?;
                        self.pageStack.push(mem_page);
                    }
                    None => unreachable!("we shall not go back up! The only way is down the slope"),
                }
            }
        }
    }

    fn insertIntoPage(&mut self, key: &OwnedValue, rec: &OwnedRecord) -> Result<CursorResult<()>> {
        loop {
            let state = &self.writeInfo.writeState;
            match state {
                WriteState::Start => {
                    let page = self.pageStack.top();
                    let int_key = match key {
                        OwnedValue::Integer(i) => *i as u64,
                        _ => unreachable!("btree tables are indexed by integers!"),
                    };

                    // get page and find cell
                    let (cell_idx, page_type) = {
                        return_if_locked!(page);

                        page.set_dirty();
                        self.pager.addDirtyPageId(page.getMutInner().pageId);

                        let page = page.getMutInner().pageContent.as_mut().unwrap();
                        assert!(matches!(page.getPageType(), PageType::TableLeaf));

                        // find cell
                        (self.find_cell(page, int_key), page.getPageType())
                    };

                    // TODO: if overwrite drop cell

                    // insert cell
                    let mut cell_payload: Vec<u8> = Vec::new();
                    self.fill_cell_payload(page_type, Some(int_key), &mut cell_payload, rec);

                    // insert
                    let overflow = {
                        let contents = page.getMutInner().pageContent.as_mut().unwrap();
                        self.insert_into_cell(contents, cell_payload.as_slice(), cell_idx);
                        contents.overflowCells.len()
                    };

                    if overflow > 0 {
                        self.writeInfo.writeState = WriteState::BalanceStart;
                    } else {
                        self.writeInfo.writeState = WriteState::Finish;
                    }
                }
                WriteState::BalanceStart | WriteState::BalanceMoveUp | WriteState::BalanceGetParentPage => return_if_io!(self.balance_leaf()),
                WriteState::Finish => {
                    self.writeInfo.writeState = WriteState::Start;
                    return Ok(CursorResult::Ok(()));
                }
            };
        }
    }

    /* insert to position and shift other pointers */
    fn insert_into_cell(&self, page: &mut PageContent, payload: &[u8], cell_idx: usize) {
        let free = self.compute_free_space(page, RefCell::borrow(&self.dbHeader));
        let enough_space = payload.len() + 2 <= free as usize;
        if !enough_space {
            // add to overflow cell
            page.overflowCells.push(OverflowCell {
                index: cell_idx,
                payload: Pin::new(Vec::from(payload)),
            });
            return;
        }

        // TODO: insert into cell payload in internal page
        let pc = self.allocate_cell_space(page, payload.len() as u16);
        let buf = page.as_ptr();

        // copy data
        buf[pc as usize..pc as usize + payload.len()].copy_from_slice(payload);
        //  memmove(pIns+2, pIns, 2*(pPage->nCell - i));
        let (pointer_area_pc_by_idx, _) = page.cell_get_raw_pointer_region();
        let pointer_area_pc_by_idx = pointer_area_pc_by_idx + (2 * cell_idx);

        // move previous pointers forward and insert new pointer there
        let n_cells_forward = 2 * (page.cellCount() - cell_idx);
        if n_cells_forward > 0 {
            buf.copy_within(
                pointer_area_pc_by_idx..pointer_area_pc_by_idx + n_cells_forward,
                pointer_area_pc_by_idx + 2,
            );
        }
        page.write_u16(pointer_area_pc_by_idx - page.offset, pc);

        // update first byte of content area
        page.write_u16(BTREE_HEADER_OFFSET_CELL_CONTENT, pc);

        // update cell count
        let new_n_cells = (page.cellCount() + 1) as u16;
        page.write_u16(BTREE_HEADER_OFFSET_CELL_COUNT, new_n_cells);
    }

    fn free_cell_range(&self, page: &mut PageContent, offset: u16, len: u16) {
        if page.first_freeblock() == 0 {
            // insert into empty list
            page.write_u16(offset as usize, 0);
            page.write_u16(offset as usize + 2, len);
            page.write_u16(BTREE_HEADER_OFFSET_FREE_BLOCK, offset);
            return;
        }
        let first_block = page.first_freeblock();

        if offset < first_block {
            // insert into head of list
            page.write_u16(offset as usize, first_block);
            page.write_u16(offset as usize + 2, len);
            page.write_u16(BTREE_HEADER_OFFSET_FREE_BLOCK, offset);
            return;
        }

        if offset <= page.cell_content_area() {
            // extend boundary of content area
            page.write_u16(BTREE_HEADER_OFFSET_FREE_BLOCK, page.first_freeblock());
            page.write_u16(BTREE_HEADER_OFFSET_CELL_CONTENT, offset + len);
            return;
        }

        let maxpc = {
            let db_header = self.dbHeader.borrow();
            let usable_space = (db_header.pageSize - db_header.pageUnusedSpace as u16) as usize;
            usable_space as u16
        };

        let mut pc = first_block;
        let mut prev = first_block;

        while pc <= maxpc && pc < offset {
            let next = page.read_u16(pc as usize);
            prev = pc;
            pc = next;
        }

        if pc >= maxpc {
            // insert into tail
            let offset = offset as usize;
            let prev = prev as usize;
            page.write_u16(prev, offset as u16);
            page.write_u16(offset, 0);
            page.write_u16(offset + 2, len);
        } else {
            // insert in between
            let next = page.read_u16(pc as usize);
            let offset = offset as usize;
            let prev = prev as usize;
            page.write_u16(prev, offset as u16);
            page.write_u16(offset, next);
            page.write_u16(offset + 2, len);
        }
    }

    fn drop_cell(&self, page: &mut PageContent, cell_idx: usize) {
        let (cell_start, cell_len) = page.cell_get_raw_region(
            cell_idx,
            self.max_local(page.getPageType()),
            self.min_local(),
            self.pageUsableSpace(),
        );
        self.free_cell_range(page, cell_start as u16, cell_len as u16);
        page.write_u16(BTREE_HEADER_OFFSET_CELL_COUNT, page.cellCount() as u16 - 1);
    }

    /// This is a naive algorithm that doesn't try to distribute cells evenly by content.
    /// It will try to split the page in half by keys not by content.
    /// Sqlite tries to have a page at least 40% full.
    fn balance_leaf(&mut self) -> Result<CursorResult<()>> {
        let state = &self.writeInfo.writeState;
        match state {
            WriteState::BalanceStart => {
                // drop divider cells and find right pointer
                // NOTE: since we are doing a simple split we only finding the pointer we want to update (right pointer).
                // Right pointer means cell that points to the last page, as we don't really want to drop this one. This one
                // can be a "rightmost pointer" or a "cell".
                // we always asumme there is a parent
                let current_page = self.pageStack.top();
                {
                    // check if we don't need to balance
                    // don't continue if there are no overflow cells
                    let page = current_page.getMutInner().pageContent.as_mut().unwrap();
                    if page.overflowCells.is_empty() {
                        self.writeInfo.writeState = WriteState::Finish;
                        return Ok(CursorResult::Ok(()));
                    }
                }

                if !self.pageStack.has_parent() {
                    self.balance_root();
                    return Ok(CursorResult::Ok(()));
                }
                debug!("Balancing leaf. leaf={}", current_page.getMutInner().pageId);

                // Copy of page used to reference cell bytes.
                // This needs to be saved somewhere safe so taht references still point to here,
                // this will be store in write_info below
                let page_copy = current_page.getMutInner().pageContent.as_ref().unwrap().clone();

                // In memory in order copy of all cells in pages we want to balance. For now let's do a 2 page split.
                // Right pointer in interior cells should be converted to regular cells if more than 2 pages are used for balancing.
                let mut scratch_cells = self.writeInfo.scratch_cells.borrow_mut();
                scratch_cells.clear();

                for cell_idx in 0..page_copy.cellCount() {
                    let (start, len) = page_copy.cell_get_raw_region(
                        cell_idx,
                        self.max_local(page_copy.getPageType()),
                        self.min_local(),
                        self.pageUsableSpace(),
                    );
                    let buf = page_copy.as_ptr();
                    scratch_cells.push(to_static_buf(&buf[start..start + len]));
                }
                for overflow_cell in &page_copy.overflowCells {
                    scratch_cells
                        .insert(overflow_cell.index, to_static_buf(&overflow_cell.payload));
                }
                *self.writeInfo.rightmost_pointer.borrow_mut() = page_copy.rightmostPtr();

                self.writeInfo.page_copy.replace(Some(page_copy));

                // allocate new pages and move cells to those new pages
                // split procedure
                let page = current_page.getMutInner().pageContent.as_mut().unwrap();
                assert!(
                    matches!(
                        page.getPageType(),
                        PageType::TableLeaf | PageType::TableInterior
                    ),
                    "indexes still not supported "
                );

                let right_page = self.allocate_page(page.getPageType(), 0);
                let right_page_id = right_page.getMutInner().pageId;

                self.writeInfo.new_pages.borrow_mut().clear();
                self.writeInfo
                    .new_pages
                    .borrow_mut()
                    .push(current_page.clone());
                self.writeInfo
                    .new_pages
                    .borrow_mut()
                    .push(right_page.clone());

                debug!(
                    "splitting left={} right={}",
                    current_page.getMutInner().pageId,
                    right_page_id
                );

                self.writeInfo.writeState = WriteState::BalanceGetParentPage;
                Ok(CursorResult::Ok(()))
            }
            WriteState::BalanceGetParentPage => {
                let parent = self.pageStack.parent();
                let loaded = parent.is_loaded();
                return_if_locked!(parent);

                if !loaded {
                    debug!("balance_leaf(loading page)");
                    self.pager.load_page(parent.clone())?;
                    return Ok(CursorResult::IO);
                }
                parent.set_dirty();
                self.writeInfo.writeState = WriteState::BalanceMoveUp;
                Ok(CursorResult::Ok(()))
            }
            WriteState::BalanceMoveUp => {
                let parent = self.pageStack.parent();

                let (page_type, current_idx) = {
                    let current_page = self.pageStack.top();
                    let contents = current_page.getMutInner().pageContent.as_ref().unwrap();
                    (contents.getPageType().clone(), current_page.getMutInner().pageId)
                };

                parent.set_dirty();
                self.pager.addDirtyPageId(parent.getMutInner().pageId);
                let parent_contents = parent.getMutInner().pageContent.as_mut().unwrap();
                // if this isn't empty next loop won't work
                assert_eq!(parent_contents.overflowCells.len(), 0);

                // Right page pointer is u32 in right most pointer, and in cell is u32 too, so we can use a *u32 to hold where we want to change this value
                let mut right_pointer = BTREE_HEADER_OFFSET_RIGHTMOST;
                for cell_idx in 0..parent_contents.cellCount() {
                    let cell = parent_contents
                        .getCell(
                            cell_idx,
                            self.pager.clone(),
                            self.max_local(page_type.clone()),
                            self.min_local(),
                            self.pageUsableSpace(),
                        )
                        .unwrap();
                    let found = match cell {
                        BTreeCell::TableInteriorCell(interior) => {
                            interior.leftChildPageIndex as usize == current_idx
                        }
                        _ => unreachable!("Parent should always be a "),
                    };
                    if found {
                        let (start, _len) = parent_contents.cell_get_raw_region(
                            cell_idx,
                            self.max_local(page_type.clone()),
                            self.min_local(),
                            self.pageUsableSpace(),
                        );
                        right_pointer = start;
                        break;
                    }
                }

                let mut new_pages = self.writeInfo.new_pages.borrow_mut();
                let scratch_cells = self.writeInfo.scratch_cells.borrow();

                // reset pages
                for page in new_pages.iter() {
                    assert!(page.is_dirty());
                    let contents = page.getMutInner().pageContent.as_mut().unwrap();

                    contents.write_u16(BTREE_HEADER_OFFSET_FREE_BLOCK, 0);
                    contents.write_u16(BTREE_HEADER_OFFSET_CELL_COUNT, 0);

                    let db_header = RefCell::borrow(&self.dbHeader);
                    let cell_content_area_start =
                        db_header.pageSize - db_header.pageUnusedSpace as u16;
                    contents.write_u16(BTREE_HEADER_OFFSET_CELL_CONTENT, cell_content_area_start);

                    contents.write_u8(BTREE_HEADER_OFFSET_FRAGMENTED, 0);
                    if !contents.isLeaf() {
                        contents.write_u32(BTREE_HEADER_OFFSET_RIGHTMOST, 0);
                    }
                }

                // distribute cells
                let new_pages_len = new_pages.len();
                let cells_per_page = scratch_cells.len() / new_pages.len();
                let mut current_cell_index = 0_usize;
                let mut divider_cells_index = Vec::new(); /* index to scratch cells that will be used as dividers in order */

                debug!(
                    "balance_leaf::distribute(cells={}, cells_per_page={})",
                    scratch_cells.len(),
                    cells_per_page
                );

                for (i, page) in new_pages.iter_mut().enumerate() {
                    let page_id = page.getMutInner().pageId;
                    let contents = page.getMutInner().pageContent.as_mut().unwrap();

                    let last_page = i == new_pages_len - 1;
                    let cells_to_copy = if last_page {
                        // last cells is remaining pages if division was odd
                        scratch_cells.len() - current_cell_index
                    } else {
                        cells_per_page
                    };
                    debug!(
                        "balance_leaf::distribute(page={}, cells_to_copy={})",
                        page_id, cells_to_copy
                    );

                    let cell_index_range = current_cell_index..current_cell_index + cells_to_copy;
                    for (j, cell_idx) in cell_index_range.enumerate() {
                        debug!("balance_leaf::distribute_in_page(page={}, cells_to_copy={}, j={}, cell_idx={})", page_id, cells_to_copy, j, cell_idx);

                        let cell = scratch_cells[cell_idx];
                        self.insert_into_cell(contents, cell, j);
                    }
                    divider_cells_index.push(current_cell_index + cells_to_copy - 1);
                    current_cell_index += cells_to_copy;
                }
                let is_leaf = {
                    let page = self.pageStack.top();
                    let page = page.getMutInner().pageContent.as_ref().unwrap();
                    page.isLeaf()
                };

                // update rightmost pointer for each page if we are in interior page
                if !is_leaf {
                    for page in new_pages.iter_mut().take(new_pages_len - 1) {
                        let contents = page.getMutInner().pageContent.as_mut().unwrap();

                        assert_eq!(contents.cellCount(), 1);

                        let last_cell =
                            contents.getCell(contents.cellCount() - 1,
                                             self.pager.clone(),
                                             self.max_local(contents.getPageType()),
                                             self.min_local(),
                                             self.pageUsableSpace())?;

                        let last_cell_pointer = match last_cell {
                            BTreeCell::TableInteriorCell(interior) => interior.leftChildPageIndex,
                            _ => unreachable!(),
                        };

                        self.drop_cell(contents, contents.cellCount() - 1);
                        contents.write_u32(BTREE_HEADER_OFFSET_RIGHTMOST, last_cell_pointer);
                    }

                    // last page right most pointer points to previous right most pointer before splitting
                    let last_page = new_pages.last().unwrap();
                    let last_page_contents = last_page.getMutInner().pageContent.as_mut().unwrap();
                    last_page_contents.write_u32(
                        BTREE_HEADER_OFFSET_RIGHTMOST,
                        self.writeInfo.rightmost_pointer.borrow().unwrap(),
                    );
                }

                // insert dividers in parent
                // we can consider dividers the first cell of each page starting from the second page
                for (page_id_index, page) in
                    new_pages.iter_mut().take(new_pages_len - 1).enumerate()
                {
                    let contents = page.getMutInner().pageContent.as_mut().unwrap();
                    let divider_cell_index = divider_cells_index[page_id_index];
                    let cell_payload = scratch_cells[divider_cell_index];
                    let cell = readBtreeCell(
                        cell_payload,
                        &contents.getPageType(),
                        0,
                        self.pager.clone(),
                        self.max_local(contents.getPageType()),
                        self.min_local(),
                        self.pageUsableSpace(),
                    ).unwrap();

                    if is_leaf {
                        // create a new divider cell and push
                        let key = match cell {
                            BTreeCell::TableLeafCell(leaf) => leaf._rowid,
                            _ => unreachable!(),
                        };
                        let mut divider_cell = Vec::new();
                        divider_cell.extend_from_slice(&(page.getMutInner().pageId as u32).to_be_bytes());
                        divider_cell.extend(std::iter::repeat(0).take(9));
                        let n = write_varint(&mut divider_cell.as_mut_slice()[4..], key);
                        divider_cell.truncate(4 + n);
                        let parent_cell_idx = self.find_cell(parent_contents, key);
                        self.insert_into_cell(
                            parent_contents,
                            divider_cell.as_slice(),
                            parent_cell_idx,
                        );
                    } else {
                        // move cell
                        let key = match cell {
                            BTreeCell::TableInteriorCell(interior) => interior.rowId,
                            _ => unreachable!(),
                        };
                        let parent_cell_idx = self.find_cell(contents, key);
                        self.insert_into_cell(parent_contents, cell_payload, parent_cell_idx);
                        // self.drop_cell(*page, 0);
                    }
                }

                {
                    // copy last page id to right pointer
                    let last_pointer = new_pages.last().unwrap().getMutInner().pageId as u32;
                    parent_contents.write_u32(right_pointer, last_pointer);
                }
                self.pageStack.pop();
                self.writeInfo.writeState = WriteState::BalanceStart;
                let _ = self.writeInfo.page_copy.take();
                Ok(CursorResult::Ok(()))
            }

            _ => unreachable!("invalid balance leaf state {:?}", state),
        }
    }

    fn balance_root(&mut self) {
        /* todo: balance deeper, create child and copy contents of root there. Then split root */
        /* if we are in root page then we just need to create a new root and push key there */

        let is_page_1 = {
            let current_root = self.pageStack.top();
            current_root.getMutInner().pageId == 1
        };

        let offset = if is_page_1 { DATABASE_HEADER_SIZE } else { 0 };
        let new_root_page = self.allocate_page(PageType::TableInterior, offset);
        {
            let current_root = self.pageStack.top();
            let current_root_contents = current_root.getMutInner().pageContent.as_ref().unwrap();

            let new_root_page_id = new_root_page.getMutInner().pageId;
            let new_root_page_contents = new_root_page.getMutInner().pageContent.as_mut().unwrap();
            if is_page_1 {
                // Copy header
                let current_root_buf = current_root_contents.as_ptr();
                let new_root_buf = new_root_page_contents.as_ptr();
                new_root_buf[0..DATABASE_HEADER_SIZE]
                    .copy_from_slice(&current_root_buf[0..DATABASE_HEADER_SIZE]);
            }
            // point new root right child to previous root
            new_root_page_contents
                .write_u32(BTREE_HEADER_OFFSET_RIGHTMOST, new_root_page_id as u32);
            new_root_page_contents.write_u16(BTREE_HEADER_OFFSET_CELL_COUNT, 0);
        }

        /* swap splitted page buffer with new root buffer so we don't have to update page idx */
        {
            let (root_id, child_id, child) = {
                let page_ref = self.pageStack.top();
                let child = page_ref.clone();

                // Swap the entire Page structs
                std::mem::swap(&mut child.getMutInner().pageId, &mut new_root_page.getMutInner().pageId);
                // TODO:: shift bytes by offset to left on child because now child has offset 100
                // and header bytes
                // Also change the offset of page
                //
                if is_page_1 {
                    // Remove header from child and set offset to 0
                    let contents = child.getMutInner().pageContent.as_mut().unwrap();
                    let (cell_pointer_offset, _) = contents.cell_get_raw_pointer_region();
                    // change cell pointers
                    for cell_idx in 0..contents.cellCount() {
                        let cell_pointer_offset = cell_pointer_offset + (2 * cell_idx) - offset;
                        let pc = contents.read_u16(cell_pointer_offset);
                        contents.write_u16(cell_pointer_offset, pc - offset as u16);
                    }

                    contents.offset = 0;
                    let buf = contents.as_ptr();
                    buf.copy_within(DATABASE_HEADER_SIZE.., 0);
                }

                self.pager.addDirtyPageId(new_root_page.getMutInner().pageId);
                self.pager.addDirtyPageId(child.getMutInner().pageId);
                (new_root_page.getMutInner().pageId, child.getMutInner().pageId, child)
            };

            debug!("Balancing root. root={}, rightmost={}", root_id, child_id);
            let root = new_root_page.clone();

            self.rootPageId = root_id;
            self.pageStack.clear();
            self.pageStack.push(root.clone());
            self.pageStack.push(child.clone());

            self.pager.put_loaded_page(root_id, root);
            self.pager.put_loaded_page(child_id, child);
        }
    }

    fn allocate_page(&self, page_type: PageType, offset: usize) -> PageArc {
        let page = self.pager.allocate_page().unwrap();
        btreeInitPage(&page, page_type, &self.dbHeader.borrow(), offset);
        page
    }

    fn allocate_overflow_page(&self) -> PageArc {
        let page = self.pager.allocate_page().unwrap();

        // setup overflow page
        let contents = page.getMutInner().pageContent.as_mut().unwrap();
        let buf = contents.as_ptr();
        buf.fill(0);

        page
    }

    /*
        Allocate space for a cell on a page.
    */
    fn allocate_cell_space(&self, page_ref: &PageContent, amount: u16) -> u16 {
        let amount = amount as usize;

        let (cell_offset, _) = page_ref.cell_get_raw_pointer_region();
        let gap = cell_offset + 2 * page_ref.cellCount();
        let mut top = page_ref.cell_content_area() as usize;

        // there are free blocks and enough space
        if page_ref.first_freeblock() != 0 && gap + 2 <= top {
            // find slot
            let db_header = RefCell::borrow(&self.dbHeader);
            let pc = find_free_cell(page_ref, db_header, amount);
            if pc != 0 {
                return pc as u16;
            }
            /* fall through, we might need to defragment */
        }

        if gap + 2 + amount > top {
            // defragment
            self.defragment_page(page_ref, RefCell::borrow(&self.dbHeader));
            top = page_ref.read_u16(BTREE_HEADER_OFFSET_CELL_CONTENT) as usize;
        }

        let db_header = RefCell::borrow(&self.dbHeader);
        top -= amount;

        page_ref.write_u16(BTREE_HEADER_OFFSET_CELL_CONTENT, top as u16);

        let usable_space = (db_header.pageSize - db_header.pageUnusedSpace as u16) as usize;
        assert!(top + amount <= usable_space);
        top as u16
    }

    fn defragment_page(&self, page: &PageContent, db_header: Ref<DbHeader>) {
        log::debug!("defragment_page");
        let cloned_page = page.clone();
        // TODO(pere): usable space should include offset probably
        let usable_space = (db_header.pageSize - db_header.pageUnusedSpace as u16) as u64;
        let mut cbrk = usable_space;

        // TODO: implement fast algorithm

        let last_cell = usable_space - 4;
        let first_cell = {
            let (start, end) = cloned_page.cell_get_raw_pointer_region();
            start + end
        };

        if cloned_page.cellCount() > 0 {
            let page_type = page.getPageType();
            let read_buf = cloned_page.as_ptr();
            let write_buf = page.as_ptr();

            for i in 0..cloned_page.cellCount() {
                let cell_offset = page.offset + 8;
                let cell_idx = cell_offset + i * 2;

                let pc = u16::from_be_bytes([read_buf[cell_idx], read_buf[cell_idx + 1]]) as u64;
                if pc > last_cell {
                    unimplemented!("corrupted page");
                }

                assert!(pc <= last_cell);

                let size = match page_type {
                    PageType::TableInterior => {
                        let (_, nr_key) = match readVarInt(&read_buf[pc as usize..]) {
                            Ok(v) => v,
                            Err(_) => todo!(
                                "error while parsing varint from cell, probably treat this as corruption?"
                            ),
                        };
                        4 + nr_key as u64
                    }
                    PageType::TableLeaf => {
                        let (payload_size, nr_payload) = match readVarInt(&read_buf[pc as usize..]) {
                            Ok(v) => v,
                            Err(_) => todo!(
                                "error while parsing varint from cell, probably treat this as corruption?"
                            ),
                        };
                        let (_, nr_key) = match readVarInt(&read_buf[pc as usize + nr_payload..]) {
                            Ok(v) => v,
                            Err(_) => todo!(
                                "error while parsing varint from cell, probably treat this as corruption?"
                            ),
                        };
                        // TODO: add overflow page calculation
                        payload_size + nr_payload as u64 + nr_key as u64
                    }
                    PageType::IndexInterior => todo!(),
                    PageType::IndexLeaf => todo!(),
                };
                cbrk -= size;
                if cbrk < first_cell as u64 || pc + size > usable_space {
                    todo!("corrupt");
                }
                assert!(cbrk + size <= usable_space && cbrk >= first_cell as u64);
                // set new pointer
                write_buf[cell_idx..cell_idx + 2].copy_from_slice(&(cbrk as u16).to_be_bytes());
                // copy payload
                write_buf[cbrk as usize..cbrk as usize + size as usize]
                    .copy_from_slice(&read_buf[pc as usize..pc as usize + size as usize]);
            }
        }

        // assert!( nfree >= 0 );
        // if( data[hdr+7]+cbrk-iCellFirst!=pPage->nFree ){
        //   return SQLITE_CORRUPT_PAGE(pPage);
        // }
        assert!(cbrk >= first_cell as u64);
        let write_buf = page.as_ptr();

        // set new first byte of cell content
        page.write_u16(BTREE_HEADER_OFFSET_CELL_CONTENT, cbrk as u16);
        // set free block to 0, unused spaced can be retrieved from gap between cell pointer end and content start
        page.write_u16(BTREE_HEADER_OFFSET_FREE_BLOCK, 0);
        // set unused space to 0
        let first_cell = cloned_page.cell_content_area() as u64;
        assert!(first_cell <= cbrk);
        write_buf[first_cell as usize..cbrk as usize].fill(0);
    }

    // Free blocks can be zero, meaning the "real free space" that can be used to allocate is expected to be between first cell byte
    // and end of cell pointer area.
    #[allow(unused_assignments)]
    fn compute_free_space(&self, page: &PageContent, db_header: Ref<DbHeader>) -> u16 {
        // TODO(pere): maybe free space is not calculated correctly with offset
        let buf = page.as_ptr();

        let usable_space = (db_header.pageSize - db_header.pageUnusedSpace as u16) as usize;
        let mut first_byte_in_cell_content = page.cell_content_area();
        if first_byte_in_cell_content == 0 {
            first_byte_in_cell_content = u16::MAX;
        }

        let fragmented_free_bytes = page.num_frag_free_bytes();
        let free_block_pointer = page.first_freeblock();
        let ncell = page.cellCount();

        // 8 + 4 == header end
        let child_pointer_size = if page.isLeaf() { 0 } else { 4 };
        let first_cell = (page.offset + 8 + child_pointer_size + (2 * ncell)) as u16;

        let mut nfree = fragmented_free_bytes as usize + first_byte_in_cell_content as usize;

        let mut pc = free_block_pointer as usize;
        if pc > 0 {
            if pc < first_byte_in_cell_content as usize {
                // corrupt
                todo!("corrupted page");
            }

            let mut next = 0;
            let mut size = 0;
            loop {
                // TODO: check corruption icellast
                next = u16::from_be_bytes(buf[pc..pc + 2].try_into().unwrap()) as usize;
                size = u16::from_be_bytes(buf[pc + 2..pc + 4].try_into().unwrap()) as usize;
                nfree += size;
                if next <= pc + size + 3 {
                    break;
                }
                pc = next;
            }

            if next > 0 {
                todo!("corrupted page ascending order");
            }

            if pc + size > usable_space {
                todo!("corrupted page last freeblock extends last page end");
            }
        }

        // if( nFree>usableSize || nFree<iCellFirst ){
        //   return SQLITE_CORRUPT_PAGE(pPage);
        // }
        // don't count header and cell pointers?
        nfree -= first_cell as usize;
        nfree as u16
    }

    fn fill_cell_payload(
        &self,
        page_type: PageType,
        int_key: Option<u64>,
        cell_payload: &mut Vec<u8>,
        record: &OwnedRecord,
    ) {
        assert!(matches!(
            page_type,
            PageType::TableLeaf | PageType::IndexLeaf
        ));
        // TODO: make record raw from start, having to serialize is not good
        let mut record_buf = Vec::new();
        record.serialize(&mut record_buf);

        // fill in header
        if matches!(page_type, PageType::TableLeaf) {
            let int_key = int_key.unwrap();
            write_varint_to_vec(record_buf.len() as u64, cell_payload);
            write_varint_to_vec(int_key, cell_payload);
        } else {
            write_varint_to_vec(record_buf.len() as u64, cell_payload);
        }

        let max_local = self.max_local(page_type.clone());
        log::debug!(
            "fill_cell_payload(record_size={}, max_local={})",
            record_buf.len(),
            max_local
        );
        if record_buf.len() <= max_local {
            // enough allowed space to fit inside a btree page
            cell_payload.extend_from_slice(record_buf.as_slice());
            cell_payload.resize(cell_payload.len() + 4, 0);
            return;
        }
        log::debug!("fill_cell_payload(overflow)");

        let min_local = self.min_local();
        let mut space_left = min_local + (record_buf.len() - min_local) % (self.pageUsableSpace() - 4);

        if space_left > max_local {
            space_left = min_local;
        }

        // cell_size must be equal to first value of space_left as this will be the bytes copied to non-overflow page.
        let cell_size = space_left + cell_payload.len() + 4; // 4 is the number of bytes of pointer to first overflow page
        let mut to_copy_buffer = record_buf.as_slice();

        let prev_size = cell_payload.len();
        cell_payload.resize(prev_size + space_left + 4, 0);
        let mut pointer = unsafe { cell_payload.as_mut_ptr().add(prev_size) };
        let mut pointer_to_next = unsafe { cell_payload.as_mut_ptr().add(prev_size + space_left) };
        let mut overflow_pages = Vec::new();

        loop {
            let to_copy = space_left.min(to_copy_buffer.len());
            unsafe { std::ptr::copy(to_copy_buffer.as_ptr(), pointer, to_copy) };

            let left = to_copy_buffer.len() - to_copy;
            if left == 0 {
                break;
            }

            // we still have bytes to add, we will need to allocate new overflow page
            let overflow_page = self.allocate_overflow_page();
            overflow_pages.push(overflow_page.clone());
            {
                let id = overflow_page.getMutInner().pageId as u32;
                let contents = overflow_page.getMutInner().pageContent.as_mut().unwrap();

                // TODO: take into account offset here?
                let buf = contents.as_ptr();
                let as_bytes = id.to_be_bytes();
                // update pointer to new overflow page
                unsafe { std::ptr::copy(as_bytes.as_ptr(), pointer_to_next, 4) };

                pointer = unsafe { buf.as_mut_ptr().add(4) };
                pointer_to_next = buf.as_mut_ptr();
                space_left = self.pageUsableSpace() - 4;
            }

            to_copy_buffer = &to_copy_buffer[to_copy..];
        }

        assert_eq!(cell_size, cell_payload.len());
    }

    fn max_local(&self, page_type: PageType) -> usize {
        let pageUsableSpace = self.pageUsableSpace();
        match page_type {
            PageType::IndexInterior | PageType::TableInterior => (pageUsableSpace - 12) * 64 / 255 - 23,
            PageType::IndexLeaf | PageType::TableLeaf => pageUsableSpace - 35,
        }
    }

    fn min_local(&self) -> usize {
        let pageUsableSpace = self.pageUsableSpace();
        (pageUsableSpace - 12) * 32 / 255 - 23
    }

    fn pageUsableSpace(&self) -> usize {
        let dbHeader = RefCell::borrow(&self.dbHeader);
        (dbHeader.pageSize - dbHeader.pageUnusedSpace as u16) as usize
    }

    fn find_cell(&self, page: &PageContent, int_key: u64) -> usize {
        let mut cell_idx = 0;
        let cell_count = page.cellCount();
        while cell_idx < cell_count {
            match page
                .getCell(
                    cell_idx,
                    self.pager.clone(),
                    self.max_local(page.getPageType()),
                    self.min_local(),
                    self.pageUsableSpace(),
                )
                .unwrap()
            {
                BTreeCell::TableLeafCell(cell) => {
                    if int_key <= cell._rowid {
                        break;
                    }
                }
                BTreeCell::TableInteriorCell(cell) => {
                    if int_key <= cell.rowId {
                        break;
                    }
                }
                _ => todo!(),
            }
            cell_idx += 1;
        }
        cell_idx
    }
}

/// Stack of pages representing the tree traversal order.
/// current_page represents the current page being used in the tree and current_page - 1 would be
/// the parent. Using current_page + 1 or higher is undefined behaviour.
struct PageStack {
    /// Pointer to the current page being consumed
    curPageIndexInStack: RefCell<i32>,

    /// List of pages in the stack. Root page will be in index 0
    pageStack: RefCell<[Option<PageArc>; BT_CURSOR_MAX_DEPTH + 1]>,

    /// List of cell indices in the stack.
    /// cell_indices[current_page] is the current cell index being consumed. Similarly
    /// cell_indices[current_page-1] is the cell index of the parent of the current page
    /// that we save in case of going back up.
    /// There are two points that need special attention:
    ///  If cell_indices[current_page] = -1, it indicates that the current iteration has reached the start of the current_page
    ///  If cell_indices[current_page] = `cell_count`, it means that the current iteration has reached the end of the current_page
    cell_indices: RefCell<[i32; BT_CURSOR_MAX_DEPTH + 1]>,
}

impl PageStack {
    fn push(&self, page: PageArc) {
        *self.curPageIndexInStack.borrow_mut() += 1;
        let current = *self.curPageIndexInStack.borrow();
        assert!(current < BT_CURSOR_MAX_DEPTH as i32, "corrupted database, stack is bigger than expected");
        self.pageStack.borrow_mut()[current as usize] = Some(page);
        self.cell_indices.borrow_mut()[current as usize] = 0;
    }

    fn pop(&self) {
        let current = *self.curPageIndexInStack.borrow();
        debug!("pagestack::pop(current={})", current);
        self.cell_indices.borrow_mut()[current as usize] = 0;
        self.pageStack.borrow_mut()[current as usize] = None;
        *self.curPageIndexInStack.borrow_mut() -= 1;
    }

    fn top(&self) -> PageArc {
        let current = *self.curPageIndexInStack.borrow();
        self.pageStack.borrow()[current as usize].as_ref().unwrap().clone()
    }

    fn parent(&self) -> PageArc {
        let current = *self.curPageIndexInStack.borrow();
        self.pageStack.borrow()[current as usize - 1].as_ref().unwrap().clone()
    }

    fn current(&self) -> usize {
        *self.curPageIndexInStack.borrow() as usize
    }

    /// Cell index of the current page
    fn current_index(&self) -> i32 {
        let current = self.current();
        self.cell_indices.borrow()[current]
    }

    fn curr_idx_out_of_begin(&self) -> bool {
        let cell_idx = self.current_index();
        cell_idx < 0
    }

    /// Advance the current cell index of the current page to the next cell.
    fn advance(&self) {
        let current = self.current();
        self.cell_indices.borrow_mut()[current] += 1;
    }

    fn retreat(&self) {
        let current = self.current();
        self.cell_indices.borrow_mut()[current] -= 1;
    }

    fn set_cell_index(&self, idx: i32) {
        let current = self.current();
        self.cell_indices.borrow_mut()[current] = idx
    }

    fn has_parent(&self) -> bool {
        *self.curPageIndexInStack.borrow() > 0
    }

    fn clear(&self) {
        *self.curPageIndexInStack.borrow_mut() = -1;
    }
}

struct WriteInfo {
    writeState: WriteState,
    new_pages: RefCell<Vec<PageArc>>,
    scratch_cells: RefCell<Vec<&'static [u8]>>,
    rightmost_pointer: RefCell<Option<u32>>,
    page_copy: RefCell<Option<PageContent>>, // this holds the copy a of a page needed for buffer references
}

#[derive(Debug)]
enum WriteState {
    Start,
    BalanceStart,
    BalanceGetParentPage,
    BalanceMoveUp,
    Finish,
}

fn find_free_cell(page_ref: &PageContent, db_header: Ref<DbHeader>, amount: usize) -> usize {
    // NOTE: freelist is in ascending order of keys and pc
    // unuse_space is reserved bytes at the end of page, therefore we must substract from maxpc
    let mut pc = page_ref.first_freeblock() as usize;

    let buf = page_ref.as_ptr();

    let usable_space = (db_header.pageSize - db_header.pageUnusedSpace as u16) as usize;
    let maxpc = usable_space - amount;
    let mut found = false;
    while pc <= maxpc {
        let next = u16::from_be_bytes(buf[pc..pc + 2].try_into().unwrap());
        let size = u16::from_be_bytes(buf[pc + 2..pc + 4].try_into().unwrap());
        if amount <= size as usize {
            found = true;
            break;
        }
        pc = next as usize;
    }
    if !found {
        0
    } else {
        pc
    }
}

/// setup btree page
pub fn btreeInitPage(page: &PageArc,
                     pageType: PageType,
                     dbHeader: &DbHeader,
                     offset: usize) {
    let pageInner = page.getMutInner();
    let pageContent = pageInner.pageContent.as_mut().unwrap();

    pageContent.offset = offset;
    pageContent.write_u8(BTREE_HEADER_OFFSET_TYPE, pageType as u8);
    pageContent.write_u16(BTREE_HEADER_OFFSET_FREE_BLOCK, 0);
    pageContent.write_u16(BTREE_HEADER_OFFSET_CELL_COUNT, 0);

    /// page的cell的data是在page的尾部写的
    let cellContentAreaStartPos = dbHeader.pageSize - dbHeader.pageUnusedSpace as u16;
    pageContent.write_u16(BTREE_HEADER_OFFSET_CELL_CONTENT, cellContentAreaStartPos);

    pageContent.write_u8(BTREE_HEADER_OFFSET_FRAGMENTED, 0);
    pageContent.write_u32(BTREE_HEADER_OFFSET_RIGHTMOST, 0);
}

fn to_static_buf(buf: &[u8]) -> &'static [u8] {
    unsafe { std::mem::transmute::<&[u8], &'static [u8]>(buf) }
}