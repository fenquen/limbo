use log::debug;
use crate::storage::page;
use crate::storage::sqlite3_ondisk::{
    readBtreeCell, readVarInt, write_varint, BTreeCell, DbHeader, PageContent, PageType,
    TableInteriorCell, TableLeafCell,
};
use crate::types::{Cursor, CursorResult, OwnedRecord, OwnedValue, SeekKey, SeekOp};
use crate::{Pager, Result};
use std::cell::{Ref, RefCell};
use std::pin::Pin;
use std::rc::Rc;
use crate::storage::sqlite3_ondisk;
use super::page::PageArc;
use super::sqlite3_ondisk::{writeVarInt2Vec, IndexInteriorCell, IndexLeafCell, OverflowCell, DB_HEADER_SIZE};

const BYTE_LEN_PAGE_NUMBER_1ST_OVERFLOW_PAGE: usize = 4;
/*
** Maximum depth of an SQLite B-Tree structure. Any B-Tree deeper than
** this will be declared corrupt. This value is calculated based on a
** maximum database size of 2^31 pages a minimum fanout of 2 for a
** root-node and 3 for all other internal nodes.
**
** If a tree that appears to be taller than this is encountered, it is
** assumed that the database is corrupt.
*/
const BT_CURSOR_MAX_DEPTH: usize = 20;

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

    rootPageId: usize,

    rowId: RefCell<Option<u64>>,
    rec: RefCell<Option<OwnedRecord>>,

    nullFlag: bool,
    dbHeader: Rc<RefCell<DbHeader>>,

    /// Index internal pages are consumed on the way up, so we store going upwards flag in case
    /// we just moved to a parent page and the parent page is an internal index page which requires to be consumed
    going_upwards: bool,

    writeInfo: WriteInfo,

    /// traverse btree
    pageStack: PageStack,
}

impl Cursor for BTreeCursor {
    fn is_empty(&self) -> bool {
        self.rec.borrow().is_none()
    }

    fn root_page(&self) -> usize {
        self.rootPageId
    }

    fn rewind(&mut self) -> Result<CursorResult<()>> {
        self.move2Root();

        let (rowid, record) = return_if_io!(self.get_next_record(None));
        self.rowId.replace(rowid);
        self.rec.replace(record);
        Ok(CursorResult::Ok(()))
    }

    fn last(&mut self) -> Result<CursorResult<()>> {
        match self.move2RightmostLeaf()? {
            CursorResult::Ok(_) => self.prev(),
            CursorResult::IO => Ok(CursorResult::IO),
        }
    }

    fn next(&mut self) -> Result<CursorResult<()>> {
        let (rowid, record) = return_if_io!(self.get_next_record(None));
        self.rowId.replace(rowid);
        self.rec.replace(record);
        Ok(CursorResult::Ok(()))
    }

    fn prev(&mut self) -> Result<CursorResult<()>> {
        match self.get_prev_record()? {
            CursorResult::Ok((rowid, record)) => {
                self.rowId.replace(rowid);
                self.rec.replace(record);
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
        Ok(*self.rowId.borrow())
    }

    fn seek(&mut self, key: SeekKey<'_>, op: SeekOp) -> Result<CursorResult<bool>> {
        let (rowid, record) = return_if_io!(self.seek(key, op));
        self.rowId.replace(rowid);
        self.rec.replace(record);
        Ok(CursorResult::Ok(rowid.is_some()))
    }

    fn seek2Last(&mut self) -> Result<CursorResult<()>> {
        return_if_io!(self.move2RightmostLeaf());

        let (rowId, rec) = return_if_io!(self.get_next_record(None));

        if rowId.is_none() {
            assert!(return_if_io!(self.is_empty_table()));
            return Ok(CursorResult::Ok(()));
        }

        self.rowId.replace(rowId);
        self.rec.replace(rec);

        Ok(CursorResult::Ok(()))
    }

    fn record(&self) -> Result<Ref<Option<OwnedRecord>>> {
        Ok(self.rec.borrow())
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

        self.rowId.replace(Some(*intKey as u64));

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

        let cell_idx = self.findCell(contents, int_key);
        if cell_idx >= contents.cellCount() {
            Ok(CursorResult::Ok(false))
        } else {
            let equals = match &contents.getCell(cell_idx,
                                                 self.pager.clone(),
                                                 self.maxLocal(contents.getPageType()),
                                                 self.minLocal(),
                                                 self.pageUsableSpace())? {
                BTreeCell::TableLeafCell(l) => l.rowId == int_key,
                _ => unreachable!(),
            };

            Ok(CursorResult::Ok(equals))
        }
    }

    fn set_null_flag(&mut self, flag: bool) {
        self.nullFlag = flag;
    }

    fn get_null_flag(&self) -> bool {
        self.nullFlag
    }

    fn btree_create(&mut self, flags: usize) -> u32 {
        let page_type = match flags {
            1 => PageType::TableLeaf,
            2 => PageType::IndexLeaf,
            _ => unreachable!("wrong create table falgs, should be 1 for table and 2 for index, got {}", flags, ),
        };

        let page = self.allocatePage(page_type, 0);
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
            rowId: RefCell::new(None),
            rec: RefCell::new(None),
            nullFlag: false,
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
                self.maxLocal(contents.getPageType()),
                self.minLocal(),
                self.pageUsableSpace(),
            )?;

            match cell {
                BTreeCell::TableInteriorCell(TableInteriorCell { leftChildPageIndex: _left_child_page, .. }) => {
                    let mem_page = self.pager.readPage(_left_child_page as usize)?;
                    self.pageStack.push(mem_page);
                    // use cell_index = i32::MAX to tell next loop to go to the end of the current page
                    self.pageStack.set_cell_index(i32::MAX);
                    continue;
                }
                BTreeCell::TableLeafCell(TableLeafCell {
                                             rowId: _rowid, _payload, ..
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

    fn get_next_record(&mut self, predicate: Option<(SeekKey<'_>, SeekOp)>) -> Result<CursorResult<(Option<u64>, Option<OwnedRecord>)>> {
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
                match contents.rightmostChildPageIndex() {
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

            let cell = contents.getCell(
                cell_idx,
                self.pager.clone(),
                self.maxLocal(contents.getPageType()),
                self.minLocal(),
                self.pageUsableSpace(),
            )?;
            match &cell {
                BTreeCell::TableInteriorCell(TableInteriorCell { leftChildPageIndex: _left_child_page, .. }) => {
                    assert!(predicate.is_none());
                    self.pageStack.advance();
                    let mem_page = self.pager.readPage(*_left_child_page as usize)?;
                    self.pageStack.push(mem_page);
                    continue;
                }
                BTreeCell::TableLeafCell(TableLeafCell {
                                             rowId: _rowid,
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

    fn seek(&mut self, key: SeekKey<'_>, op: SeekOp) -> Result<CursorResult<(Option<u64>, Option<OwnedRecord>)>> {
        return_if_io!(self.moveTo(key.clone(), op.clone()));

        {
            let page = self.pageStack.top();
            return_if_locked!(page);

            let contents = page.getMutInner().pageContent.as_ref().unwrap();

            for cell_idx in 0..contents.cellCount() {
                let cell = contents.getCell(
                    cell_idx,
                    self.pager.clone(),
                    self.maxLocal(contents.getPageType()),
                    self.minLocal(),
                    self.pageUsableSpace(),
                )?;
                match &cell {
                    BTreeCell::TableLeafCell(TableLeafCell {
                                                 rowId: cell_rowid,
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

    fn move2RightmostLeaf(&mut self) -> Result<CursorResult<()>> {
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

            match contents.rightmostChildPageIndex() {
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
                                           self.maxLocal(pageContent.getPageType()),
                                           self.minLocal(),
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
                match pageContent.rightmostChildPageIndex() {
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
                    let topPage = self.pageStack.top();

                    let intKey = match key {
                        OwnedValue::Integer(intKey) => *intKey as u64,
                        _ => panic!("btree tables should be indexed by integers"),
                    };

                    // get page and find cell
                    let (cellIndex, pageType) = {
                        return_if_locked!(topPage);

                        topPage.setDirty();
                        self.pager.addDirtyPageId(topPage.getMutInner().pageId);

                        let pageContent = topPage.getMutInner().pageContent.as_mut().unwrap();
                        assert!(matches!(pageContent.getPageType(), PageType::TableLeaf));

                        (self.findCell(pageContent, intKey), PageType::TableLeaf)
                    };

                    // TODO: if overwrite drop cell

                    let mut cellPayload: Vec<u8> = Vec::new();
                    self.fillCellPayload(pageType, Some(intKey), &mut cellPayload, rec);

                    // insert
                    let overflowCellCount = {
                        let pageContent = topPage.getMutInner().pageContent.as_mut().unwrap();
                        self.insertIntoCell(pageContent, cellPayload.as_slice(), cellIndex);
                        pageContent.overflowCells.len()
                    };

                    if overflowCellCount > 0 {
                        self.writeInfo.writeState = WriteState::BalanceStart;
                    } else {
                        self.writeInfo.writeState = WriteState::Finish;
                    }
                }
                WriteState::BalanceStart | WriteState::BalanceMoveUp | WriteState::BalanceGetParentPage => return_if_io!(self.balanceLeaf()),
                WriteState::Finish => {
                    self.writeInfo.writeState = WriteState::Start;
                    return Ok(CursorResult::Ok(()));
                }
            };
        }
    }

    //// insert to position and shift other pointers
    fn insertIntoCell(&self, pageContent: &mut PageContent, payload: &[u8], cellIndex: usize) {
        let free = pageContent.computeFreeSpace(RefCell::borrow(&self.dbHeader));

        if payload.len() + 2 > (free as usize) {
            pageContent.overflowCells.push(OverflowCell {
                index: cellIndex,
                payload: Pin::new(Vec::from(payload)),
            });

            return;
        }

        // TODO: insert into cell payload in internal page
        let pc = self.allocate_cell_space(pageContent, payload.len());
        let buf = pageContent.asMutSlice();

        // copy data
        buf[pc as usize..pc as usize + payload.len()].copy_from_slice(payload);
        //  memmove(pIns+2, pIns, 2*(pPage->nCell - i));
        let (pointer_area_pc_by_idx, _) = pageContent.cell_get_raw_pointer_region();
        let pointer_area_pc_by_idx = pointer_area_pc_by_idx + (2 * cellIndex);

        // move previous pointers forward and insert new pointer there
        let n_cells_forward = 2 * (pageContent.cellCount() - cellIndex);
        if n_cells_forward > 0 {
            buf.copy_within(pointer_area_pc_by_idx..pointer_area_pc_by_idx + n_cells_forward,
                            pointer_area_pc_by_idx + 2);
        }
        pageContent.write_u16(pointer_area_pc_by_idx - pageContent.offset, pc);

        // update first byte of content area
        pageContent.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT, pc);

        // update cell count
        let new_n_cells = (pageContent.cellCount() + 1) as u16;
        pageContent.write_u16(page::PAGE_HEADER_OFFSET_CELL_COUNT, new_n_cells);
    }

    fn free_cell_range(&self, page: &mut PageContent, offset: u16, len: u16) {
        if page.firstFreeBlockPos() == 0 {
            // insert into empty list
            page.write_u16(offset as usize, 0);
            page.write_u16(offset as usize + 2, len);
            page.write_u16(page::PAGE_HEADER_OFFSET_FREE_BLOCK, offset);
            return;
        }
        let first_block = page.firstFreeBlockPos();

        if offset < first_block {
            // insert into head of list
            page.write_u16(offset as usize, first_block);
            page.write_u16(offset as usize + 2, len);
            page.write_u16(page::PAGE_HEADER_OFFSET_FREE_BLOCK, offset);
            return;
        }

        if offset <= page.cellContentAreaPos() {
            // extend boundary of content area
            page.write_u16(page::PAGE_HEADER_OFFSET_FREE_BLOCK, page.firstFreeBlockPos());
            page.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT, offset + len);
            return;
        }

        let maxpc = {
            let db_header = self.dbHeader.borrow();
            let usable_space = (db_header.pageSize - db_header.pageReservedSpace as u16) as usize;
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
        let (cell_start, cell_len) =
            page.cell_get_raw_region(cell_idx,
                                     self.maxLocal(page.getPageType()),
                                     self.minLocal(),
                                     self.pageUsableSpace());
        self.free_cell_range(page, cell_start as u16, cell_len as u16);
        page.write_u16(page::PAGE_HEADER_OFFSET_CELL_COUNT, page.cellCount() as u16 - 1);
    }

    /// This is a naive algorithm that doesn't try to distribute cells evenly by content.
    /// It will try to split the page in half by keys not by content.
    /// Sqlite tries to have a page at least 40% full.
    fn balanceLeaf(&mut self) -> Result<CursorResult<()>> {
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
                        self.maxLocal(page_copy.getPageType()),
                        self.minLocal(),
                        self.pageUsableSpace(),
                    );
                    let buf = page_copy.asMutSlice();
                    scratch_cells.push(to_static_buf(&buf[start..start + len]));
                }
                for overflow_cell in &page_copy.overflowCells {
                    scratch_cells.insert(overflow_cell.index, to_static_buf(&overflow_cell.payload));
                }

                *self.writeInfo.rightmost_pointer.borrow_mut() = page_copy.rightmostChildPageIndex();

                self.writeInfo.page_copy.replace(Some(page_copy));

                // allocate new pages and move cells to those new pages split procedure
                let page = current_page.getMutInner().pageContent.as_mut().unwrap();
                assert!(matches!(page.getPageType(),PageType::TableLeaf | PageType::TableInterior), "indexes still not supported ");

                let right_page = self.allocatePage(page.getPageType(), 0);

                self.writeInfo.new_pages.borrow_mut().clear();
                self.writeInfo
                    .new_pages
                    .borrow_mut()
                    .push(current_page.clone());
                self.writeInfo
                    .new_pages
                    .borrow_mut()
                    .push(right_page.clone());


                self.writeInfo.writeState = WriteState::BalanceGetParentPage;

                Ok(CursorResult::Ok(()))
            }
            WriteState::BalanceGetParentPage => {
                let parent = self.pageStack.parent();
                let loaded = parent.is_loaded();
                return_if_locked!(parent);

                if !loaded {
                    self.pager.load_page(parent.clone())?;
                    return Ok(CursorResult::IO);
                }
                parent.setDirty();

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

                parent.setDirty();
                self.pager.addDirtyPageId(parent.getMutInner().pageId);
                let parent_contents = parent.getMutInner().pageContent.as_mut().unwrap();
                // if this isn't empty next loop won't work
                assert_eq!(parent_contents.overflowCells.len(), 0);

                // Right page pointer is u32 in right most pointer, and in cell is u32 too, so we can use a *u32 to hold where we want to change this value
                let mut right_pointer = page::PAGE_HEADER_OFFSET_RIGHTMOST;
                for cell_idx in 0..parent_contents.cellCount() {
                    let cell =
                        parent_contents.getCell(cell_idx,
                                                self.pager.clone(),
                                                self.maxLocal(page_type.clone()),
                                                self.minLocal(),
                                                self.pageUsableSpace())?;
                    let found = match cell {
                        BTreeCell::TableInteriorCell(interior) => interior.leftChildPageIndex as usize == current_idx,
                        _ => unreachable!("Parent should always be a "),
                    };
                    if found {
                        let (start, _len) = parent_contents.cell_get_raw_region(
                            cell_idx,
                            self.maxLocal(page_type.clone()),
                            self.minLocal(),
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

                    contents.write_u16(page::PAGE_HEADER_OFFSET_FREE_BLOCK, 0);
                    contents.write_u16(page::PAGE_HEADER_OFFSET_CELL_COUNT, 0);

                    let db_header = RefCell::borrow(&self.dbHeader);
                    let cell_content_area_start =
                        db_header.pageSize - db_header.pageReservedSpace as u16;
                    contents.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT, cell_content_area_start);

                    contents.write_u8(page::PAGE_HEADER_OFFSET_FRAGMENTED, 0);
                    if !contents.isLeaf() {
                        contents.write_u32(page::PAGE_HEADER_OFFSET_RIGHTMOST, 0);
                    }
                }

                // distribute cells
                let new_pages_len = new_pages.len();
                let cells_per_page = scratch_cells.len() / new_pages.len();
                let mut current_cell_index = 0_usize;
                let mut divider_cells_index = Vec::new(); /* index to scratch cells that will be used as dividers in order */

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

                    let cell_index_range = current_cell_index..current_cell_index + cells_to_copy;
                    for (j, cell_idx) in cell_index_range.enumerate() {
                        let cell = scratch_cells[cell_idx];
                        self.insertIntoCell(contents, cell, j);
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
                                             self.maxLocal(contents.getPageType()),
                                             self.minLocal(),
                                             self.pageUsableSpace())?;

                        let last_cell_pointer = match last_cell {
                            BTreeCell::TableInteriorCell(interior) => interior.leftChildPageIndex,
                            _ => unreachable!(),
                        };

                        self.drop_cell(contents, contents.cellCount() - 1);
                        contents.write_u32(page::PAGE_HEADER_OFFSET_RIGHTMOST, last_cell_pointer);
                    }

                    // last page right most pointer points to previous right most pointer before splitting
                    let last_page = new_pages.last().unwrap();
                    let last_page_contents = last_page.getMutInner().pageContent.as_mut().unwrap();
                    last_page_contents.write_u32(page::PAGE_HEADER_OFFSET_RIGHTMOST,
                                                 self.writeInfo.rightmost_pointer.borrow().unwrap());
                }

                // insert dividers in parent
                // we can consider dividers the first cell of each page starting from the second page
                for (page_id_index, page) in
                    new_pages.iter_mut().take(new_pages_len - 1).enumerate()
                {
                    let contents = page.getMutInner().pageContent.as_mut().unwrap();
                    let divider_cell_index = divider_cells_index[page_id_index];
                    let cell_payload = scratch_cells[divider_cell_index];
                    let cell =
                        readBtreeCell(cell_payload,
                                      &contents.getPageType(),
                                      0,
                                      self.pager.clone(),
                                      self.maxLocal(contents.getPageType()),
                                      self.minLocal(),
                                      self.pageUsableSpace())?;

                    if is_leaf {
                        // create a new divider cell and push
                        let key = match cell {
                            BTreeCell::TableLeafCell(leaf) => leaf.rowId,
                            _ => unreachable!(),
                        };
                        let mut divider_cell = Vec::new();
                        divider_cell.extend_from_slice(&(page.getMutInner().pageId as u32).to_be_bytes());
                        divider_cell.extend(std::iter::repeat(0).take(9));
                        let n = write_varint(&mut divider_cell.as_mut_slice()[4..], key);
                        divider_cell.truncate(4 + n);
                        let parent_cell_idx = self.findCell(parent_contents, key);
                        self.insertIntoCell(
                            parent_contents,
                            divider_cell.as_slice(),
                            parent_cell_idx,
                        );
                    } else {
                        // move cell
                        let rowId = match cell {
                            BTreeCell::TableInteriorCell(interior) => interior.rowId,
                            _ => unreachable!(),
                        };

                        let parent_cell_idx = self.findCell(contents, rowId);
                        self.insertIntoCell(parent_contents, cell_payload, parent_cell_idx);
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
            _ => panic!("invalid state"),
        }
    }

    fn balance_root(&mut self) {
        /* todo: balance deeper, create child and copy contents of root there. Then split root */
        /* if we are in root page then we just need to create a new root and push key there */

        let is_page_1 = {
            let current_root = self.pageStack.top();
            current_root.getMutInner().pageId == 1
        };

        let offset = if is_page_1 { DB_HEADER_SIZE } else { 0 };
        let new_root_page = self.allocatePage(PageType::TableInterior, offset);
        {
            let current_root = self.pageStack.top();
            let current_root_contents = current_root.getMutInner().pageContent.as_ref().unwrap();

            let new_root_page_id = new_root_page.getMutInner().pageId;
            let new_root_page_contents = new_root_page.getMutInner().pageContent.as_mut().unwrap();
            if is_page_1 {
                // Copy header
                let current_root_buf = current_root_contents.asMutSlice();
                let new_root_buf = new_root_page_contents.asMutSlice();
                new_root_buf[0..DB_HEADER_SIZE].copy_from_slice(&current_root_buf[0..DB_HEADER_SIZE]);
            }
            // point new root right child to previous root
            new_root_page_contents.write_u32(page::PAGE_HEADER_OFFSET_RIGHTMOST, new_root_page_id as u32);
            new_root_page_contents.write_u16(page::PAGE_HEADER_OFFSET_CELL_COUNT, 0);
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
                    let buf = contents.asMutSlice();
                    buf.copy_within(DB_HEADER_SIZE.., 0);
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

    fn allocatePage(&self, page_type: PageType, offset: usize) -> PageArc {
        let page = self.pager.allocatePage().unwrap();
        page.init(page_type, &self.dbHeader.borrow(), offset);
        page
    }

    fn allocateOverflowPage(&self) -> PageArc {
        let page = self.pager.allocatePage().unwrap();

        let pageContent = page.getMutInner().pageContent.as_mut().unwrap();
        pageContent.asMutSlice().fill(0);

        page
    }

    /// Allocate space for a cell on a page.
    fn allocate_cell_space(&self, pageContent: &PageContent, amount: usize) -> u16 {
        let (cell_offset, _) = pageContent.cell_get_raw_pointer_region();
        let gap = cell_offset + 2 * pageContent.cellCount();
        let mut top = pageContent.cellContentAreaPos() as usize;

        // there are free blocks and enough space
        if pageContent.firstFreeBlockPos() != 0 && gap + 2 <= top {
            // find slot
            let db_header = RefCell::borrow(&self.dbHeader);
            let pc = find_free_cell(pageContent, db_header, amount);
            if pc != 0 {
                return pc as u16;
            }
            /* fall through, we might need to defragment */
        }

        if gap + 2 + amount > top {
            // defragment
            self.defragment_page(pageContent, RefCell::borrow(&self.dbHeader));
            top = pageContent.read_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT) as usize;
        }

        let db_header = RefCell::borrow(&self.dbHeader);
        top -= amount;

        pageContent.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT, top as u16);

        let usable_space = (db_header.pageSize - db_header.pageReservedSpace as u16) as usize;
        assert!(top + amount <= usable_space);
        top as u16
    }

    fn defragment_page(&self, page: &PageContent, db_header: Ref<DbHeader>) {
        let cloned_page = page.clone();
        // TODO(pere): usable space should include offset probably
        let usable_space = (db_header.pageSize - db_header.pageReservedSpace as u16) as u64;
        let mut cbrk = usable_space;

        // TODO: implement fast algorithm

        let last_cell = usable_space - 4;
        let first_cell = {
            let (start, end) = cloned_page.cell_get_raw_pointer_region();
            start + end
        };

        if cloned_page.cellCount() > 0 {
            let page_type = page.getPageType();
            let read_buf = cloned_page.asMutSlice();
            let write_buf = page.asMutSlice();

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
                            Err(_) => todo!("error while parsing varint from cell, probably treat this as corruption?"),
                        };
                        4 + nr_key as u64
                    }
                    PageType::TableLeaf => {
                        let (payload_size, nr_payload) = match readVarInt(&read_buf[pc as usize..]) {
                            Ok(v) => v,
                            Err(_) => todo!("error while parsing varint from cell, probably treat this as corruption?"),
                        };
                        let (_, nr_key) = match readVarInt(&read_buf[pc as usize + nr_payload..]) {
                            Ok(v) => v,
                            Err(_) => todo!("error while parsing varint from cell, probably treat this as corruption?"),
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
                write_buf[cbrk as usize..cbrk as usize + size as usize].copy_from_slice(&read_buf[pc as usize..pc as usize + size as usize]);
            }
        }

        // assert!( nfree >= 0 );
        // if( data[hdr+7]+cbrk-iCellFirst!=pPage->nFree ){
        //   return SQLITE_CORRUPT_PAGE(pPage);
        // }
        assert!(cbrk >= first_cell as u64);
        let write_buf = page.asMutSlice();

        // set new first byte of cell content
        page.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT, cbrk as u16);
        // set free block to 0, unused spaced can be retrieved from gap between cell pointer end and content start
        page.write_u16(page::PAGE_HEADER_OFFSET_FREE_BLOCK, 0);
        // set unused space to 0
        let first_cell = cloned_page.cellContentAreaPos() as u64;
        assert!(first_cell <= cbrk);
        write_buf[first_cell as usize..cbrk as usize].fill(0);
    }

    fn fillCellPayload(&self,
                       pageType: PageType,
                       key: Option<u64>,
                       cellPayload: &mut Vec<u8>,
                       rec: &OwnedRecord) {
        assert!(matches!(pageType,PageType::TableLeaf | PageType::IndexLeaf));

        // TODO: make record raw from start, having to serialize is not good
        let mut recordBuf = Vec::new();
        rec.serializeToVec(&mut recordBuf);

        // leaf都有的: payload大小
        writeVarInt2Vec(recordBuf.len() as u64, cellPayload);

        // rowId
        if matches!(pageType, PageType::TableLeaf) {
            writeVarInt2Vec(key.unwrap(), cellPayload);
        }

        let maxLocal = self.maxLocal(pageType.clone());

        // enough allowed space to fit inside a btree page
        if recordBuf.len() <= maxLocal {
            cellPayload.extend_from_slice(recordBuf.as_slice());
            // 因为未overflow, leaf 末尾 4 byte 的 “Page number of first overflow page” 为0
            cellPayload.resize(cellPayload.len() + BYTE_LEN_PAGE_NUMBER_1ST_OVERFLOW_PAGE, 0);
            return;
        }

        let minLocal = self.minLocal();
        let mut spaceLeft = minLocal + (recordBuf.len() - minLocal) % (self.pageUsableSpace() - BYTE_LEN_PAGE_NUMBER_1ST_OVERFLOW_PAGE);

        if spaceLeft > maxLocal {
            spaceLeft = minLocal;
        }

        let cellPayloadLenOld = cellPayload.len();

        let mut to_copy_buffer = recordBuf.as_slice();

        cellPayload.resize(cellPayloadLenOld + spaceLeft + BYTE_LEN_PAGE_NUMBER_1ST_OVERFLOW_PAGE, 0);
        let mut dataPos = unsafe { cellPayload.as_mut_ptr().add(cellPayloadLenOld) };
        // 末尾的4字节是头个overflowPage的id
        let mut nextOverflowPageIdPos = unsafe { cellPayload.as_mut_ptr().add(cellPayloadLenOld + spaceLeft) };

        // 要是有overflow,那么cell的末尾4字节是第头个overflow page的id,然后后面的各个overflow page的头4 byte是下个 overflow page的id
        loop {
            let copyCount = spaceLeft.min(to_copy_buffer.len());
            unsafe { std::ptr::copy(to_copy_buffer.as_ptr(), dataPos, copyCount) };

            if to_copy_buffer.len() - copyCount == 0 {
                break;
            }

            // we still have bytes to add, we will need to allocate new overflow page
            let overflowPage = self.allocateOverflowPage();

            {
                let overflowPageId = overflowPage.getMutInner().pageId as u32;
                let pageContent = overflowPage.getMutInner().pageContent.as_mut().unwrap();

                // TODO: take into account offset here?
                let buf = pageContent.asMutSlice();

                // update pointer to new overflow page
                unsafe { std::ptr::copy(overflowPageId.to_be_bytes().as_ptr(), nextOverflowPageIdPos, BYTE_LEN_PAGE_NUMBER_1ST_OVERFLOW_PAGE) };

                dataPos = unsafe { buf.as_mut_ptr().add(BYTE_LEN_PAGE_NUMBER_1ST_OVERFLOW_PAGE) };
                // 各个overflowPage的头4 byte是下个overflow page的id
                nextOverflowPageIdPos = buf.as_mut_ptr();
                spaceLeft = self.pageUsableSpace() - 4;
            }

            to_copy_buffer = &to_copy_buffer[copyCount..];
        }
    }

    fn maxLocal(&self, page_type: PageType) -> usize {
        let pageUsableSpace = self.pageUsableSpace();
        match page_type {
            PageType::IndexInterior | PageType::TableInterior => (pageUsableSpace - 12) * 64 / 255 - 23,
            PageType::IndexLeaf | PageType::TableLeaf => pageUsableSpace - 35,
        }
    }

    fn minLocal(&self) -> usize {
        let pageUsableSpace = self.pageUsableSpace();
        (pageUsableSpace - 12) * 32 / 255 - 23
    }

    fn pageUsableSpace(&self) -> usize {
        let dbHeader = RefCell::borrow(&self.dbHeader);
        (dbHeader.pageSize - dbHeader.pageReservedSpace as u16) as usize
    }

    fn findCell(&self, page: &PageContent, intKey: u64) -> usize {
        let mut cellIndex = 0;

        let cellCount = page.cellCount();
        while cellIndex < cellCount {
            match page.getCell(cellIndex,
                               self.pager.clone(),
                               self.maxLocal(page.getPageType()),
                               self.minLocal(),
                               self.pageUsableSpace()).unwrap() {
                BTreeCell::TableLeafCell(cell) => {
                    if intKey <= cell.rowId {
                        break;
                    }
                }
                BTreeCell::TableInteriorCell(cell) => {
                    if intKey <= cell.rowId {
                        break;
                    }
                }
                _ => todo!(),
            }

            cellIndex += 1;
        }

        cellIndex
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
    let mut pc = page_ref.firstFreeBlockPos() as usize;

    let buf = page_ref.asMutSlice();

    let usable_space = (db_header.pageSize - db_header.pageReservedSpace as u16) as usize;
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

fn to_static_buf(buf: &[u8]) -> &'static [u8] {
    unsafe { std::mem::transmute::<&[u8], &'static [u8]>(buf) }
}