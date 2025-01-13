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
                newPages: RefCell::new(Vec::with_capacity(4)),
                scratchCells: RefCell::new(Vec::new()),
                rightmostChildPageIndex: RefCell::new(None),
                pageContentClone: RefCell::new(None),
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
                    if self.pageStack.hasParent() {
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
            if !page.loaded() {
                self.pager.loadPage(page.clone())?;
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
                                             rowId: _rowid, payload: _payload, ..
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
            if !mem_page_rc.loaded() {
                self.pager.loadPage(mem_page_rc.clone())?;
                return Ok(CursorResult::IO);
            }
            let mem_page = mem_page_rc.getMutInner();

            let contents = mem_page.pageContent.as_ref().unwrap();

            if cell_idx == contents.cellCount() {
                // do rightmost
                let has_parent = self.pageStack.hasParent();
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
                                             payload: _payload,
                                             firstOverflowPageIndex: _,
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
                                                 payload: payload,
                                                 firstOverflowPageIndex: _,
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
                    let curPage = self.pageStack.top();

                    let intKey = match key {
                        OwnedValue::Integer(intKey) => *intKey as u64,
                        _ => panic!("btree tables should be indexed by integers"),
                    };

                    // get page and find cell
                    let (cellIndex, pageType) = {
                        return_if_locked!(curPage);

                        curPage.setDirty();
                        self.pager.addDirtyPageId(curPage.getMutInner().pageId);

                        let pageContent = curPage.getMutInner().pageContent.as_mut().unwrap();
                        assert!(matches!(pageContent.getPageType(), PageType::TableLeaf));

                        (self.findCell(pageContent, intKey), PageType::TableLeaf)
                    };

                    // TODO: if overwrite drop cell

                    let mut cellPayload: Vec<u8> = Vec::new();
                    self.fillCellPayload(pageType, Some(intKey), &mut cellPayload, rec);

                    // insert
                    let overflowCellCount = {
                        let curPageContent = curPage.getMutInner().pageContent.as_mut().unwrap();
                        self.insertIntoCell(curPageContent, cellPayload.as_slice(), cellIndex);
                        curPageContent.overflowCells.len()
                    };

                    self.writeInfo.writeState = if overflowCellCount > 0 {
                        WriteState::BalanceStart
                    } else {
                        WriteState::Finish
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

    /// insert to position and shift other pointers
    fn insertIntoCell(&self, pageContent: &mut PageContent, payload: &[u8], cellIndex: usize) {
        let pageFreeSpace = pageContent.computeFreeSpace(RefCell::borrow(&self.dbHeader));

        if payload.len() + page::POINTER_CELL_BYTE_LEN > (pageFreeSpace as usize) {
            pageContent.overflowCells.push(OverflowCell {
                index: cellIndex,
                payload: Pin::new(Vec::from(payload)),
            });

            return;
        }

        // TODO: insert into cell payload in internal page
        let dataCellPos = pageContent.allocateCellSpace(&self.dbHeader, payload.len());
        let buf = pageContent.asMutSlice();

        // copy playload to buf
        buf[dataCellPos as usize..dataCellPos as usize + payload.len()].copy_from_slice(payload);

        //  memmove(pIns+2, pIns, 2*(pPage->nCell - i));
        let (pointerCellsStartPos, _) = pageContent.getPointerCellsStartPos();
        let pointerCellStartPos = pointerCellsStartPos + (page::POINTER_CELL_BYTE_LEN * cellIndex);

        // move previous pointers forward and insert new pointer there
        let n_cells_forward = page::POINTER_CELL_BYTE_LEN * (pageContent.cellCount() - cellIndex);
        if n_cells_forward > 0 {
            buf.copy_within(pointerCellStartPos..pointerCellStartPos + n_cells_forward,
                            pointerCellStartPos + page::POINTER_CELL_BYTE_LEN);
        }
        pageContent.write_u16(pointerCellStartPos - pageContent.offset, dataCellPos);

        // 变更 CELL_CONTENT_START_POS
        pageContent.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT_START_POS, dataCellPos);

        // 变更 cell count
        pageContent.write_u16(page::PAGE_HEADER_OFFSET_CELL_COUNT, (pageContent.cellCount() + 1) as u16);
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

        if offset <= page.cellContentAreaStartPos() {
            // extend boundary of content area
            page.write_u16(page::PAGE_HEADER_OFFSET_FREE_BLOCK, page.firstFreeBlockPos());
            page.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT_START_POS, offset + len);
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

    fn dropCell(&self, pageContent: &mut PageContent, cellIndex: usize) {
        let (cell_start, cell_len) =
            pageContent.getCellPayloadStartPos(cellIndex,
                                               self.maxLocal(pageContent.getPageType()),
                                               self.minLocal(),
                                               self.pageUsableSpace());

        self.free_cell_range(pageContent, cell_start as u16, cell_len as u16);

        pageContent.write_u16(page::PAGE_HEADER_OFFSET_CELL_COUNT, pageContent.cellCount() as u16 - 1);
    }

    /// This is a naive algorithm that doesn't try to distribute cells evenly by content.
    /// It will try to split the page in half by keys not by content.
    /// Sqlite tries to have a page at least 40% full.
    fn balanceLeaf(&mut self) -> Result<CursorResult<()>> {
        match self.writeInfo.writeState {
            WriteState::BalanceStart => {
                let curPage = self.pageStack.top();

                // check if we don't need to balance ,don't continue if there are no overflow cells
                if curPage.getMutInner().pageContent.as_mut().unwrap().overflowCells.is_empty() {
                    self.writeInfo.writeState = WriteState::Finish;
                    return Ok(CursorResult::Ok(()));
                }

                if !self.pageStack.hasParent() {
                    self.balanceRoot();
                    return Ok(CursorResult::Ok(()));
                }

                let curPageContentClone = curPage.getMutInner().pageContent.as_ref().unwrap().clone();

                // In memory in order copy of all cells in pages we want to balance. For now let's do a 2 page split.
                // Right pointer in interior cells should be converted to regular cells if more than 2 pages are used for balancing.
                let mut scratchCellPayloads = self.writeInfo.scratchCells.borrow_mut();
                scratchCellPayloads.clear();

                for cellIndex in 0..curPageContentClone.cellCount() {
                    let (start, len) =
                        curPageContentClone.getCellPayloadStartPos(cellIndex,
                                                                   self.maxLocal(curPageContentClone.getPageType()),
                                                                   self.minLocal(),
                                                                   self.pageUsableSpace());
                    let buf = curPageContentClone.asMutSlice();
                    scratchCellPayloads.push(toStaticBuf(&buf[start..start + len]));
                }

                for overflowCell in &curPageContentClone.overflowCells {
                    scratchCellPayloads.insert(overflowCell.index, toStaticBuf(&overflowCell.payload));
                }

                *self.writeInfo.rightmostChildPageIndex.borrow_mut() = curPageContentClone.rightmostChildPageIndex();

                self.writeInfo.pageContentClone.replace(Some(curPageContentClone));

                // allocate new pages and move cells to those new pages split procedure
                let curPageContent = curPage.getMutInner().pageContent.as_mut().unwrap();
                assert!(matches!(curPageContent.getPageType(), PageType::TableLeaf | PageType::TableInterior), "indexes not supported");
                let rightPage = self.allocatePage(curPageContent.getPageType(), 0);

                self.writeInfo.newPages.borrow_mut().clear();
                self.writeInfo.newPages.borrow_mut().push(curPage.clone());
                self.writeInfo.newPages.borrow_mut().push(rightPage.clone());

                self.writeInfo.writeState = WriteState::BalanceGetParentPage;

                Ok(CursorResult::Ok(()))
            }
            WriteState::BalanceGetParentPage => {
                let parentPage = self.pageStack.parent();
                return_if_locked!(parentPage);

                if !parentPage.loaded() {
                    self.pager.loadPage(parentPage.clone())?;
                    return Ok(CursorResult::IO);
                }

                parentPage.setDirty();

                self.writeInfo.writeState = WriteState::BalanceMoveUp;

                Ok(CursorResult::Ok(()))
            }
            WriteState::BalanceMoveUp => {
                let parentPage = self.pageStack.parent();

                let (curPageType, curPageIndex) = {
                    let curPage = self.pageStack.top();
                    let curPageContent = curPage.getMutInner().pageContent.as_ref().unwrap();
                    (curPageContent.getPageType().clone(), curPage.getMutInner().pageId)
                };

                parentPage.setDirty();
                self.pager.addDirtyPageId(parentPage.getMutInner().pageId);

                let parentPageContent = parentPage.getMutInner().pageContent.as_mut().unwrap();
                assert_eq!(parentPageContent.overflowCells.len(), 0);

                let rightmostPos = {
                    let mut rightmostPos = page::PAGE_HEADER_OFFSET_RIGHTMOST;

                    for cellIndex in 0..parentPageContent.cellCount() {
                        let cell =
                            parentPageContent.getCell(cellIndex,
                                                      self.pager.clone(),
                                                      self.maxLocal(curPageType.clone()),
                                                      self.minLocal(),
                                                      self.pageUsableSpace())?;

                        let found = match cell {
                            BTreeCell::TableInteriorCell(tableInteriorCell) => tableInteriorCell.leftChildPageIndex as usize == curPageIndex,
                            _ => unreachable!("Parent should always be a "),
                        };

                        if found {
                            let (start, _) =
                                parentPageContent.getCellPayloadStartPos(cellIndex,
                                                                         self.maxLocal(curPageType.clone()),
                                                                         self.minLocal(),
                                                                         self.pageUsableSpace());
                            rightmostPos = start;
                            break;
                        }
                    }

                    rightmostPos
                };

                let mut newPages = self.writeInfo.newPages.borrow_mut();
                let scratchCells = self.writeInfo.scratchCells.borrow();

                // reset new pages header
                for newPage in newPages.iter() {
                    assert!(newPage.is_dirty());

                    let newPageContent = newPage.getMutInner().pageContent.as_mut().unwrap();

                    newPageContent.write_u16(page::PAGE_HEADER_OFFSET_FREE_BLOCK, 0);
                    newPageContent.write_u16(page::PAGE_HEADER_OFFSET_CELL_COUNT, 0);

                    let dbHeader = RefCell::borrow(&self.dbHeader);
                    newPageContent.write_u16(page::PAGE_HEADER_OFFSET_CELL_CONTENT_START_POS, dbHeader.pageUsableSpace() as u16);

                    newPageContent.write_u8(page::PAGE_HEADER_OFFSET_FRAGMENTED, 0);

                    if !newPageContent.isLeaf() {
                        newPageContent.write_u32(page::PAGE_HEADER_OFFSET_RIGHTMOST, 0);
                    }
                }

                // 将各个的cell的内容分配到各个newPage
                let newPagesLen = newPages.len();
                let cellsPerPage = scratchCells.len() / newPagesLen;
                let mut current_cell_index = 0_usize;
                let mut dividerCellIndexVec = Vec::new();

                for (i, newPage) in newPages.iter().enumerate() {
                    let newPageContent = newPage.getMutInner().pageContent.as_mut().unwrap();

                    let cellsToCopyCount =
                        if i == newPagesLen - 1 {
                            scratchCells.len() - current_cell_index
                        } else {
                            cellsPerPage
                        };

                    for (j, cell_idx) in (current_cell_index..current_cell_index + cellsToCopyCount).enumerate() {
                        self.insertIntoCell(newPageContent, scratchCells[cell_idx], j);
                    }

                    dividerCellIndexVec.push(current_cell_index + cellsToCopyCount - 1);

                    current_cell_index += cellsToCopyCount;
                }

                let curPageIsLeaf = self.pageStack.top().getMutInner().pageContent.as_ref().unwrap().isLeaf();

                // update rightmost pointer for each page if we are in interior page
                if !curPageIsLeaf {
                    for newPage in newPages.iter_mut().take(newPagesLen - 1) {
                        let newPageContent = newPage.getMutInner().pageContent.as_mut().unwrap();

                        assert_eq!(newPageContent.cellCount(), 1);

                        let lastCellIndex = newPageContent.cellCount() - 1;

                        let lastCell =
                            newPageContent.getCell(lastCellIndex,
                                                   self.pager.clone(),
                                                   self.maxLocal(newPageContent.getPageType()),
                                                   self.minLocal(),
                                                   self.pageUsableSpace())?;

                        let leftChildPageIndex = match lastCell {
                            BTreeCell::TableInteriorCell(tableInteriorCell) => tableInteriorCell.leftChildPageIndex,
                            _ => unreachable!(),
                        };

                        self.dropCell(newPageContent, lastCellIndex);

                        newPageContent.write_u32(page::PAGE_HEADER_OFFSET_RIGHTMOST, leftChildPageIndex);
                    }

                    // last page right most pointer points to previous right most pointer before splitting
                    let lastNewPage = newPages.last().unwrap();
                    let lastNewPageContent = lastNewPage.getMutInner().pageContent.as_mut().unwrap();
                    lastNewPageContent.write_u32(page::PAGE_HEADER_OFFSET_RIGHTMOST, self.writeInfo.rightmostChildPageIndex.borrow().unwrap());
                }

                // insert dividers in parent
                // we can consider dividers the first cell of each page starting from the second page
                for (newPageIndex, newPage) in newPages.iter_mut().take(newPagesLen - 1).enumerate() {
                    let newPageContent = newPage.getMutInner().pageContent.as_mut().unwrap();

                    let dividerCellPayload = scratchCells[dividerCellIndexVec[newPageIndex]];

                    let cell =
                        readBtreeCell(dividerCellPayload,
                                      &newPageContent.getPageType(),
                                      0,
                                      self.pager.clone(),
                                      self.maxLocal(newPageContent.getPageType()),
                                      self.minLocal(),
                                      self.pageUsableSpace())?;

                    // create a new divider cell and push
                    if curPageIsLeaf {
                        let rowId = match cell {
                            BTreeCell::TableLeafCell(leaf) => leaf.rowId,
                            _ => unreachable!(),
                        };

                        // 生成 table interior cell
                        let mut divider_cell = Vec::new();
                        divider_cell.extend_from_slice(&(newPage.getMutInner().pageId as u32).to_be_bytes());
                        divider_cell.extend(std::iter::repeat(0).take(9));
                        let varIntLen = write_varint(&mut divider_cell.as_mut_slice()[4..], rowId);
                        divider_cell.truncate(4 + varIntLen);

                        let parent_cell_idx = self.findCell(parentPageContent, rowId);

                        self.insertIntoCell(parentPageContent, divider_cell.as_slice(), parent_cell_idx);
                    } else {  // move cell
                        let rowId = match cell {
                            BTreeCell::TableInteriorCell(interior) => interior.rowId,
                            _ => unreachable!(),
                        };

                        let parent_cell_idx = self.findCell(newPageContent, rowId);
                        self.insertIntoCell(parentPageContent, dividerCellPayload, parent_cell_idx);
                        // self.drop_cell(*page, 0);
                    }
                }

                // copy last page id to right pointer
                parentPageContent.write_u32(rightmostPos, newPages.last().unwrap().getMutInner().pageId as u32);

                self.pageStack.pop();
                self.writeInfo.writeState = WriteState::BalanceStart;
                let _ = self.writeInfo.pageContentClone.take();

                Ok(CursorResult::Ok(()))
            }
            _ => panic!("invalid state"),
        }
    }

    fn balanceRoot(&mut self) {
        /* todo: balance deeper, create child and copy contents of root there. Then split root */
        /* if we are in root page then we just need to create a new root and push key there */

        let isFirstPage = {
            let topPage = self.pageStack.top();
            topPage.getMutInner().pageId == 1
        };

        let offset = if isFirstPage { DB_HEADER_SIZE } else { 0 };
        let new_root_page = self.allocatePage(PageType::TableInterior, offset);
        {
            let current_root = self.pageStack.top();
            let current_root_contents = current_root.getMutInner().pageContent.as_ref().unwrap();

            let new_root_page_id = new_root_page.getMutInner().pageId;
            let new_root_page_contents = new_root_page.getMutInner().pageContent.as_mut().unwrap();
            if isFirstPage {
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
                if isFirstPage {
                    // Remove header from child and set offset to 0
                    let contents = child.getMutInner().pageContent.as_mut().unwrap();
                    let (cell_pointer_offset, _) = contents.getPointerCellsStartPos();
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
        page.initPageHeader(page_type, &self.dbHeader.borrow(), offset);
        page
    }

    fn allocateOverflowPage(&self) -> PageArc {
        let page = self.pager.allocatePage().unwrap();

        let pageContent = page.getMutInner().pageContent.as_mut().unwrap();
        pageContent.asMutSlice().fill(0);

        page
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

    fn findCell(&self, pageContent: &PageContent, intKey: u64) -> usize {
        let mut cellIndex = 0;

        let cellCount = pageContent.cellCount();
        while cellIndex < cellCount {
            match pageContent.getCell(cellIndex,
                                      self.pager.clone(),
                                      self.maxLocal(pageContent.getPageType()),
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
        let current = self.current();
        self.pageStack.borrow()[current].as_ref().unwrap().clone()
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

    fn hasParent(&self) -> bool {
        *self.curPageIndexInStack.borrow() > 0
    }

    fn clear(&self) {
        *self.curPageIndexInStack.borrow_mut() = -1;
    }
}

struct WriteInfo {
    writeState: WriteState,
    newPages: RefCell<Vec<PageArc>>,
    scratchCells: RefCell<Vec<&'static [u8]>>,
    rightmostChildPageIndex: RefCell<Option<u32>>,
    pageContentClone: RefCell<Option<PageContent>>, // this holds the copy a of a page needed for buffer references
}

#[derive(Debug, Copy, Clone)]
enum WriteState {
    Start,
    BalanceStart,
    BalanceGetParentPage,
    BalanceMoveUp,
    Finish,
}

fn toStaticBuf(buf: &[u8]) -> &'static [u8] {
    unsafe { std::mem::transmute::<&[u8], &'static [u8]>(buf) }
}