use crate::{
    types::{SeekKey, SeekOp},
    Result,
};
use std::cell::{Ref, RefCell};

use crate::types::{Cursor, CursorResult, OwnedRecord, OwnedValue};

pub struct PseudoCursor {
    current: RefCell<Option<OwnedRecord>>,
}

impl PseudoCursor {
    pub fn new() -> Self {
        Self {
            current: RefCell::new(None),
        }
    }
}

impl Cursor for PseudoCursor {
    fn is_empty(&self) -> bool {
        self.current.borrow().is_none()
    }

    fn root_page(&self) -> usize {
        unreachable!()
    }

    fn rewind(&mut self) -> Result<CursorResult<()>> {
        *self.current.borrow_mut() = None;
        Ok(CursorResult::Ok(()))
    }

    fn last(&mut self) -> Result<CursorResult<()>> {
        todo!()
    }

    fn next(&mut self) -> Result<CursorResult<()>> {
        *self.current.borrow_mut() = None;
        Ok(CursorResult::Ok(()))
    }

    fn prev(&mut self) -> Result<CursorResult<()>> {
        todo!()
    }

    fn wait_for_completion(&mut self) -> Result<()> {
        Ok(())
    }

    fn rowid(&self) -> Result<Option<u64>> {
        let rowId =
            self.current.borrow().as_ref().map(|record| match record.values[0] {
                OwnedValue::Integer(rowid) => rowid as u64,
                ref ov => panic!("Expected integer value, got {:?}", ov),
            });

        Ok(rowId)
    }

    fn seek(&mut self, _: SeekKey<'_>, _: SeekOp) -> Result<CursorResult<bool>> {
        unimplemented!();
    }

    fn seek2Last(&mut self) -> Result<CursorResult<()>> {
        unimplemented!();
    }

    fn record(&self) -> Result<Ref<Option<OwnedRecord>>> {
        Ok(self.current.borrow())
    }

    fn insert(&mut self,
              key: &OwnedValue,
              record: &OwnedRecord,
              moved_before: bool) -> Result<CursorResult<()>> {
        *self.current.borrow_mut() = Some(record.clone());
        Ok(CursorResult::Ok(()))
    }

    fn exists(&mut self, key: &OwnedValue) -> Result<CursorResult<bool>> {
        todo!()
    }

    fn set_null_flag(&mut self, _null_flag: bool) {
    }

    fn get_null_flag(&self) -> bool {
        false
    }

    fn btree_create(&mut self, _flags: usize) -> u32 {
        unreachable!("Please don't.")
    }
}
