use std::rc::Weak;
use std::{cell::RefCell, rc::Rc};

use crate::storage::sqlite3_ondisk::DbHeader;
use crate::Conn;
use crate::{schema::Schema, vdbe::Program, Result};
use sqlite3_parser::ast;

use super::emitter::emit_program;
use super::optimizer::optimize_plan;
use super::planner::prepareSelPlan;

pub fn translateSel(schema: &Schema,
                    select: ast::Select,
                    dbHeader: Rc<RefCell<DbHeader>>,
                    connection: Weak<Conn>) -> Result<Program> {
    let selectPlan = prepareSelPlan(schema, select)?;
    let optimized_plan = optimize_plan(selectPlan)?;
    emit_program(dbHeader, optimized_plan, connection)
}
