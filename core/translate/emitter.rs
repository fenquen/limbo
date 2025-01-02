// This module contains code for emitting bytecode instructions for SQL query execution.
// It handles translating high-level SQL operations into low-level bytecode that can be executed by the virtual machine.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::{Rc, Weak};

use sqlite3_parser::ast::{self};

use crate::schema::{Column, PseudoTable, Table};
use crate::storage::sqlite3_ondisk::DbHeader;
use crate::translate::plan::{IterationDirection, IndexSearch};
use crate::types::{OwnedRecord, OwnedValue};
use crate::util::exprs_are_equivalent;
use crate::vdbe::program_builder::ProgramBuilder;
use crate::vdbe::{BranchOffset, Insn, Program};
use crate::{Conn, Result};
use crate::translate::expr;
use super::expr::{
    translate_aggregation, translate_aggregation_groupby,
    translate_condition_expr,
    ConditionMetadata,
};
use super::plan::{Aggregate, BTreeTableRef, Direction, GroupBy, Plan};
use super::plan::{ResultSetColumn, SrcOperator};

// Metadata for handling LEFT JOIN operations
#[derive(Debug)]
pub struct LeftJoinMetadata {
    // integer register that holds a flag that is set to true if the current row has a match for the left join
    pub match_flag_register: usize,

    // label for the instruction that sets the match flag to true
    pub set_match_flag_true_label: BranchOffset,

    // label for the instruction that checks if the match flag is true
    pub check_match_flag_label: BranchOffset,
}

// Metadata for handling ORDER BY operations
#[derive(Debug)]
pub struct SortMetadata {
    // cursor id for the Sorter table where the sorted rows are stored
    pub sort_cursor: usize,

    // register where the sorter data is inserted and later retrieved from
    pub sorter_data_register: usize,
}

// Metadata for handling GROUP BY operations
#[derive(Debug)]
pub struct GroupByMetadata {
    // Cursor ID for the Sorter table where the grouped rows are stored
    pub sort_cursor: usize,

    // Label for the subroutine that clears the accumulator registers (temporary storage for per-group aggregate calculations)
    pub subroutine_accumulator_clear_label: BranchOffset,

    // Register holding the return offset for the accumulator clear subroutine
    pub subroutine_accumulator_clear_return_offset_register: usize,

    // Label for the subroutine that outputs the accumulator contents
    pub subroutine_accumulator_output_label: BranchOffset,

    // Register holding the return offset for the accumulator output subroutine
    pub subroutine_accumulator_output_return_offset_register: usize,

    // Label for the instruction that sets the accumulator indicator to true (indicating data exists in the accumulator for the current group)
    pub accumulator_indicator_set_true_label: BranchOffset,

    // Register holding the key used for sorting in the Sorter
    pub sorter_key_register: usize,

    // Register holding a flag to abort the grouping process if necessary
    pub abort_flag_register: usize,

    // Register holding a boolean indicating whether there's data in the accumulator (used for aggregation)
    pub data_in_accumulator_indicator_register: usize,

    // Register holding the start of the accumulator group registers (i.e. the groups, not the aggregates)
    pub group_exprs_accumulator_register: usize,

    // Starting index of the register(s) that hold the comparison result between the current row and the previous row
    // The comparison result is used to determine if the current row belongs to the same group as the previous row
    // Each group by expression has a corresponding register
    pub group_exprs_comparison_register: usize,
}

/// The Metadata struct holds various information and labels used during bytecode generation.
/// It is used for maintaining state and control flow during the bytecode generation process.
#[derive(Debug)]
pub struct Metadata {
    // labels for the instructions that terminate the execution when a conditional check evaluates to false. typically jumps to Halt, but can also jump to AggFinal if a parent in the tree is an aggregation
    terminationLabelStack: Vec<BranchOffset>,

    // labels for the instructions that jump to the next row in the current operator.
    // for example, in a join with two nested scans, the inner loop will jump to its Next instruction when the join condition is false;
    // in a join with a scan and a seek, the seek will jump to the scan's Next instruction when the join condition is false.
    nextRowLabels: HashMap<usize, BranchOffset>,

    // labels for the instructions beginning the inner loop of a scan operator.
    scanLoopBodyLabels: Vec<BranchOffset>,

    // metadata for the group by operator
    group_by_metadata: Option<GroupByMetadata>,

    // metadata for the order by operator
    sort_metadata: Option<SortMetadata>,

    // mapping between Join operator id and associated metadata (for left joins only)
    left_joins: HashMap<usize, LeftJoinMetadata>,

    // First register of the aggregation results
    pub aggregation_start_register: Option<usize>,

    // We need to emit result columns in the order they are present in the SELECT, but they may not be in the same order in the ORDER BY sorter.
    // This vector holds the indexes of the result columns in the ORDER BY sorter.
    pub result_column_indexes_in_orderby_sorter: HashMap<usize, usize>,

    // We might skip adding a SELECT result column into the ORDER BY sorter if it is an exact match in the ORDER BY keys.
    // This vector holds the indexes of the result columns that we need to skip.
    pub result_columns_to_skip_in_orderby_sorter: Option<Vec<usize>>,
}

/// Initialize the program with basic setup and return initial metadata and labels
fn prologue() -> Result<(ProgramBuilder, Metadata, BranchOffset, BranchOffset)> {
    let mut programBuilder = ProgramBuilder::new();

    let initLabel = programBuilder.allocateLabel();
    let haltLabel = programBuilder.allocateLabel();

    programBuilder.addInsnWithLabelDependency(Insn::Init { target_pc: initLabel }, initLabel);

    let metadata = Metadata {
        terminationLabelStack: vec![haltLabel],
        group_by_metadata: None,
        left_joins: HashMap::new(),
        nextRowLabels: HashMap::new(),
        scanLoopBodyLabels: vec![],
        sort_metadata: None,
        aggregation_start_register: None,
        result_column_indexes_in_orderby_sorter: HashMap::new(),
        result_columns_to_skip_in_orderby_sorter: None,
    };

    let startOffset = programBuilder.nextPc();

    Ok((programBuilder, metadata, initLabel, startOffset))
}

/// Clean up and finalize the program, resolving any remaining labels
/// Note that although these are the final instructions, typically an SQLite
/// query will jump to the Transaction instruction via init_label.
fn epilogue(program: &mut ProgramBuilder,
            metadata: &mut Metadata,
            init_label: BranchOffset,
            start_offset: BranchOffset) -> Result<()> {
    let halt_label = metadata.terminationLabelStack.pop().unwrap();
    program.resolveLabel(halt_label, program.nextPc());
    program.addInsn0(Insn::Halt {
        err_code: 0,
        description: String::new(),
    });

    program.resolveLabel(init_label, program.nextPc());
    program.addInsn0(Insn::Transaction { write: false });

    program.emit_constant_insns();
    program.addInsn0(Insn::Goto {
        targetPc: start_offset,
    });

    program.resolve_deferred_labels();

    Ok(())
}

/// Main entry point for emitting bytecode for a SQL query
/// Takes a query plan and generates the corresponding bytecode program
pub fn emit_program(dbHeader: Rc<RefCell<DbHeader>>,
                    mut plan: Plan,
                    conn: Weak<Conn>) -> Result<Program> {
    let (mut programBuilder, mut metadata, initLabel, startOffset) = prologue()?;

    if let Some(limit) = plan.limit {
        if limit == 0 {
            epilogue(&mut programBuilder, &mut metadata, initLabel, startOffset)?;
            return Ok(programBuilder.build(dbHeader, conn));
        }
    }

    // No rows will be read from source table loops if there is a constant false condition eg. WHERE 0
    // however an aggregation might still happen,
    // e.g. SELECT COUNT(*) WHERE 0 returns a row with 0, not an empty result set
    let skipLoopsLabel =
        if plan.containsConstantFalseCondition {
            let skipLoopsLabel = programBuilder.allocateLabel();
            programBuilder.addInsnWithLabelDependency(Insn::Goto { targetPc: skipLoopsLabel }, skipLoopsLabel);
            Some(skipLoopsLabel)
        } else {
            None
        };

    // Initialize cursors and other resources needed for query execution
    if let Some(ref mut orderBy) = plan.orderBys {
        initOrderBy(&mut programBuilder, orderBy, &mut metadata)?;
    }

    if let Some(ref mut group_by) = plan.group_by {
        initGroupBy(&mut programBuilder, group_by, &plan.aggregates, &mut metadata)?;
    }

    initSrcOperator(&mut programBuilder, &plan.srcOperator, &mut metadata)?;

    // Set up main query execution loop
    openLoop(&mut programBuilder,
             &mut plan.srcOperator,
             &plan.tblRefs,
             &mut metadata)?;

    // Process result columns and expressions in the inner loop
    inner_loop_emit(&mut programBuilder, &mut plan, &mut metadata)?;

    // Clean up and close the main execution loop
    close_loop(&mut programBuilder,
               &plan.srcOperator,
               &mut metadata,
               &plan.tblRefs)?;

    if let Some(skipLoopsLabel) = skipLoopsLabel {
        programBuilder.resolveLabel(skipLoopsLabel, programBuilder.nextPc());
    }

    let mut order_by_necessary = plan.orderBys.is_some() && !plan.containsConstantFalseCondition;

    // Handle GROUP BY and aggregation processing
    if let Some(ref mut group_by) = plan.group_by {
        group_by_emit(&mut programBuilder,
                      &plan.resultCols,
                      group_by,
                      plan.orderBys.as_ref(),
                      &plan.aggregates,
                      plan.limit,
                      &plan.tblRefs,
                      &mut metadata)?;
    } else if !plan.aggregates.is_empty() {
        // Handle aggregation without GROUP BY
        agg_without_group_by_emit(&mut programBuilder,
                                  &plan.tblRefs,
                                  &plan.resultCols,
                                  &plan.aggregates,
                                  &mut metadata)?;

        // Single row result for aggregates without GROUP BY, so ORDER BY not needed
        order_by_necessary = false;
    }

    // Process ORDER BY results if needed
    if let Some(ref mut order_by) = plan.orderBys {
        if order_by_necessary {
            order_by_emit(&mut programBuilder,
                          order_by,
                          &plan.resultCols,
                          plan.limit,
                          &mut metadata)?;
        }
    }

    // finalize program
    epilogue(&mut programBuilder, &mut metadata, initLabel, startOffset)?;

    Ok(programBuilder.build(dbHeader, conn))
}

/// Initialize resources needed for ORDER BY processing
fn initOrderBy(program: &mut ProgramBuilder,
               order_by: &[(ast::Expr, Direction)],
               metadata: &mut Metadata) -> Result<()> {
    metadata
        .terminationLabelStack
        .push(program.allocateLabel());
    let sort_cursor = program.allocCursorId(None, None);
    metadata.sort_metadata = Some(SortMetadata {
        sort_cursor,
        sorter_data_register: program.allocRegister(),
    });
    let mut order = Vec::new();
    for (_, direction) in order_by.iter() {
        order.push(OwnedValue::Integer(*direction as i64));
    }
    program.addInsn0(Insn::SorterOpen {
        cursor_id: sort_cursor,
        columns: order_by.len(),
        order: OwnedRecord::new(order),
    });
    Ok(())
}

/// Initialize resources needed for GROUP BY processing
fn initGroupBy(
    program: &mut ProgramBuilder,
    group_by: &GroupBy,
    aggregates: &[Aggregate],
    metadata: &mut Metadata,
) -> Result<()> {
    let agg_final_label = program.allocateLabel();
    metadata.terminationLabelStack.push(agg_final_label);
    let num_aggs = aggregates.len();

    let sort_cursor = program.allocCursorId(None, None);

    let abort_flag_register = program.allocRegister();
    let data_in_accumulator_indicator_register = program.allocRegister();
    let group_exprs_comparison_register = program.allocRegisters(group_by.exprs.len());
    let group_exprs_accumulator_register = program.allocRegisters(group_by.exprs.len());
    let agg_exprs_start_reg = program.allocRegisters(num_aggs);
    let sorter_key_register = program.allocRegister();

    let subroutine_accumulator_clear_label = program.allocateLabel();
    let subroutine_accumulator_output_label = program.allocateLabel();

    let mut order = Vec::new();
    const ASCENDING: i64 = 0;
    for _ in group_by.exprs.iter() {
        order.push(OwnedValue::Integer(ASCENDING));
    }
    program.addInsn0(Insn::SorterOpen {
        cursor_id: sort_cursor,
        columns: aggregates.len() + group_by.exprs.len(),
        order: OwnedRecord::new(order),
    });

    program.add_comment(program.nextPc(), "clear group by abort flag");
    program.addInsn0(Insn::Integer {
        value: 0,
        destReg: abort_flag_register,
    });

    program.add_comment(
        program.nextPc(),
        "initialize group by comparison registers to NULL",
    );
    program.addInsn0(Insn::Null {
        dest: group_exprs_comparison_register,
        dest_end: if group_by.exprs.len() > 1 {
            Some(group_exprs_comparison_register + group_by.exprs.len() - 1)
        } else {
            None
        },
    });

    program.add_comment(program.nextPc(), "go to clear accumulator subroutine");

    let subroutine_accumulator_clear_return_offset_register = program.allocRegister();
    program.addInsnWithLabelDependency(
        Insn::Gosub {
            target_pc: subroutine_accumulator_clear_label,
            return_reg: subroutine_accumulator_clear_return_offset_register,
        },
        subroutine_accumulator_clear_label,
    );

    metadata.aggregation_start_register = Some(agg_exprs_start_reg);

    metadata.group_by_metadata = Some(GroupByMetadata {
        sort_cursor,
        subroutine_accumulator_clear_label,
        subroutine_accumulator_clear_return_offset_register,
        subroutine_accumulator_output_label,
        subroutine_accumulator_output_return_offset_register: program.allocRegister(),
        accumulator_indicator_set_true_label: program.allocateLabel(),
        abort_flag_register,
        data_in_accumulator_indicator_register,
        group_exprs_accumulator_register,
        group_exprs_comparison_register,
        sorter_key_register,
    });
    Ok(())
}

/// Initialize resources needed for the source operators (tables, joins, etc)
fn initSrcOperator(programBuilder: &mut ProgramBuilder,
                   srcOperator: &SrcOperator,
                   metadata: &mut Metadata) -> Result<()> {
    match srcOperator {
        SrcOperator::Join { id, left, right, outer, .. } => {
            if *outer {
                let lj_metadata = LeftJoinMetadata {
                    match_flag_register: programBuilder.allocRegister(),
                    set_match_flag_true_label: programBuilder.allocateLabel(),
                    check_match_flag_label: programBuilder.allocateLabel(),
                };

                metadata.left_joins.insert(*id, lj_metadata);
            }

            initSrcOperator(programBuilder, left, metadata)?;
            initSrcOperator(programBuilder, right, metadata)?;

            Ok(())
        }
        SrcOperator::Search { id, tblRef, indexSearch: indexSearch, .. } => {
            let cursorIdTbl =
                programBuilder.allocCursorId(Some(tblRef.table_identifier.clone()),
                                             Some(Table::BTree(tblRef.table.clone())));

            metadata.nextRowLabels.insert(*id, programBuilder.allocateLabel());

            programBuilder.addInsn0(Insn::OpenReadAsync {
                cursorId: cursorIdTbl,
                rootPage: tblRef.table.rootPage,
            });

            programBuilder.addInsn0(Insn::OpenReadAwait);

            //------------------------------------------------------------------------

            if let IndexSearch::IndexSearch { index, .. } = indexSearch {
                let cursorIdIndex =
                    programBuilder.allocCursorId(Some(index.name.clone()),
                                                 Some(Table::Index(index.clone())));

                programBuilder.addInsn0(Insn::OpenReadAsync {
                    cursorId: cursorIdIndex,
                    rootPage: index.rootPage,
                });

                programBuilder.addInsn0(Insn::OpenReadAwait);
            }

            Ok(())
        }
        SrcOperator::Scan { id, tblRef, .. } => {
            let cursorIdTbl =
                programBuilder.allocCursorId(Some(tblRef.table_identifier.clone()),
                                             Some(Table::BTree(tblRef.table.clone())));

            metadata.nextRowLabels.insert(*id, programBuilder.allocateLabel());

            programBuilder.addInsn0(Insn::OpenReadAsync {
                cursorId: cursorIdTbl,
                rootPage: tblRef.table.rootPage,
            });

            programBuilder.addInsn0(Insn::OpenReadAwait);

            Ok(())
        }
        SrcOperator::Nothing => Ok(())
    }
}

/// Set up the main query execution loop
/// For example in the case of a nested table scan, this means emitting the RewindAsync instruction
/// for all tables involved, outermost first.
fn openLoop(programBuilder: &mut ProgramBuilder,
            srcOperator: &mut SrcOperator,
            tblRefs: &[BTreeTableRef],
            metadata: &mut Metadata) -> Result<()> {
    match srcOperator {
        SrcOperator::Join {
            id,
            left,
            right,
            predicates,
            outer,
            ..
        } => {
            openLoop(programBuilder, left, tblRefs, metadata)?;

            let mut jumpDestWhenFalse =
                *metadata.nextRowLabels.get(&right.id()).or(metadata.nextRowLabels.get(&left.id())).unwrap_or(metadata.terminationLabelStack.last().unwrap());

            if *outer {
                let lj_meta = metadata.left_joins.get(id).unwrap();
                programBuilder.addInsn0(Insn::Integer {
                    value: 0,
                    destReg: lj_meta.match_flag_register,
                });
                jumpDestWhenFalse = lj_meta.check_match_flag_label;
            }

            metadata.nextRowLabels.insert(right.id(), jumpDestWhenFalse);

            openLoop(programBuilder, right, tblRefs, metadata)?;

            if let Some(predicates) = predicates {
                let jump_target_when_true = programBuilder.allocateLabel();
                let condition_metadata = ConditionMetadata {
                    jump_if_condition_is_true: false,
                    jump_target_when_true,
                    jump_target_when_false: jumpDestWhenFalse,
                };
                for predicate in predicates.iter() {
                    translate_condition_expr(
                        programBuilder,
                        tblRefs,
                        predicate,
                        condition_metadata,
                        None,
                    )?;
                }
                programBuilder.resolveLabel(jump_target_when_true, programBuilder.nextPc());
            }

            if *outer {
                let lj_meta = metadata.left_joins.get(id).unwrap();
                programBuilder.defer_label_resolution(
                    lj_meta.set_match_flag_true_label,
                    programBuilder.nextPc() as usize,
                );
                programBuilder.addInsn0(Insn::Integer {
                    value: 1,
                    destReg: lj_meta.match_flag_register,
                });
            }

            Ok(())
        }
        SrcOperator::Search { id, tblRef, indexSearch, predicates, .. } => {
            let tblCursorId = programBuilder.resolveCursorId(&tblRef.table_identifier);

            // Open the loop for the index search.
            // Rowid equality point lookups are handled with a SeekRowid instruction which does not loop, since it is a single row lookup.
            if !matches!(indexSearch, IndexSearch::RowidEq { .. }) {
                let index_cursor_id = if let IndexSearch::IndexSearch { index, .. } = indexSearch {
                    Some(programBuilder.resolveCursorId(&index.name))
                } else {
                    None
                };

                let scanLoopBodyLabel = programBuilder.allocateLabel();
                metadata.scanLoopBodyLabels.push(scanLoopBodyLabel);

                let cmpRegister = programBuilder.allocRegister();

                let (cmp_expr, cmp_op) = match indexSearch {
                    IndexSearch::IndexSearch { cmp_expr, cmp_op, .. } => (cmp_expr, cmp_op),
                    IndexSearch::RowidSearch { cmp_expr, cmp_op } => (cmp_expr, cmp_op),
                    IndexSearch::RowidEq { .. } => unreachable!(),
                };

                // TODO this only handles ascending indexes
                match cmp_op {
                    ast::Operator::Equals | ast::Operator::Greater | ast::Operator::GreaterEquals => _ = expr::translateExpr(programBuilder, Some(tblRefs), cmp_expr, cmpRegister, None)?,
                    ast::Operator::Less | ast::Operator::LessEquals => programBuilder.addInsn0(Insn::Null { dest: cmpRegister, dest_end: None }),
                    _ => unreachable!(),
                }

                programBuilder.addInsnWithLabelDependency(
                    match cmp_op {
                        ast::Operator::Equals | ast::Operator::GreaterEquals =>
                            Insn::SeekGE {
                                is_index: index_cursor_id.is_some(),
                                cursor_id: index_cursor_id.unwrap_or(tblCursorId),
                                start_reg: cmpRegister,
                                num_regs: 1,
                                target_pc: *metadata.terminationLabelStack.last().unwrap(),
                            },
                        ast::Operator::Greater | ast::Operator::Less | ast::Operator::LessEquals =>
                            Insn::SeekGT {
                                is_index: index_cursor_id.is_some(),
                                cursor_id: index_cursor_id.unwrap_or(tblCursorId),
                                start_reg: cmpRegister,
                                num_regs: 1,
                                target_pc: *metadata.terminationLabelStack.last().unwrap(),
                            },
                        _ => unreachable!(),
                    },
                    *metadata.terminationLabelStack.last().unwrap(),
                );

                if *cmp_op == ast::Operator::Less || *cmp_op == ast::Operator::LessEquals {
                    expr::translateExpr(programBuilder, Some(tblRefs), cmp_expr, cmpRegister, None)?;
                }

                programBuilder.defer_label_resolution(scanLoopBodyLabel, programBuilder.nextPc() as usize);

                // TODO: We are currently only handling ascending indexes.
                // For conditions like index_key > 10, we have already seeked to the first key greater than 10, and can just scan forward.
                // For conditions like index_key < 10, we are at the beginning of the index, and will scan forward and emit IdxGE(10) with a conditional jump to the end.
                // For conditions like index_key = 10, we have already seeked to the first key greater than or equal to 10, and can just scan forward and emit IdxGT(10) with a conditional jump to the end.
                // For conditions like index_key >= 10, we have already seeked to the first key greater than or equal to 10, and can just scan forward.
                // For conditions like index_key <= 10, we are at the beginning of the index, and will scan forward and emit IdxGT(10) with a conditional jump to the end.
                // For conditions like index_key != 10, TODO. probably the optimal way is not to use an index at all.
                //
                // For primary key searches we emit RowId and then compare it to the seek value.

                let abort_jump_target = *metadata.nextRowLabels.get(id).unwrap_or(metadata.terminationLabelStack.last().unwrap());

                match cmp_op {
                    ast::Operator::Equals | ast::Operator::LessEquals => {
                        if let Some(index_cursor_id) = index_cursor_id {
                            programBuilder.addInsnWithLabelDependency(
                                Insn::IdxGT {
                                    cursor_id: index_cursor_id,
                                    start_reg: cmpRegister,
                                    num_regs: 1,
                                    target_pc: abort_jump_target,
                                },
                                abort_jump_target,
                            );
                        } else {
                            let rowid_reg = programBuilder.allocRegister();
                            programBuilder.addInsn0(Insn::RowId {
                                cursor_id: tblCursorId,
                                dest: rowid_reg,
                            });
                            programBuilder.addInsnWithLabelDependency(
                                Insn::Gt {
                                    lhs: rowid_reg,
                                    rhs: cmpRegister,
                                    target_pc: abort_jump_target,
                                },
                                abort_jump_target,
                            );
                        }
                    }
                    ast::Operator::Less => {
                        if let Some(index_cursor_id) = index_cursor_id {
                            programBuilder.addInsnWithLabelDependency(
                                Insn::IdxGE {
                                    cursor_id: index_cursor_id,
                                    start_reg: cmpRegister,
                                    num_regs: 1,
                                    target_pc: abort_jump_target,
                                },
                                abort_jump_target,
                            );
                        } else {
                            let rowid_reg = programBuilder.allocRegister();
                            programBuilder.addInsn0(Insn::RowId {
                                cursor_id: tblCursorId,
                                dest: rowid_reg,
                            });
                            programBuilder.addInsnWithLabelDependency(
                                Insn::Ge {
                                    lhs: rowid_reg,
                                    rhs: cmpRegister,
                                    target_pc: abort_jump_target,
                                },
                                abort_jump_target,
                            );
                        }
                    }
                    _ => {}
                }

                if let Some(index_cursor_id) = index_cursor_id {
                    programBuilder.addInsn0(Insn::DeferredSeek {
                        index_cursor_id,
                        table_cursor_id: tblCursorId,
                    });
                }
            }

            let jump_label = metadata.nextRowLabels.get(id).unwrap();

            if let IndexSearch::RowidEq { cmp_expr } = indexSearch {
                let srcReg = programBuilder.allocRegister();

                expr::translateExpr(programBuilder, Some(tblRefs), cmp_expr, srcReg, None)?;

                programBuilder.addInsnWithLabelDependency(
                    Insn::SeekRowid {
                        cursor_id: tblCursorId,
                        srcReg,
                        target_pc: *jump_label,
                    },
                    *jump_label,
                );
            }

            if let Some(whereExprs) = predicates {
                for predicate in whereExprs.iter() {
                    let jump_target_when_true = programBuilder.allocateLabel();

                    let condition_metadata = ConditionMetadata {
                        jump_if_condition_is_true: false,
                        jump_target_when_true,
                        jump_target_when_false: *jump_label,
                    };

                    translate_condition_expr(
                        programBuilder,
                        tblRefs,
                        predicate,
                        condition_metadata,
                        None,
                    )?;

                    programBuilder.resolveLabel(jump_target_when_true, programBuilder.nextPc());
                }
            }

            Ok(())
        }
        SrcOperator::Scan {
            id,
            tblRef: table_reference,
            whereExprs: predicates,
            iterDirection: iter_dir,
        } => {
            let cursor_id = programBuilder.resolveCursorId(&table_reference.table_identifier);

            if iter_dir.as_ref().is_some_and(|dir| *dir == IterationDirection::Backwards) {
                programBuilder.addInsn0(Insn::LastAsync { cursor_id });
            } else {
                programBuilder.addInsn0(Insn::RewindAsync { cursor_id });
            }

            let scan_loop_body_label = programBuilder.allocateLabel();
            let halt_label = metadata.terminationLabelStack.last().unwrap();
            programBuilder.addInsnWithLabelDependency(
                if iter_dir.as_ref().is_some_and(|dir| *dir == IterationDirection::Backwards) {
                    Insn::LastAwait {
                        cursor_id,
                        pc_if_empty: *halt_label,
                    }
                } else {
                    Insn::RewindAwait {
                        cursor_id,
                        pc_if_empty: *halt_label,
                    }
                },
                *halt_label,
            );

            metadata.scanLoopBodyLabels.push(scan_loop_body_label);
            programBuilder.defer_label_resolution(scan_loop_body_label, programBuilder.nextPc() as usize);

            let jump_label = metadata.nextRowLabels.get(id).unwrap_or(halt_label);

            if let Some(preds) = predicates {
                for expr in preds {
                    let jump_target_when_true = programBuilder.allocateLabel();

                    let condition_metadata = ConditionMetadata {
                        jump_if_condition_is_true: false,
                        jump_target_when_true,
                        jump_target_when_false: *jump_label,
                    };

                    translate_condition_expr(programBuilder,
                                             tblRefs,
                                             expr,
                                             condition_metadata,
                                             None)?;

                    programBuilder.resolveLabel(jump_target_when_true, programBuilder.nextPc());
                }
            }

            Ok(())
        }
        SrcOperator::Nothing => Ok(()),
    }
}

/// SQLite (and so Limbo) processes joins as a nested loop.
/// The inner loop may emit rows to various destinations depending on the query:
/// - a GROUP BY sorter (grouping is done by sorting based on the GROUP BY keys and aggregating while the GROUP BY keys match)
/// - an ORDER BY sorter (when there is no GROUP BY, but there is an ORDER BY)
/// - an AggStep (the columns are collected for aggregation, which is finished later)
/// - a ResultRow (there is none of the above, so the loop emits a result row directly)
pub enum InnerLoopEmitTarget<'a> {
    GroupBySorter {
        group_by: &'a GroupBy,
        aggregates: &'a Vec<Aggregate>,
    },
    OrderBySorter {
        order_by: &'a Vec<(ast::Expr, Direction)>,
    },
    AggStep,
    ResultRow {
        limit: Option<usize>,
    },
}

/// Emits the bytecode for the inner loop of a query.
/// At this point the cursors for all tables have been opened and rewound.
fn inner_loop_emit(
    program: &mut ProgramBuilder,
    plan: &mut Plan,
    metadata: &mut Metadata,
) -> Result<()> {
    // if we have a group by, we emit a record into the group by sorter.
    if let Some(group_by) = &plan.group_by {
        return inner_loop_source_emit(
            program,
            &plan.resultCols,
            &plan.aggregates,
            metadata,
            InnerLoopEmitTarget::GroupBySorter {
                group_by,
                aggregates: &plan.aggregates,
            },
            &plan.tblRefs,
        );
    }
    // if we DONT have a group by, but we have aggregates, we emit without ResultRow.
    // we also do not need to sort because we are emitting a single row.
    if !plan.aggregates.is_empty() {
        return inner_loop_source_emit(
            program,
            &plan.resultCols,
            &plan.aggregates,
            metadata,
            InnerLoopEmitTarget::AggStep,
            &plan.tblRefs,
        );
    }
    // if we DONT have a group by, but we have an order by, we emit a record into the order by sorter.
    if let Some(order_by) = &plan.orderBys {
        return inner_loop_source_emit(
            program,
            &plan.resultCols,
            &plan.aggregates,
            metadata,
            InnerLoopEmitTarget::OrderBySorter { order_by },
            &plan.tblRefs,
        );
    }
    // if we have neither, we emit a ResultRow. In that case, if we have a Limit, we handle that with DecrJumpZero.
    return inner_loop_source_emit(
        program,
        &plan.resultCols,
        &plan.aggregates,
        metadata,
        InnerLoopEmitTarget::ResultRow { limit: plan.limit },
        &plan.tblRefs,
    );
}

/// This is a helper function for inner_loop_emit,
/// which does a different thing depending on the emit target.
/// See the InnerLoopEmitTarget enum for more details.
fn inner_loop_source_emit(
    program: &mut ProgramBuilder,
    result_columns: &[ResultSetColumn],
    aggregates: &[Aggregate],
    metadata: &mut Metadata,
    emit_target: InnerLoopEmitTarget,
    referenced_tables: &[BTreeTableRef],
) -> Result<()> {
    match emit_target {
        InnerLoopEmitTarget::GroupBySorter {
            group_by,
            aggregates,
        } => {
            let sort_keys_count = group_by.exprs.len();
            let aggregate_arguments_count =
                aggregates.iter().map(|agg| agg.args.len()).sum::<usize>();
            let column_count = sort_keys_count + aggregate_arguments_count;
            let start_reg = program.allocRegisters(column_count);
            let mut cur_reg = start_reg;

            // The group by sorter rows will contain the grouping keys first. They are also the sort keys.
            for expr in group_by.exprs.iter() {
                let key_reg = cur_reg;
                cur_reg += 1;
                expr::translateExpr(program, Some(referenced_tables), expr, key_reg, None)?;
            }
            // Then we have the aggregate arguments.
            for agg in aggregates.iter() {
                // Here we are collecting scalars for the group by sorter, which will include
                // both the group by expressions and the aggregate arguments.
                // e.g. in `select u.first_name, sum(u.age) from users group by u.first_name`
                // the sorter will have two scalars: u.first_name and u.age.
                // these are then sorted by u.first_name, and for each u.first_name, we sum the u.age.
                // the actual aggregation is done later.
                for expr in agg.args.iter() {
                    let agg_reg = cur_reg;
                    cur_reg += 1;
                    expr::translateExpr(program, Some(referenced_tables), expr, agg_reg, None)?;
                }
            }

            // TODO: although it's less often useful, SQLite does allow for expressions in the SELECT that are not part of a GROUP BY or aggregate.
            // We currently ignore those and only emit the GROUP BY keys and aggregate arguments. This should be fixed.

            let group_by_metadata = metadata.group_by_metadata.as_ref().unwrap();

            sorter_insert(
                program,
                start_reg,
                column_count,
                group_by_metadata.sort_cursor,
                group_by_metadata.sorter_key_register,
            );

            Ok(())
        }
        InnerLoopEmitTarget::OrderBySorter { order_by } => {
            order_by_sorter_insert(
                program,
                referenced_tables,
                order_by,
                result_columns,
                &mut metadata.result_column_indexes_in_orderby_sorter,
                metadata.sort_metadata.as_ref().unwrap(),
                None,
            )?;
            Ok(())
        }
        InnerLoopEmitTarget::AggStep => {
            let agg_final_label = program.allocateLabel();
            metadata.terminationLabelStack.push(agg_final_label);
            let num_aggs = aggregates.len();
            let start_reg = program.allocRegisters(num_aggs);
            metadata.aggregation_start_register = Some(start_reg);

            // In planner.rs, we have collected all aggregates from the SELECT clause, including ones where the aggregate is embedded inside
            // a more complex expression. Some examples: length(sum(x)), sum(x) + avg(y), sum(x) + 1, etc.
            // The result of those more complex expressions depends on the final result of the aggregate, so we don't translate the complete expressions here.
            // Instead, we translate the aggregates + any expressions that do not contain aggregates.
            for (i, agg) in aggregates.iter().enumerate() {
                let reg = start_reg + i;
                translate_aggregation(program, referenced_tables, agg, reg)?;
            }
            for (i, rc) in result_columns.iter().enumerate() {
                if rc.contains_aggregates {
                    // Do nothing, aggregates are computed above
                    // if this result column is e.g. something like sum(x) + 1 or length(sum(x)), we do not want to translate that (+1) or length() yet,
                    // it will be computed after the aggregations are finalized.
                    continue;
                }
                let reg = start_reg + num_aggs + i;
                expr::translateExpr(program, Some(referenced_tables), &rc.expr, reg, None)?;
            }
            Ok(())
        }
        InnerLoopEmitTarget::ResultRow { limit } => {
            assert!(
                aggregates.is_empty(),
                "We should not get here with aggregates"
            );
            emit_select_result(
                program,
                referenced_tables,
                result_columns,
                None,
                limit.map(|l| (l, *metadata.terminationLabelStack.last().unwrap())),
            )?;

            Ok(())
        }
    }
}

/// Closes the loop for a given source operator.
/// For example in the case of a nested table scan, this means emitting the NextAsync instruction
/// for all tables involved, innermost first.
fn close_loop(program: &mut ProgramBuilder,
              source: &SrcOperator,
              metadata: &mut Metadata,
              referenced_tables: &[BTreeTableRef]) -> Result<()> {
    match source {
        SrcOperator::Join {
            id,
            left,
            right,
            outer,
            ..
        } => {
            close_loop(program, right, metadata, referenced_tables)?;

            if *outer {
                let lj_meta = metadata.left_joins.get(id).unwrap();
                // The left join match flag is set to 1 when there is any match on the right table
                // (e.g. SELECT * FROM t1 LEFT JOIN t2 ON t1.a = t2.a).
                // If the left join match flag has been set to 1, we jump to the next row on the outer table,
                // i.e. continue to the next row of t1 in our example.
                program.resolveLabel(lj_meta.check_match_flag_label, program.nextPc());
                let jump_offset = program.nextPc() + 3;
                program.addInsn0(Insn::IfPos {
                    reg: lj_meta.match_flag_register,
                    target_pc: jump_offset,
                    decrement_by: 0,
                });
                // If the left join match flag is still 0, it means there was no match on the right table,
                // but since it's a LEFT JOIN, we still need to emit a row with NULLs for the right table.
                // In that case, we now enter the routine that does exactly that.
                // First we set the right table cursor's "pseudo null bit" on, which means any Insn::Column will return NULL
                let right_cursor_id = match right.as_ref() {
                    SrcOperator::Scan {
                        tblRef: table_reference, ..
                    } => program.resolveCursorId(&table_reference.table_identifier),
                    SrcOperator::Search {
                        tblRef: table_reference, ..
                    } => program.resolveCursorId(&table_reference.table_identifier),
                    _ => unreachable!(),
                };
                program.addInsn0(Insn::NullRow {
                    cursor_id: right_cursor_id,
                });
                // Then we jump to setting the left join match flag to 1 again,
                // but this time the right table cursor will set everything to null.
                // This leads to emitting a row with cols from the left + nulls from the right,
                // and we will end up back in the IfPos instruction above, which will then
                // check the match flag again, and since it is now 1, we will jump to the
                // next row in the left table.
                program.addInsnWithLabelDependency(
                    Insn::Goto {
                        targetPc: lj_meta.set_match_flag_true_label,
                    },
                    lj_meta.set_match_flag_true_label,
                );

                assert!(program.nextPc() == jump_offset);
            }

            close_loop(program, left, metadata, referenced_tables)?;

            Ok(())
        }
        SrcOperator::Scan {
            id,
            tblRef: table_reference,
            iterDirection: iter_dir,
            ..
        } => {
            let cursor_id = program.resolveCursorId(&table_reference.table_identifier);
            program.resolveLabel(*metadata.nextRowLabels.get(id).unwrap(), program.nextPc());
            if iter_dir.as_ref().is_some_and(|dir| *dir == IterationDirection::Backwards) {
                program.addInsn0(Insn::PrevAsync { cursor_id });
            } else {
                program.addInsn0(Insn::NextAsync { cursor_id });
            }

            let jump_label = metadata.scanLoopBodyLabels.pop().unwrap();

            if iter_dir.as_ref().is_some_and(|dir| *dir == IterationDirection::Backwards) {
                program.addInsnWithLabelDependency(
                    Insn::PrevAwait {
                        cursor_id,
                        pc_if_next: jump_label,
                    },
                    jump_label,
                );
            } else {
                program.addInsnWithLabelDependency(
                    Insn::NextAwait {
                        cursor_id,
                        pc_if_next: jump_label,
                    },
                    jump_label,
                );
            }

            Ok(())
        }
        SrcOperator::Search {
            id,
            tblRef: table_reference,
            indexSearch: search,
            ..
        } => {
            program.resolveLabel(*metadata.nextRowLabels.get(id).unwrap(), program.nextPc());
            if matches!(search, IndexSearch::RowidEq { .. }) {
                // Rowid equality point lookups are handled with a SeekRowid instruction which does not loop, so there is no need to emit a NextAsync instruction.
                return Ok(());
            }
            let cursor_id = match search {
                IndexSearch::IndexSearch { index, .. } => program.resolveCursorId(&index.name),
                IndexSearch::RowidSearch { .. } => {
                    program.resolveCursorId(&table_reference.table_identifier)
                }
                IndexSearch::RowidEq { .. } => unreachable!(),
            };

            program.addInsn0(Insn::NextAsync { cursor_id });
            let jump_label = metadata.scanLoopBodyLabels.pop().unwrap();
            program.addInsnWithLabelDependency(
                Insn::NextAwait {
                    cursor_id,
                    pc_if_next: jump_label,
                },
                jump_label,
            );

            Ok(())
        }
        SrcOperator::Nothing => Ok(()),
    }
}

/// Emits the bytecode for processing a GROUP BY clause.
/// This is called when the main query execution loop has finished processing,
/// and we now have data in the GROUP BY sorter.
#[allow(clippy::too_many_arguments)]
fn group_by_emit(
    program: &mut ProgramBuilder,
    result_columns: &[ResultSetColumn],
    group_by: &GroupBy,
    order_by: Option<&Vec<(ast::Expr, Direction)>>,
    aggregates: &[Aggregate],
    limit: Option<usize>,
    referenced_tables: &[BTreeTableRef],
    metadata: &mut Metadata,
) -> Result<()> {
    let sort_loop_start_label = program.allocateLabel();
    let grouping_done_label = program.allocateLabel();
    let group_by_metadata = metadata.group_by_metadata.as_mut().unwrap();

    let GroupByMetadata {
        group_exprs_comparison_register: comparison_register,
        subroutine_accumulator_output_return_offset_register,
        subroutine_accumulator_output_label,
        subroutine_accumulator_clear_return_offset_register,
        subroutine_accumulator_clear_label,
        data_in_accumulator_indicator_register,
        accumulator_indicator_set_true_label,
        group_exprs_accumulator_register: group_exprs_start_register,
        abort_flag_register,
        sorter_key_register,
        ..
    } = *group_by_metadata;
    let halt_label = *metadata.terminationLabelStack.first().unwrap();

    // all group by columns and all arguments of agg functions are in the sorter.
    // the sort keys are the group by columns (the aggregation within groups is done based on how long the sort keys remain the same)
    let sorter_column_count =
        group_by.exprs.len() + aggregates.iter().map(|agg| agg.args.len()).sum::<usize>();
    // sorter column names do not matter
    let pseudo_columns = (0..sorter_column_count)
        .map(|i| Column {
            name: i.to_string(),
            primary_key: false,
            columnType: crate::schema::ColumnType::Null,
            is_rowid_alias: false,
        })
        .collect::<Vec<_>>();

    // A pseudo table is a "fake" table to which we read one row at a time from the sorter
    let pseudo_table = Rc::new(PseudoTable {
        columns: pseudo_columns,
    });

    let pseudo_cursor = program.allocCursorId(None, Some(Table::Pseudo(pseudo_table.clone())));

    program.addInsn0(Insn::OpenPseudo {
        cursor_id: pseudo_cursor,
        content_reg: sorter_key_register,
        num_fields: sorter_column_count,
    });

    // Sort the sorter based on the group by columns
    program.addInsnWithLabelDependency(
        Insn::SorterSort {
            cursor_id: group_by_metadata.sort_cursor,
            pc_if_empty: grouping_done_label,
        },
        grouping_done_label,
    );

    program.defer_label_resolution(sort_loop_start_label, program.nextPc() as usize);
    // Read a row from the sorted data in the sorter into the pseudo cursor
    program.addInsn0(Insn::SorterData {
        cursor_id: group_by_metadata.sort_cursor,
        dest_reg: group_by_metadata.sorter_key_register,
        pseudo_cursor,
    });

    // Read the group by columns from the pseudo cursor
    let groups_start_reg = program.allocRegisters(group_by.exprs.len());
    for i in 0..group_by.exprs.len() {
        let sorter_column_index = i;
        let group_reg = groups_start_reg + i;
        program.addInsn0(Insn::Column {
            cursor_id: pseudo_cursor,
            column: sorter_column_index,
            destReg: group_reg,
        });
    }

    // Compare the group by columns to the previous group by columns to see if we are at a new group or not
    program.addInsn0(Insn::Compare {
        start_reg_a: comparison_register,
        start_reg_b: groups_start_reg,
        count: group_by.exprs.len(),
    });

    let agg_step_label = program.allocateLabel();

    program.add_comment(
        program.nextPc(),
        "start new group if comparison is not equal",
    );
    // If we are at a new group, continue. If we are at the same group, jump to the aggregation step (i.e. accumulate more values into the aggregations)
    program.addInsnWithLabelDependency(
        Insn::Jump {
            target_pc_lt: program.nextPc() + 1,
            target_pc_eq: agg_step_label,
            target_pc_gt: program.nextPc() + 1,
        },
        agg_step_label,
    );

    // New group, move current group by columns into the comparison register
    program.addInsn0(Insn::Move {
        source_reg: groups_start_reg,
        dest_reg: comparison_register,
        count: group_by.exprs.len(),
    });

    program.add_comment(
        program.nextPc(),
        "check if ended group had data, and output if so",
    );
    program.addInsnWithLabelDependency(
        Insn::Gosub {
            target_pc: subroutine_accumulator_output_label,
            return_reg: subroutine_accumulator_output_return_offset_register,
        },
        subroutine_accumulator_output_label,
    );

    program.add_comment(program.nextPc(), "check abort flag");
    program.addInsnWithLabelDependency(
        Insn::IfPos {
            reg: abort_flag_register,
            target_pc: halt_label,
            decrement_by: 0,
        },
        metadata.terminationLabelStack[0],
    );

    program.add_comment(program.nextPc(), "goto clear accumulator subroutine");
    program.addInsnWithLabelDependency(
        Insn::Gosub {
            target_pc: subroutine_accumulator_clear_label,
            return_reg: subroutine_accumulator_clear_return_offset_register,
        },
        subroutine_accumulator_clear_label,
    );

    // Accumulate the values into the aggregations
    program.resolveLabel(agg_step_label, program.nextPc());
    let start_reg = metadata.aggregation_start_register.unwrap();
    let mut cursor_index = group_by.exprs.len();
    for (i, agg) in aggregates.iter().enumerate() {
        let agg_result_reg = start_reg + i;
        translate_aggregation_groupby(
            program,
            referenced_tables,
            pseudo_cursor,
            cursor_index,
            agg,
            agg_result_reg,
        )?;
        cursor_index += agg.args.len();
    }

    // We only emit the group by columns if we are going to start a new group (i.e. the prev group will not accumulate any more values into the aggregations)
    program.add_comment(
        program.nextPc(),
        "don't emit group columns if continuing existing group",
    );
    program.addInsnWithLabelDependency(
        Insn::If {
            target_pc: accumulator_indicator_set_true_label,
            reg: data_in_accumulator_indicator_register,
            null_reg: 0, // unused in this case
        },
        accumulator_indicator_set_true_label,
    );

    // Read the group by columns for a finished group
    for i in 0..group_by.exprs.len() {
        let key_reg = group_exprs_start_register + i;
        let sorter_column_index = i;
        program.addInsn0(Insn::Column {
            cursor_id: pseudo_cursor,
            column: sorter_column_index,
            destReg: key_reg,
        });
    }

    program.resolveLabel(accumulator_indicator_set_true_label, program.nextPc());
    program.add_comment(program.nextPc(), "indicate data in accumulator");
    program.addInsn0(Insn::Integer {
        value: 1,
        destReg: data_in_accumulator_indicator_register,
    });

    program.addInsnWithLabelDependency(
        Insn::SorterNext {
            cursor_id: group_by_metadata.sort_cursor,
            pc_if_next: sort_loop_start_label,
        },
        sort_loop_start_label,
    );

    program.resolveLabel(grouping_done_label, program.nextPc());

    program.add_comment(program.nextPc(), "emit row for final group");
    program.addInsnWithLabelDependency(
        Insn::Gosub {
            target_pc: group_by_metadata.subroutine_accumulator_output_label,
            return_reg: group_by_metadata.subroutine_accumulator_output_return_offset_register,
        },
        group_by_metadata.subroutine_accumulator_output_label,
    );

    program.add_comment(program.nextPc(), "group by finished");
    let termination_label =
        metadata.terminationLabelStack[metadata.terminationLabelStack.len() - 2];
    program.addInsnWithLabelDependency(
        Insn::Goto {
            targetPc: termination_label,
        },
        termination_label,
    );
    program.addInsn0(Insn::Integer {
        value: 1,
        destReg: group_by_metadata.abort_flag_register,
    });
    program.addInsn0(Insn::Return {
        return_reg: group_by_metadata.subroutine_accumulator_output_return_offset_register,
    });

    program.resolveLabel(
        group_by_metadata.subroutine_accumulator_output_label,
        program.nextPc(),
    );

    program.add_comment(program.nextPc(), "output group by row subroutine start");
    let termination_label = *metadata.terminationLabelStack.last().unwrap();
    program.addInsnWithLabelDependency(
        Insn::IfPos {
            reg: group_by_metadata.data_in_accumulator_indicator_register,
            target_pc: termination_label,
            decrement_by: 0,
        },
        termination_label,
    );
    let group_by_end_without_emitting_row_label = program.allocateLabel();
    program.defer_label_resolution(
        group_by_end_without_emitting_row_label,
        program.nextPc() as usize,
    );
    program.addInsn0(Insn::Return {
        return_reg: group_by_metadata.subroutine_accumulator_output_return_offset_register,
    });

    let agg_start_reg = metadata.aggregation_start_register.unwrap();
    program.resolveLabel(
        metadata.terminationLabelStack.pop().unwrap(),
        program.nextPc(),
    );
    for (i, agg) in aggregates.iter().enumerate() {
        let agg_result_reg = agg_start_reg + i;
        program.addInsn0(Insn::AggFinal {
            register: agg_result_reg,
            func: agg.func.clone(),
        });
    }

    // we now have the group by columns in registers (group_exprs_start_register..group_exprs_start_register + group_by.len() - 1)
    // and the agg results in (agg_start_reg..agg_start_reg + aggregates.len() - 1)
    // we need to call translate_expr on each result column, but replace the expr with a register copy in case any part of the
    // result column expression matches a) a group by column or b) an aggregation result.
    let mut precomputed_exprs_to_register =
        Vec::with_capacity(aggregates.len() + group_by.exprs.len());
    for (i, expr) in group_by.exprs.iter().enumerate() {
        precomputed_exprs_to_register.push((expr, group_exprs_start_register + i));
    }
    for (i, agg) in aggregates.iter().enumerate() {
        precomputed_exprs_to_register.push((&agg.original_expr, agg_start_reg + i));
    }

    if let Some(having) = &group_by.having {
        for expr in having.iter() {
            translate_condition_expr(
                program,
                referenced_tables,
                expr,
                ConditionMetadata {
                    jump_if_condition_is_true: false,
                    jump_target_when_false: group_by_end_without_emitting_row_label,
                    jump_target_when_true: i64::MAX, // unused
                },
                Some(&precomputed_exprs_to_register),
            )?;
        }
    }

    match order_by {
        None => {
            emit_select_result(
                program,
                referenced_tables,
                result_columns,
                Some(&precomputed_exprs_to_register),
                limit.map(|l| (l, *metadata.terminationLabelStack.last().unwrap())),
            )?;
        }
        Some(order_by) => {
            order_by_sorter_insert(
                program,
                referenced_tables,
                order_by,
                result_columns,
                &mut metadata.result_column_indexes_in_orderby_sorter,
                metadata.sort_metadata.as_ref().unwrap(),
                Some(&precomputed_exprs_to_register),
            )?;
        }
    }

    program.addInsn0(Insn::Return {
        return_reg: group_by_metadata.subroutine_accumulator_output_return_offset_register,
    });

    program.add_comment(program.nextPc(), "clear accumulator subroutine start");
    program.resolveLabel(
        group_by_metadata.subroutine_accumulator_clear_label,
        program.nextPc(),
    );
    let start_reg = group_by_metadata.group_exprs_accumulator_register;
    program.addInsn0(Insn::Null {
        dest: start_reg,
        dest_end: Some(start_reg + group_by.exprs.len() + aggregates.len() - 1),
    });

    program.addInsn0(Insn::Integer {
        value: 0,
        destReg: group_by_metadata.data_in_accumulator_indicator_register,
    });
    program.addInsn0(Insn::Return {
        return_reg: group_by_metadata.subroutine_accumulator_clear_return_offset_register,
    });

    Ok(())
}

/// Emits the bytecode for processing an aggregate without a GROUP BY clause.
/// This is called when the main query execution loop has finished processing,
/// and we can now materialize the aggregate results.
fn agg_without_group_by_emit(
    program: &mut ProgramBuilder,
    referenced_tables: &[BTreeTableRef],
    result_columns: &[ResultSetColumn],
    aggregates: &[Aggregate],
    metadata: &mut Metadata,
) -> Result<()> {
    let agg_start_reg = metadata.aggregation_start_register.unwrap();
    for (i, agg) in aggregates.iter().enumerate() {
        let agg_result_reg = agg_start_reg + i;
        program.addInsn0(Insn::AggFinal {
            register: agg_result_reg,
            func: agg.func.clone(),
        });
    }
    // we now have the agg results in (agg_start_reg..agg_start_reg + aggregates.len() - 1)
    // we need to call translate_expr on each result column, but replace the expr with a register copy in case any part of the
    // result column expression matches a) a group by column or b) an aggregation result.
    let mut precomputed_exprs_to_register = Vec::with_capacity(aggregates.len());
    for (i, agg) in aggregates.iter().enumerate() {
        precomputed_exprs_to_register.push((&agg.original_expr, agg_start_reg + i));
    }

    // This always emits a ResultRow because currently it can only be used for a single row result
    // Limit is None because we early exit on limit 0 and the max rows here is 1
    emit_select_result(
        program,
        referenced_tables,
        result_columns,
        Some(&precomputed_exprs_to_register),
        None,
    )?;

    Ok(())
}

/// Emits the bytecode for outputting rows from an ORDER BY sorter.
/// This is called when the main query execution loop has finished processing,
/// and we can now emit rows from the ORDER BY sorter.
fn order_by_emit(
    program: &mut ProgramBuilder,
    order_by: &[(ast::Expr, Direction)],
    result_columns: &[ResultSetColumn],
    limit: Option<usize>,
    metadata: &mut Metadata,
) -> Result<()> {
    let sort_loop_start_label = program.allocateLabel();
    let sort_loop_end_label = program.allocateLabel();
    program.resolveLabel(
        metadata.terminationLabelStack.pop().unwrap(),
        program.nextPc(),
    );
    let mut pseudo_columns = vec![];
    for (i, _) in order_by.iter().enumerate() {
        pseudo_columns.push(Column {
            // Names don't matter. We are tracking which result column is in which position in the ORDER BY clause in m.result_column_indexes_in_orderby_sorter.
            name: format!("sort_key_{}", i),
            primary_key: false,
            columnType: crate::schema::ColumnType::Null,
            is_rowid_alias: false,
        });
    }
    for (i, rc) in result_columns.iter().enumerate() {
        // If any result columns are not in the ORDER BY sorter, it's because they are equal to a sort key and were already added to the pseudo columns above.
        if let Some(ref v) = metadata.result_columns_to_skip_in_orderby_sorter {
            if v.contains(&i) {
                continue;
            }
        }
        pseudo_columns.push(Column {
            name: rc.expr.to_string(),
            primary_key: false,
            columnType: crate::schema::ColumnType::Null,
            is_rowid_alias: false,
        });
    }

    let num_columns_in_sorter = order_by.len() + result_columns.len()
        - metadata
        .result_columns_to_skip_in_orderby_sorter
        .as_ref()
        .map(|v| v.len())
        .unwrap_or(0);

    let pseudo_cursor = program.allocCursorId(
        None,
        Some(Table::Pseudo(Rc::new(PseudoTable {
            columns: pseudo_columns,
        }))),
    );
    let sort_metadata = metadata.sort_metadata.as_mut().unwrap();

    program.addInsn0(Insn::OpenPseudo {
        cursor_id: pseudo_cursor,
        content_reg: sort_metadata.sorter_data_register,
        num_fields: num_columns_in_sorter,
    });

    program.addInsnWithLabelDependency(
        Insn::SorterSort {
            cursor_id: sort_metadata.sort_cursor,
            pc_if_empty: sort_loop_end_label,
        },
        sort_loop_end_label,
    );

    program.defer_label_resolution(sort_loop_start_label, program.nextPc() as usize);
    program.addInsn0(Insn::SorterData {
        cursor_id: sort_metadata.sort_cursor,
        dest_reg: sort_metadata.sorter_data_register,
        pseudo_cursor,
    });

    // We emit the columns in SELECT order, not sorter order (sorter always has the sort keys first).
    // This is tracked in m.result_column_indexes_in_orderby_sorter.
    let cursor_id = pseudo_cursor;
    let start_reg = program.allocRegisters(result_columns.len());
    for i in 0..result_columns.len() {
        let reg = start_reg + i;
        program.addInsn0(Insn::Column {
            cursor_id,
            column: metadata.result_column_indexes_in_orderby_sorter[&i],
            destReg: reg,
        });
    }
    emit_result_row_and_limit(
        program,
        start_reg,
        result_columns.len(),
        limit.map(|l| (l, sort_loop_end_label)),
    )?;

    program.addInsnWithLabelDependency(
        Insn::SorterNext {
            cursor_id: sort_metadata.sort_cursor,
            pc_if_next: sort_loop_start_label,
        },
        sort_loop_start_label,
    );

    program.resolveLabel(sort_loop_end_label, program.nextPc());

    Ok(())
}

/// Emits the bytecode for: result row and limit.
fn emit_result_row_and_limit(
    program: &mut ProgramBuilder,
    start_reg: usize,
    result_columns_len: usize,
    limit: Option<(usize, BranchOffset)>,
) -> Result<()> {
    program.addInsn0(Insn::ResultRow {
        start_reg,
        count: result_columns_len,
    });
    if let Some((limit, jump_label_on_limit_reached)) = limit {
        let limit_reg = program.allocRegister();
        program.addInsn0(Insn::Integer {
            value: limit as i64,
            destReg: limit_reg,
        });
        program.mark_last_insn_constant();
        program.addInsnWithLabelDependency(
            Insn::DecrJumpZero {
                reg: limit_reg,
                target_pc: jump_label_on_limit_reached,
            },
            jump_label_on_limit_reached,
        );
    }
    Ok(())
}

/// Emits the bytecode for: all result columns, result row, and limit.
fn emit_select_result(
    program: &mut ProgramBuilder,
    referenced_tables: &[BTreeTableRef],
    result_columns: &[ResultSetColumn],
    precomputed_exprs_to_register: Option<&Vec<(&ast::Expr, usize)>>,
    limit: Option<(usize, BranchOffset)>,
) -> Result<()> {
    let start_reg = program.allocRegisters(result_columns.len());
    for (i, rc) in result_columns.iter().enumerate() {
        let reg = start_reg + i;
        expr::translateExpr(
            program,
            Some(referenced_tables),
            &rc.expr,
            reg,
            precomputed_exprs_to_register,
        )?;
    }
    emit_result_row_and_limit(program, start_reg, result_columns.len(), limit)?;
    Ok(())
}

/// Emits the bytecode for inserting a row into a sorter.
/// This can be either a GROUP BY sorter or an ORDER BY sorter.
fn sorter_insert(
    program: &mut ProgramBuilder,
    start_reg: usize,
    column_count: usize,
    cursor_id: usize,
    record_reg: usize,
) {
    program.addInsn0(Insn::MakeRecord {
        startReg: start_reg,
        count: column_count,
        destReg: record_reg,
    });
    program.addInsn0(Insn::SorterInsert {
        cursor_id,
        record_reg,
    });
}

/// Emits the bytecode for inserting a row into an ORDER BY sorter.
fn order_by_sorter_insert(
    program: &mut ProgramBuilder,
    referenced_tables: &[BTreeTableRef],
    order_by: &[(ast::Expr, Direction)],
    result_columns: &[ResultSetColumn],
    result_column_indexes_in_orderby_sorter: &mut HashMap<usize, usize>,
    sort_metadata: &SortMetadata,
    precomputed_exprs_to_register: Option<&Vec<(&ast::Expr, usize)>>,
) -> Result<()> {
    let order_by_len = order_by.len();
    // If any result columns can be skipped due to being an exact duplicate of a sort key, we need to know which ones and their new index in the ORDER BY sorter.
    let result_columns_to_skip = order_by_deduplicate_result_columns(order_by, result_columns);
    let result_columns_to_skip_len = result_columns_to_skip
        .as_ref()
        .map(|v| v.len())
        .unwrap_or(0);

    // The ORDER BY sorter has the sort keys first, then the result columns.
    let orderby_sorter_column_count =
        order_by_len + result_columns.len() - result_columns_to_skip_len;
    let start_reg = program.allocRegisters(orderby_sorter_column_count);
    for (i, (expr, _)) in order_by.iter().enumerate() {
        let key_reg = start_reg + i;
        expr::translateExpr(
            program,
            Some(referenced_tables),
            expr,
            key_reg,
            precomputed_exprs_to_register,
        )?;
    }
    let mut cur_reg = start_reg + order_by_len;
    let mut cur_idx_in_orderby_sorter = order_by_len;
    for (i, rc) in result_columns.iter().enumerate() {
        if let Some(ref v) = result_columns_to_skip {
            let found = v.iter().find(|(skipped_idx, _)| *skipped_idx == i);
            // If the result column is in the list of columns to skip, we need to know its new index in the ORDER BY sorter.
            if let Some((_, result_column_idx)) = found {
                result_column_indexes_in_orderby_sorter.insert(i, *result_column_idx);
                continue;
            }
        }
        expr::translateExpr(
            program,
            Some(referenced_tables),
            &rc.expr,
            cur_reg,
            precomputed_exprs_to_register,
        )?;
        result_column_indexes_in_orderby_sorter.insert(i, cur_idx_in_orderby_sorter);
        cur_idx_in_orderby_sorter += 1;
        cur_reg += 1;
    }

    sorter_insert(
        program,
        start_reg,
        orderby_sorter_column_count,
        sort_metadata.sort_cursor,
        sort_metadata.sorter_data_register,
    );
    Ok(())
}

/// In case any of the ORDER BY sort keys are exactly equal to a result column, we can skip emitting that result column.
/// If we skip a result column, we need to keep track what index in the ORDER BY sorter the result columns have,
/// because the result columns should be emitted in the SELECT clause order, not the ORDER BY clause order.
///
/// If any result columns can be skipped, this returns list of 2-tuples of (SkippedResultColumnIndex: usize, ResultColumnIndexInOrderBySorter: usize)
fn order_by_deduplicate_result_columns(
    order_by: &[(ast::Expr, Direction)],
    result_columns: &[ResultSetColumn],
) -> Option<Vec<(usize, usize)>> {
    let mut result_column_remapping: Option<Vec<(usize, usize)>> = None;
    for (i, rc) in result_columns.iter().enumerate() {
        let found = order_by
            .iter()
            .enumerate()
            .find(|(_, (expr, _))| exprs_are_equivalent(expr, &rc.expr));
        if let Some((j, _)) = found {
            if let Some(ref mut v) = result_column_remapping {
                v.push((i, j));
            } else {
                result_column_remapping = Some(vec![(i, j)]);
            }
        }
    }

    result_column_remapping
}
