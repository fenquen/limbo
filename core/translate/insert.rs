use std::rc::Weak;
use std::{cell::RefCell, ops::Deref, rc::Rc};

use sqlite3_parser::ast::{
    DistinctNames, InsertBody, QualifiedName, ResolveType, ResultColumn, With,
};

use crate::error::SQLITE_CONSTRAINT_PRIMARYKEY;
use crate::{
    schema::{Schema, Table},
    storage::sqlite3_ondisk::DbHeader,
    translate::expr::translateExpr,
    vdbe::{program_builder::ProgramBuilder, Insn, Program},
};
use crate::{Conn, Result};

#[allow(clippy::too_many_arguments)]
pub fn translateInsert(schema: &Schema,
                       tblName: &QualifiedName,
                       _columns: &Option<DistinctNames>,
                       body: &InsertBody,
                       _returning: &Option<Vec<ResultColumn>>,
                       database_header: Rc<RefCell<DbHeader>>,
                       connection: Weak<Conn>) -> Result<Program> {
    let mut programBuilder = ProgramBuilder::new();

    let initLabel = programBuilder.allocateLabel();

    programBuilder.addInsnWithLabelDependency(Insn::Init { target_pc: initLabel }, initLabel);

    let startPc = programBuilder.nextPc();

    let tblName = tblName.name.0.to_owned();

    let table = match schema.getTbl(&tblName) {
        Some(table) => Rc::new(Table::BTree(table)),
        None => crate::bail_corrupt_error!("Parse error: no such table: {}", tblName),
    };

    let cursorId = programBuilder.allocCursorId(Some(tblName), Some(table.clone().deref().clone()));

    let rootPage = match table.as_ref() {
        Table::BTree(btreeTbl) => btreeTbl.rootPage,
        Table::Index(index) => index.rootPage,
        Table::Pseudo(_) => todo!(),
    };

    let colCount = {
        let mut colCount = table.columns().len();

        if table.hasRowId() {
            colCount += 1;
        }

        colCount
    };

    // column_registers_start[0] == rowid if has rowid
    let colRegStart = programBuilder.allocRegisters(colCount);

    // Coroutine for values
    let yieldReg = programBuilder.allocRegister();
    let jump_on_definition_label = programBuilder.allocateLabel();
    {
        programBuilder.addInsnWithLabelDependency(
            Insn::InitCoroutine {
                yieldReg,
                jump_on_definition: jump_on_definition_label,
                start_offset: programBuilder.nextPc() + 1,
            },
            jump_on_definition_label,
        );

        match body {
            // insert into select 的
            InsertBody::Select(select, None) => match &select.body.select {
                sqlite3_parser::ast::OneSelect::Values(valVecVec) => {
                    for valVec in valVecVec {
                        for (col, expr) in valVec.iter().enumerate() {
                            let col = {
                                if table.hasRowId() {
                                    col + 1
                                } else {
                                    col
                                }
                            };

                            translateExpr(&mut programBuilder, None, expr, colRegStart + col, None)?;
                        }

                        programBuilder.addInsn0(Insn::Yield { yieldReg, end_offset: 0 });
                    }
                }
                _ => todo!()
            },
            _ => todo!(),
        }

        programBuilder.addInsn0(Insn::EndCoroutine { yieldReg });
    }

    programBuilder.resolveLabel(jump_on_definition_label, programBuilder.nextPc());

    programBuilder.addInsn0(Insn::OpenWriteAsync { cursorId, rootPage });
    programBuilder.addInsn0(Insn::OpenWriteAwait {});

    // Main loop
    let recReg = programBuilder.allocRegister();

    let haltLabel = programBuilder.allocateLabel();

    let loopStartPc = programBuilder.nextPc();

    programBuilder.addInsnWithLabelDependency(Insn::Yield {
        yieldReg,
        end_offset: haltLabel,
    }, haltLabel);

    if table.hasRowId() {
        let rowIdReg = colRegStart;

        if let Some(rowid_alias_column) = table.get_rowid_alias_column() {
            let key_reg = colRegStart + 1 + rowid_alias_column.0;
            // copy key to rowid
            programBuilder.addInsn0(Insn::Copy {
                src_reg: key_reg,
                dst_reg: rowIdReg,
                amount: 0,
            });
            programBuilder.addInsn0(Insn::SoftNull { reg: key_reg });
        }

        let notnull_label = programBuilder.allocateLabel();
        programBuilder.addInsnWithLabelDependency(
            Insn::NotNull {
                reg: rowIdReg,
                target_pc: notnull_label,
            },
            notnull_label,
        );

        programBuilder.addInsn0(Insn::NewRowid {
            cursorId,
            rowid_reg: rowIdReg,
            prev_largest_reg: 0,
        });

        programBuilder.resolveLabel(notnull_label, programBuilder.nextPc());

        programBuilder.addInsn0(Insn::MustBeInt { reg: rowIdReg });

        let labelMakeRecord = programBuilder.allocateLabel();

        programBuilder.addInsnWithLabelDependency(
            Insn::NotExists {
                cursor: cursorId,
                rowid_reg: rowIdReg,
                target_pc: labelMakeRecord,
            },
            labelMakeRecord,
        );

        // TODO: rollback
        programBuilder.addInsn0(Insn::Halt {
            err_code: SQLITE_CONSTRAINT_PRIMARYKEY,
            description: format!("{}.{}", table.get_name(), table.column_index_to_name(0).unwrap()),
        });

        programBuilder.resolveLabel(labelMakeRecord, programBuilder.nextPc());

        programBuilder.addInsn0(Insn::MakeRecord {
            startReg: colRegStart + 1,
            count: colCount - 1,
            destReg: recReg,
        });

        programBuilder.addInsn0(Insn::InsertAsync {
            cursorId,
            keyReg: colRegStart,
            recReg,
            flag: 0,
        });

        programBuilder.addInsn0(Insn::InsertAwait { cursor_id: cursorId });
    }

    // 循环loop的
    programBuilder.addInsn0(Insn::Goto { targetPc: loopStartPc });

    programBuilder.resolveLabel(haltLabel, programBuilder.nextPc());

    programBuilder.addInsn0(Insn::Halt { err_code: 0, description: String::new() });

    programBuilder.resolveLabel(initLabel, programBuilder.nextPc());

    programBuilder.addInsn0(Insn::Transaction { write: true });

    programBuilder.emit_constant_insns();

    // 实现了循环效果
    programBuilder.addInsn0(Insn::Goto { targetPc: startPc });

    programBuilder.resolve_deferred_labels();

    Ok(programBuilder.build(database_header, connection))
}
