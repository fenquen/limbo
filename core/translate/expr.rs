use sqlite3_parser::ast::{self, UnaryOperator};

#[cfg(feature = "json")]
use crate::function::JsonFunc;
use crate::function::{AggFunc, Func, FuncCtx, MathFuncArity, ScalarFunc};
use crate::schema::ColumnType;
use crate::util::normalize_ident;
use crate::vdbe::{program_builder::ProgramBuilder, BranchOffset, Insn};
use crate::Result;

use super::plan::{Aggregate, BTreeTableRef};

#[derive(Default, Debug, Clone, Copy)]
pub struct ConditionMetadata {
    pub jump_if_condition_is_true: bool,
    pub jump_target_when_true: BranchOffset,
    pub jump_target_when_false: BranchOffset,
}

pub fn translate_condition_expr(program: &mut ProgramBuilder,
                                referenced_tables: &[BTreeTableRef],
                                expr: &ast::Expr,
                                condition_metadata: ConditionMetadata,
                                precomputed_exprs_to_registers: Option<&Vec<(&ast::Expr, usize)>>) -> Result<()> {
    match expr {
        ast::Expr::Between { .. } => todo!(),
        ast::Expr::Binary(lhs, ast::Operator::And, rhs) => {
            // In a binary AND, never jump to the 'jump_target_when_true' label on the first condition, because
            // the second condition must also be true.
            let _ = translate_condition_expr(
                program,
                referenced_tables,
                lhs,
                ConditionMetadata {
                    jump_if_condition_is_true: false,
                    ..condition_metadata
                },
                precomputed_exprs_to_registers,
            );
            let _ = translate_condition_expr(
                program,
                referenced_tables,
                rhs,
                condition_metadata,
                precomputed_exprs_to_registers,
            );
        }
        ast::Expr::Binary(lhs, ast::Operator::Or, rhs) => {
            let jump_target_when_false = program.allocateLabel();
            let _ = translate_condition_expr(
                program,
                referenced_tables,
                lhs,
                ConditionMetadata {
                    // If the first condition is true, we don't need to evaluate the second condition.
                    jump_if_condition_is_true: true,
                    jump_target_when_false,
                    ..condition_metadata
                },
                precomputed_exprs_to_registers,
            );
            program.resolveLabel(jump_target_when_false, program.nextPc());
            let _ = translate_condition_expr(
                program,
                referenced_tables,
                rhs,
                condition_metadata,
                precomputed_exprs_to_registers,
            );
        }
        ast::Expr::Binary(lhs, op, rhs) => {
            let lhs_reg = program.allocRegister();
            let _ = translateExpr(
                program,
                Some(referenced_tables),
                lhs,
                lhs_reg,
                precomputed_exprs_to_registers,
            );
            if let ast::Expr::Literal(_) = lhs.as_ref() {
                program.mark_last_insn_constant()
            }
            let rhs_reg = program.allocRegister();
            let _ = translateExpr(
                program,
                Some(referenced_tables),
                rhs,
                rhs_reg,
                precomputed_exprs_to_registers,
            );
            if let ast::Expr::Literal(_) = rhs.as_ref() {
                program.mark_last_insn_constant()
            }
            match op {
                ast::Operator::Greater => {
                    if condition_metadata.jump_if_condition_is_true {
                        program.addInsnWithLabelDependency(
                            Insn::Gt {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_true,
                            },
                            condition_metadata.jump_target_when_true,
                        )
                    } else {
                        program.addInsnWithLabelDependency(
                            Insn::Le {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_false,
                            },
                            condition_metadata.jump_target_when_false,
                        )
                    }
                }
                ast::Operator::GreaterEquals => {
                    if condition_metadata.jump_if_condition_is_true {
                        program.addInsnWithLabelDependency(
                            Insn::Ge {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_true,
                            },
                            condition_metadata.jump_target_when_true,
                        )
                    } else {
                        program.addInsnWithLabelDependency(
                            Insn::Lt {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_false,
                            },
                            condition_metadata.jump_target_when_false,
                        )
                    }
                }
                ast::Operator::Less => {
                    if condition_metadata.jump_if_condition_is_true {
                        program.addInsnWithLabelDependency(
                            Insn::Lt {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_true,
                            },
                            condition_metadata.jump_target_when_true,
                        )
                    } else {
                        program.addInsnWithLabelDependency(
                            Insn::Ge {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_false,
                            },
                            condition_metadata.jump_target_when_false,
                        )
                    }
                }
                ast::Operator::LessEquals => {
                    if condition_metadata.jump_if_condition_is_true {
                        program.addInsnWithLabelDependency(
                            Insn::Le {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_true,
                            },
                            condition_metadata.jump_target_when_true,
                        )
                    } else {
                        program.addInsnWithLabelDependency(
                            Insn::Gt {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_false,
                            },
                            condition_metadata.jump_target_when_false,
                        )
                    }
                }
                ast::Operator::Equals => {
                    if condition_metadata.jump_if_condition_is_true {
                        program.addInsnWithLabelDependency(
                            Insn::Eq {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_true,
                            },
                            condition_metadata.jump_target_when_true,
                        )
                    } else {
                        program.addInsnWithLabelDependency(
                            Insn::Ne {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_false,
                            },
                            condition_metadata.jump_target_when_false,
                        )
                    }
                }
                ast::Operator::NotEquals => {
                    if condition_metadata.jump_if_condition_is_true {
                        program.addInsnWithLabelDependency(
                            Insn::Ne {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_true,
                            },
                            condition_metadata.jump_target_when_true,
                        )
                    } else {
                        program.addInsnWithLabelDependency(
                            Insn::Eq {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_false,
                            },
                            condition_metadata.jump_target_when_false,
                        )
                    }
                }
                ast::Operator::Is => todo!(),
                ast::Operator::IsNot => todo!(),
                _ => {
                    todo!("op {:?} not implemented", op);
                }
            }
        }
        ast::Expr::Literal(lit) => match lit {
            ast::Literal::Numeric(val) => {
                let maybe_int = val.parse::<i64>();
                if let Ok(int_value) = maybe_int {
                    let reg = program.allocRegister();
                    program.addInsn0(Insn::Integer {
                        value: int_value,
                        destReg: reg,
                    });
                    if condition_metadata.jump_if_condition_is_true {
                        program.addInsnWithLabelDependency(
                            Insn::If {
                                reg,
                                target_pc: condition_metadata.jump_target_when_true,
                                null_reg: reg,
                            },
                            condition_metadata.jump_target_when_true,
                        )
                    } else {
                        program.addInsnWithLabelDependency(
                            Insn::IfNot {
                                reg,
                                target_pc: condition_metadata.jump_target_when_false,
                                null_reg: reg,
                            },
                            condition_metadata.jump_target_when_false,
                        )
                    }
                } else {
                    crate::bail_parse_error!("unsupported literal type in condition");
                }
            }
            ast::Literal::String(string) => {
                let reg = program.allocRegister();
                program.addInsn0(Insn::String8 {
                    value: string.clone(),
                    dest: reg,
                });
                if condition_metadata.jump_if_condition_is_true {
                    program.addInsnWithLabelDependency(
                        Insn::If {
                            reg,
                            target_pc: condition_metadata.jump_target_when_true,
                            null_reg: reg,
                        },
                        condition_metadata.jump_target_when_true,
                    )
                } else {
                    program.addInsnWithLabelDependency(
                        Insn::IfNot {
                            reg,
                            target_pc: condition_metadata.jump_target_when_false,
                            null_reg: reg,
                        },
                        condition_metadata.jump_target_when_false,
                    )
                }
            }
            unimpl => todo!("literal {:?} not implemented", unimpl),
        },
        ast::Expr::InList { lhs, not, rhs } => {
            // lhs is e.g. a column reference
            // rhs is an Option<Vec<Expr>>
            // If rhs is None, it means the IN expression is always false, i.e. tbl.id IN ().
            // If rhs is Some, it means the IN expression has a list of values to compare against, e.g. tbl.id IN (1, 2, 3).
            //
            // The IN expression is equivalent to a series of OR expressions.
            // For example, `a IN (1, 2, 3)` is equivalent to `a = 1 OR a = 2 OR a = 3`.
            // The NOT IN expression is equivalent to a series of AND expressions.
            // For example, `a NOT IN (1, 2, 3)` is equivalent to `a != 1 AND a != 2 AND a != 3`.
            //
            // SQLite typically optimizes IN expressions to use a binary search on an ephemeral index if there are many values.
            // For now we don't have the plumbing to do that, so we'll just emit a series of comparisons,
            // which is what SQLite also does for small lists of values.
            // TODO: Let's refactor this later to use a more efficient implementation conditionally based on the number of values.

            if rhs.is_none() {
                // If rhs is None, IN expressions are always false and NOT IN expressions are always true.
                if *not {
                    // On a trivially true NOT IN () expression we can only jump to the 'jump_target_when_true' label if 'jump_if_condition_is_true'; otherwise me must fall through.
                    // This is because in a more complex condition we might need to evaluate the rest of the condition.
                    // Note that we are already breaking up our WHERE clauses into a series of terms at "AND" boundaries, so right now we won't be running into cases where jumping on true would be incorrect,
                    // but once we have e.g. parenthesization and more complex conditions, not having this 'if' here would introduce a bug.
                    if condition_metadata.jump_if_condition_is_true {
                        program.addInsnWithLabelDependency(
                            Insn::Goto {
                                targetPc: condition_metadata.jump_target_when_true,
                            },
                            condition_metadata.jump_target_when_true,
                        );
                    }
                } else {
                    program.addInsnWithLabelDependency(
                        Insn::Goto {
                            targetPc: condition_metadata.jump_target_when_false,
                        },
                        condition_metadata.jump_target_when_false,
                    );
                }
                return Ok(());
            }

            // The left hand side only needs to be evaluated once we have a list of values to compare against.
            let lhs_reg = program.allocRegister();
            let _ = translateExpr(
                program,
                Some(referenced_tables),
                lhs,
                lhs_reg,
                precomputed_exprs_to_registers,
            )?;

            let rhs = rhs.as_ref().unwrap();

            // The difference between a local jump and an "upper level" jump is that for example in this case:
            // WHERE foo IN (1,2,3) OR bar = 5,
            // we can immediately jump to the 'jump_target_when_true' label of the ENTIRE CONDITION if foo = 1, foo = 2, or foo = 3 without evaluating the bar = 5 condition.
            // This is why in Binary-OR expressions we set jump_if_condition_is_true to true for the first condition.
            // However, in this example:
            // WHERE foo IN (1,2,3) AND bar = 5,
            // we can't jump to the 'jump_target_when_true' label of the entire condition foo = 1, foo = 2, or foo = 3, because we still need to evaluate the bar = 5 condition later.
            // This is why in that case we just jump over the rest of the IN conditions in this "local" branch which evaluates the IN condition.
            let jump_target_when_true = if condition_metadata.jump_if_condition_is_true {
                condition_metadata.jump_target_when_true
            } else {
                program.allocateLabel()
            };

            if !*not {
                // If it's an IN expression, we need to jump to the 'jump_target_when_true' label if any of the conditions are true.
                for (i, expr) in rhs.iter().enumerate() {
                    let rhs_reg = program.allocRegister();
                    let last_condition = i == rhs.len() - 1;
                    let _ = translateExpr(
                        program,
                        Some(referenced_tables),
                        expr,
                        rhs_reg,
                        precomputed_exprs_to_registers,
                    )?;
                    // If this is not the last condition, we need to jump to the 'jump_target_when_true' label if the condition is true.
                    if !last_condition {
                        program.addInsnWithLabelDependency(
                            Insn::Eq {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: jump_target_when_true,
                            },
                            jump_target_when_true,
                        );
                    } else {
                        // If this is the last condition, we need to jump to the 'jump_target_when_false' label if there is no match.
                        program.addInsnWithLabelDependency(
                            Insn::Ne {
                                lhs: lhs_reg,
                                rhs: rhs_reg,
                                target_pc: condition_metadata.jump_target_when_false,
                            },
                            condition_metadata.jump_target_when_false,
                        );
                    }
                }
                // If we got here, then the last condition was a match, so we jump to the 'jump_target_when_true' label if 'jump_if_condition_is_true'.
                // If not, we can just fall through without emitting an unnecessary instruction.
                if condition_metadata.jump_if_condition_is_true {
                    program.addInsnWithLabelDependency(
                        Insn::Goto {
                            targetPc: condition_metadata.jump_target_when_true,
                        },
                        condition_metadata.jump_target_when_true,
                    );
                }
            } else {
                // If it's a NOT IN expression, we need to jump to the 'jump_target_when_false' label if any of the conditions are true.
                for expr in rhs.iter() {
                    let rhs_reg = program.allocRegister();
                    let _ = translateExpr(
                        program,
                        Some(referenced_tables),
                        expr,
                        rhs_reg,
                        precomputed_exprs_to_registers,
                    )?;
                    program.addInsnWithLabelDependency(
                        Insn::Eq {
                            lhs: lhs_reg,
                            rhs: rhs_reg,
                            target_pc: condition_metadata.jump_target_when_false,
                        },
                        condition_metadata.jump_target_when_false,
                    );
                }
                // If we got here, then none of the conditions were a match, so we jump to the 'jump_target_when_true' label if 'jump_if_condition_is_true'.
                // If not, we can just fall through without emitting an unnecessary instruction.
                if condition_metadata.jump_if_condition_is_true {
                    program.addInsnWithLabelDependency(
                        Insn::Goto {
                            targetPc: condition_metadata.jump_target_when_true,
                        },
                        condition_metadata.jump_target_when_true,
                    );
                }
            }

            if !condition_metadata.jump_if_condition_is_true {
                program.resolveLabel(jump_target_when_true, program.nextPc());
            }
        }
        ast::Expr::Like {
            lhs,
            not,
            op,
            rhs,
            escape: _,
        } => {
            let cur_reg = program.allocRegister();
            match op {
                ast::LikeOperator::Like | ast::LikeOperator::Glob => {
                    let pattern_reg = program.allocRegister();
                    let column_reg = program.allocRegister();
                    let mut constant_mask = 0;
                    let _ = translateExpr(
                        program,
                        Some(referenced_tables),
                        lhs,
                        column_reg,
                        precomputed_exprs_to_registers,
                    )?;
                    if let ast::Expr::Literal(_) = lhs.as_ref() {
                        program.mark_last_insn_constant();
                    }
                    let _ = translateExpr(
                        program,
                        Some(referenced_tables),
                        rhs,
                        pattern_reg,
                        precomputed_exprs_to_registers,
                    )?;
                    if let ast::Expr::Literal(_) = rhs.as_ref() {
                        program.mark_last_insn_constant();
                        constant_mask = 1;
                    }
                    let func = match op {
                        ast::LikeOperator::Like => ScalarFunc::Like,
                        ast::LikeOperator::Glob => ScalarFunc::Glob,
                        _ => unreachable!(),
                    };
                    program.addInsn0(Insn::Function {
                        constant_mask,
                        start_reg: pattern_reg,
                        dest: cur_reg,
                        func: FuncCtx {
                            func: Func::Scalar(func),
                            arg_count: 2,
                        },
                    });
                }
                ast::LikeOperator::Match => todo!(),
                ast::LikeOperator::Regexp => todo!(),
            }
            if !*not {
                if condition_metadata.jump_if_condition_is_true {
                    program.addInsnWithLabelDependency(
                        Insn::If {
                            reg: cur_reg,
                            target_pc: condition_metadata.jump_target_when_true,
                            null_reg: cur_reg,
                        },
                        condition_metadata.jump_target_when_true,
                    );
                } else {
                    program.addInsnWithLabelDependency(
                        Insn::IfNot {
                            reg: cur_reg,
                            target_pc: condition_metadata.jump_target_when_false,
                            null_reg: cur_reg,
                        },
                        condition_metadata.jump_target_when_false,
                    );
                }
            } else if condition_metadata.jump_if_condition_is_true {
                program.addInsnWithLabelDependency(
                    Insn::IfNot {
                        reg: cur_reg,
                        target_pc: condition_metadata.jump_target_when_true,
                        null_reg: cur_reg,
                    },
                    condition_metadata.jump_target_when_true,
                );
            } else {
                program.addInsnWithLabelDependency(
                    Insn::If {
                        reg: cur_reg,
                        target_pc: condition_metadata.jump_target_when_false,
                        null_reg: cur_reg,
                    },
                    condition_metadata.jump_target_when_false,
                );
            }
        }
        ast::Expr::Parenthesized(exprs) => {
            // TODO: this is probably not correct; multiple expressions in a parenthesized expression
            // are reserved for special cases like `(a, b) IN ((1, 2), (3, 4))`.
            for expr in exprs {
                let _ = translate_condition_expr(
                    program,
                    referenced_tables,
                    expr,
                    condition_metadata,
                    precomputed_exprs_to_registers,
                );
            }
        }
        _ => todo!("op {:?} not implemented", expr),
    }
    Ok(())
}

pub fn translateExpr(programBuilder: &mut ProgramBuilder,
                     tblRefs: Option<&[BTreeTableRef]>,
                     expr: &ast::Expr,
                     destReg: usize,
                     precomputed_exprs_to_registers: Option<&Vec<(&ast::Expr, usize)>>) -> Result<usize> {
    if let Some(precomputed_exprs_to_registers) = precomputed_exprs_to_registers {
        for (precomputed_expr, reg) in precomputed_exprs_to_registers.iter() {
            // TODO: implement a custom equality check for expressions
            // there are lots of examples where this breaks, even simple ones like sum(x) != SUM(x)
            if expr == *precomputed_expr {
                programBuilder.addInsn0(Insn::Copy {
                    src_reg: *reg,
                    dst_reg: destReg,
                    amount: 0,
                });
                return Ok(destReg);
            }
        }
    }
    match expr {
        ast::Expr::Literal(literal) => match literal {
            ast::Literal::Numeric(val) => {
                if let Ok(int_value) = val.parse::<i64>() {
                    programBuilder.addInsn0(Insn::Integer { value: int_value, destReg });
                } else { // must be a float
                    programBuilder.addInsn0(Insn::Real { value: val.parse().unwrap(), dest: destReg });
                }

                Ok(destReg)
            }
            ast::Literal::String(s) => {
                programBuilder.addInsn0(Insn::String8 {
                    value: s[1..s.len() - 1].to_string(),
                    dest: destReg,
                });
                Ok(destReg)
            }
            ast::Literal::Blob(s) => {
                let bytes = s.as_bytes().chunks_exact(2).map(|pair| {
                    // We assume that sqlite3-parser has already validated that
                    // the input is valid hex string, thus unwrap is safe.
                    let hex_byte = std::str::from_utf8(pair).unwrap();
                    u8::from_str_radix(hex_byte, 16).unwrap()
                }).collect();

                programBuilder.addInsn0(Insn::Blob { value: bytes, dest: destReg });

                Ok(destReg)
            }
            ast::Literal::Null => {
                programBuilder.addInsn0(Insn::Null { dest: destReg, dest_end: None });
                Ok(destReg)
            }
            _ => todo!(),
        },
        ast::Expr::Binary(e1, op, e2) => {
            let e1_reg = programBuilder.allocRegister();
            translateExpr(
                programBuilder,
                tblRefs,
                e1,
                e1_reg,
                precomputed_exprs_to_registers,
            )?;
            let e2_reg = programBuilder.allocRegister();
            translateExpr(
                programBuilder,
                tblRefs,
                e2,
                e2_reg,
                precomputed_exprs_to_registers,
            )?;

            match op {
                ast::Operator::NotEquals => {
                    let if_true_label = programBuilder.allocateLabel();
                    wrap_eval_jump_expr(
                        programBuilder,
                        Insn::Ne {
                            lhs: e1_reg,
                            rhs: e2_reg,
                            target_pc: if_true_label,
                        },
                        destReg,
                        if_true_label,
                    );
                }
                ast::Operator::Equals => {
                    let if_true_label = programBuilder.allocateLabel();
                    wrap_eval_jump_expr(
                        programBuilder,
                        Insn::Eq {
                            lhs: e1_reg,
                            rhs: e2_reg,
                            target_pc: if_true_label,
                        },
                        destReg,
                        if_true_label,
                    );
                }
                ast::Operator::Less => {
                    let if_true_label = programBuilder.allocateLabel();
                    wrap_eval_jump_expr(
                        programBuilder,
                        Insn::Lt {
                            lhs: e1_reg,
                            rhs: e2_reg,
                            target_pc: if_true_label,
                        },
                        destReg,
                        if_true_label,
                    );
                }
                ast::Operator::LessEquals => {
                    let if_true_label = programBuilder.allocateLabel();
                    wrap_eval_jump_expr(
                        programBuilder,
                        Insn::Le {
                            lhs: e1_reg,
                            rhs: e2_reg,
                            target_pc: if_true_label,
                        },
                        destReg,
                        if_true_label,
                    );
                }
                ast::Operator::Greater => {
                    let if_true_label = programBuilder.allocateLabel();
                    wrap_eval_jump_expr(
                        programBuilder,
                        Insn::Gt {
                            lhs: e1_reg,
                            rhs: e2_reg,
                            target_pc: if_true_label,
                        },
                        destReg,
                        if_true_label,
                    );
                }
                ast::Operator::GreaterEquals => {
                    let if_true_label = programBuilder.allocateLabel();
                    wrap_eval_jump_expr(
                        programBuilder,
                        Insn::Ge {
                            lhs: e1_reg,
                            rhs: e2_reg,
                            target_pc: if_true_label,
                        },
                        destReg,
                        if_true_label,
                    );
                }
                ast::Operator::Add => {
                    programBuilder.addInsn0(Insn::Add {
                        lhs: e1_reg,
                        rhs: e2_reg,
                        dest: destReg,
                    });
                }
                ast::Operator::Subtract => {
                    programBuilder.addInsn0(Insn::Subtract {
                        lhs: e1_reg,
                        rhs: e2_reg,
                        dest: destReg,
                    });
                }
                ast::Operator::Multiply => {
                    programBuilder.addInsn0(Insn::Multiply {
                        lhs: e1_reg,
                        rhs: e2_reg,
                        dest: destReg,
                    });
                }
                ast::Operator::Divide => {
                    programBuilder.addInsn0(Insn::Divide {
                        lhs: e1_reg,
                        rhs: e2_reg,
                        dest: destReg,
                    });
                }
                ast::Operator::BitwiseAnd => {
                    programBuilder.addInsn0(Insn::BitAnd {
                        lhs: e1_reg,
                        rhs: e2_reg,
                        dest: destReg,
                    });
                }
                ast::Operator::BitwiseOr => {
                    programBuilder.addInsn0(Insn::BitOr {
                        lhs: e1_reg,
                        rhs: e2_reg,
                        dest: destReg,
                    });
                }
                other_unimplemented => todo!("{:?}", other_unimplemented),
            }
            Ok(destReg)
        }
        ast::Expr::Case {
            base,
            when_then_pairs,
            else_expr,
        } => {
            // There's two forms of CASE, one which checks a base expression for equality
            // against the WHEN values, and returns the corresponding THEN value if it matches:
            //   CASE 2 WHEN 1 THEN 'one' WHEN 2 THEN 'two' ELSE 'many' END
            // And one which evaluates a series of boolean predicates:
            //   CASE WHEN is_good THEN 'good' WHEN is_bad THEN 'bad' ELSE 'okay' END
            // This just changes which sort of branching instruction to issue, after we
            // generate the expression if needed.
            let return_label = programBuilder.allocateLabel();
            let mut next_case_label = programBuilder.allocateLabel();
            // Only allocate a reg to hold the base expression if one was provided.
            // And base_reg then becomes the flag we check to see which sort of
            // case statement we're processing.
            let base_reg = base.as_ref().map(|_| programBuilder.allocRegister());
            let expr_reg = programBuilder.allocRegister();
            if let Some(base_expr) = base {
                translateExpr(
                    programBuilder,
                    tblRefs,
                    base_expr,
                    base_reg.unwrap(),
                    precomputed_exprs_to_registers,
                )?;
            };
            for (when_expr, then_expr) in when_then_pairs {
                translateExpr(
                    programBuilder,
                    tblRefs,
                    when_expr,
                    expr_reg,
                    precomputed_exprs_to_registers,
                )?;
                match base_reg {
                    // CASE 1 WHEN 0 THEN 0 ELSE 1 becomes 1==0, Ne branch to next clause
                    Some(base_reg) => programBuilder.addInsnWithLabelDependency(
                        Insn::Ne {
                            lhs: base_reg,
                            rhs: expr_reg,
                            target_pc: next_case_label,
                        },
                        next_case_label,
                    ),
                    // CASE WHEN 0 THEN 0 ELSE 1 becomes ifnot 0 branch to next clause
                    None => programBuilder.addInsnWithLabelDependency(
                        Insn::IfNot {
                            reg: expr_reg,
                            target_pc: next_case_label,
                            null_reg: 1,
                        },
                        next_case_label,
                    ),
                };
                // THEN...
                translateExpr(
                    programBuilder,
                    tblRefs,
                    then_expr,
                    destReg,
                    precomputed_exprs_to_registers,
                )?;
                programBuilder.addInsnWithLabelDependency(
                    Insn::Goto {
                        targetPc: return_label,
                    },
                    return_label,
                );
                // This becomes either the next WHEN, or in the last WHEN/THEN, we're
                // assured to have at least one instruction corresponding to the ELSE immediately follow.
                programBuilder.preassignLabelToNextInsn(next_case_label);
                next_case_label = programBuilder.allocateLabel();
            }
            match else_expr {
                Some(expr) => {
                    translateExpr(
                        programBuilder,
                        tblRefs,
                        expr,
                        destReg,
                        precomputed_exprs_to_registers,
                    )?;
                }
                // If ELSE isn't specified, it means ELSE null.
                None => {
                    programBuilder.addInsn0(Insn::Null {
                        dest: destReg,
                        dest_end: None,
                    });
                }
            };
            programBuilder.resolveLabel(return_label, programBuilder.nextPc());
            Ok(destReg)
        }
        ast::Expr::Cast { expr, type_name } => {
            let type_name = type_name.as_ref().unwrap(); // TODO: why is this optional?
            let reg_expr = programBuilder.allocRegister();
            translateExpr(
                programBuilder,
                tblRefs,
                expr,
                reg_expr,
                precomputed_exprs_to_registers,
            )?;
            let reg_type = programBuilder.allocRegister();
            programBuilder.addInsn0(Insn::String8 {
                // we make a comparison against uppercase static strs in the affinity() function,
                // so we need to make sure we're comparing against the uppercase version,
                // and it's better to do this once instead of every time we check affinity
                value: type_name.name.to_uppercase(),
                dest: reg_type,
            });
            programBuilder.mark_last_insn_constant();
            programBuilder.addInsn0(Insn::Function {
                constant_mask: 0,
                start_reg: reg_expr,
                dest: destReg,
                func: FuncCtx {
                    func: Func::Scalar(ScalarFunc::Cast),
                    arg_count: 2,
                },
            });
            Ok(destReg)
        }
        ast::Expr::Collate(_, _) => todo!(),
        ast::Expr::DoublyQualified(_, _, _) => todo!(),
        ast::Expr::Exists(_) => todo!(),
        ast::Expr::FunctionCall {
            name,
            distinctness: _,
            args,
            filter_over: _,
            order_by: _,
        } => {
            let args_count = if let Some(args) = args { args.len() } else { 0 };
            let func_type: Option<Func> =
                Func::resolve_function(normalize_ident(name.0.as_str()).as_str(), args_count).ok();

            if func_type.is_none() {
                crate::bail_parse_error!("unknown function {}", name.0);
            }

            let func_ctx = FuncCtx {
                func: func_type.unwrap(),
                arg_count: args_count,
            };

            match &func_ctx.func {
                Func::Agg(_) => {
                    crate::bail_parse_error!("aggregation function in non-aggregation context")
                }
                #[cfg(feature = "json")]
                Func::Json(j) => match j {
                    JsonFunc::Json => {
                        let args = if let Some(args) = args {
                            if args.len() != 1 {
                                crate::bail_parse_error!(
                                    "{} function with not exactly 1 argument",
                                    j.to_string()
                                );
                            }
                            args
                        } else {
                            crate::bail_parse_error!(
                                "{} function with no arguments",
                                j.to_string()
                            );
                        };
                        let regs = programBuilder.allocRegister();
                        translateExpr(
                            programBuilder,
                            tblRefs,
                            &args[0],
                            regs,
                            precomputed_exprs_to_registers,
                        )?;
                        programBuilder.addInsn0(Insn::Function {
                            constant_mask: 0,
                            start_reg: regs,
                            dest: destReg,
                            func: func_ctx,
                        });
                        Ok(destReg)
                    }
                },
                Func::Scalar(srf) => {
                    match srf {
                        ScalarFunc::Cast => {
                            unreachable!("this is always ast::Expr::Cast")
                        }
                        ScalarFunc::Char => {
                            let args = args.clone().unwrap_or_else(Vec::new);

                            for arg in args.iter() {
                                let reg = programBuilder.allocRegister();
                                translateExpr(
                                    programBuilder,
                                    tblRefs,
                                    arg,
                                    reg,
                                    precomputed_exprs_to_registers,
                                )?;
                            }

                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: destReg + 1,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Coalesce => {
                            let args = if let Some(args) = args {
                                if args.len() < 2 {
                                    crate::bail_parse_error!(
                                        "{} function with less than 2 arguments",
                                        srf.to_string()
                                    );
                                }
                                args
                            } else {
                                crate::bail_parse_error!(
                                    "{} function with no arguments",
                                    srf.to_string()
                                );
                            };

                            // coalesce function is implemented as a series of not null checks
                            // whenever a not null check succeeds, we jump to the end of the series
                            let label_coalesce_end = programBuilder.allocateLabel();
                            for (index, arg) in args.iter().enumerate() {
                                let reg = translateExpr(
                                    programBuilder,
                                    tblRefs,
                                    arg,
                                    destReg,
                                    precomputed_exprs_to_registers,
                                )?;
                                if index < args.len() - 1 {
                                    programBuilder.addInsnWithLabelDependency(
                                        Insn::NotNull {
                                            reg,
                                            target_pc: label_coalesce_end,
                                        },
                                        label_coalesce_end,
                                    );
                                }
                            }
                            programBuilder.preassignLabelToNextInsn(label_coalesce_end);

                            Ok(destReg)
                        }
                        ScalarFunc::LastInsertRowid => {
                            let regs = programBuilder.allocRegister();
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: regs,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Concat => {
                            let args = if let Some(args) = args {
                                args
                            } else {
                                crate::bail_parse_error!(
                                    "{} function with no arguments",
                                    srf.to_string()
                                );
                            };
                            let mut start_reg = None;
                            for arg in args.iter() {
                                let reg = programBuilder.allocRegister();
                                start_reg = Some(start_reg.unwrap_or(reg));
                                translateExpr(
                                    programBuilder,
                                    tblRefs,
                                    arg,
                                    reg,
                                    precomputed_exprs_to_registers,
                                )?;
                            }
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: start_reg.unwrap(),
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::ConcatWs => {
                            let args = match args {
                                Some(args) if args.len() >= 2 => args,
                                Some(_) => crate::bail_parse_error!(
                                    "{} function requires at least 2 arguments",
                                    srf.to_string()
                                ),
                                None => crate::bail_parse_error!(
                                    "{} function requires arguments",
                                    srf.to_string()
                                ),
                            };

                            let temp_register = programBuilder.allocRegister();
                            for arg in args.iter() {
                                let reg = programBuilder.allocRegister();
                                translateExpr(
                                    programBuilder,
                                    tblRefs,
                                    arg,
                                    reg,
                                    precomputed_exprs_to_registers,
                                )?;
                            }
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: temp_register + 1,
                                dest: temp_register,
                                func: func_ctx,
                            });

                            programBuilder.addInsn0(Insn::Copy {
                                src_reg: temp_register,
                                dst_reg: destReg,
                                amount: 1,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::IfNull => {
                            let args = match args {
                                Some(args) if args.len() == 2 => args,
                                Some(_) => crate::bail_parse_error!(
                                    "{} function requires exactly 2 arguments",
                                    srf.to_string()
                                ),
                                None => crate::bail_parse_error!(
                                    "{} function requires arguments",
                                    srf.to_string()
                                ),
                            };

                            let temp_reg = programBuilder.allocRegister();
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[0],
                                temp_reg,
                                precomputed_exprs_to_registers,
                            )?;
                            programBuilder.addInsn0(Insn::NotNull {
                                reg: temp_reg,
                                target_pc: programBuilder.nextPc() + 2,
                            });

                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[1],
                                temp_reg,
                                precomputed_exprs_to_registers,
                            )?;
                            programBuilder.addInsn0(Insn::Copy {
                                src_reg: temp_reg,
                                dst_reg: destReg,
                                amount: 0,
                            });

                            Ok(destReg)
                        }
                        ScalarFunc::Iif => {
                            let args = match args {
                                Some(args) if args.len() == 3 => args,
                                _ => crate::bail_parse_error!(
                                    "{} requires exactly 3 arguments",
                                    srf.to_string()
                                ),
                            };
                            let temp_reg = programBuilder.allocRegister();
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[0],
                                temp_reg,
                                precomputed_exprs_to_registers,
                            )?;
                            let jump_target_when_false = programBuilder.allocateLabel();
                            programBuilder.addInsnWithLabelDependency(
                                Insn::IfNot {
                                    reg: temp_reg,
                                    target_pc: jump_target_when_false,
                                    null_reg: 1,
                                },
                                jump_target_when_false,
                            );
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[1],
                                destReg,
                                precomputed_exprs_to_registers,
                            )?;
                            let jump_target_result = programBuilder.allocateLabel();
                            programBuilder.addInsnWithLabelDependency(
                                Insn::Goto {
                                    targetPc: jump_target_result,
                                },
                                jump_target_result,
                            );
                            programBuilder.resolveLabel(jump_target_when_false, programBuilder.nextPc());
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[2],
                                destReg,
                                precomputed_exprs_to_registers,
                            )?;
                            programBuilder.resolveLabel(jump_target_result, programBuilder.nextPc());
                            Ok(destReg)
                        }
                        ScalarFunc::Glob | ScalarFunc::Like => {
                            let args = if let Some(args) = args {
                                if args.len() < 2 {
                                    crate::bail_parse_error!(
                                        "{} function with less than 2 arguments",
                                        srf.to_string()
                                    );
                                }
                                args
                            } else {
                                crate::bail_parse_error!(
                                    "{} function with no arguments",
                                    srf.to_string()
                                );
                            };
                            for arg in args {
                                let reg = programBuilder.allocRegister();
                                let _ = translateExpr(
                                    programBuilder,
                                    tblRefs,
                                    arg,
                                    reg,
                                    precomputed_exprs_to_registers,
                                )?;
                                if let ast::Expr::Literal(_) = arg {
                                    programBuilder.mark_last_insn_constant()
                                }
                            }
                            programBuilder.addInsn0(Insn::Function {
                                // Only constant patterns for LIKE are supported currently, so this
                                // is always 1
                                constant_mask: 1,
                                start_reg: destReg + 1,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Abs
                        | ScalarFunc::Lower
                        | ScalarFunc::Upper
                        | ScalarFunc::Length
                        | ScalarFunc::OctetLength
                        | ScalarFunc::Typeof
                        | ScalarFunc::Unicode
                        | ScalarFunc::Quote
                        | ScalarFunc::RandomBlob
                        | ScalarFunc::Sign
                        | ScalarFunc::Soundex
                        | ScalarFunc::ZeroBlob => {
                            let args = if let Some(args) = args {
                                if args.len() != 1 {
                                    crate::bail_parse_error!(
                                        "{} function with not exactly 1 argument",
                                        srf.to_string()
                                    );
                                }
                                args
                            } else {
                                crate::bail_parse_error!(
                                    "{} function with no arguments",
                                    srf.to_string()
                                );
                            };

                            let regs = programBuilder.allocRegister();
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[0],
                                regs,
                                precomputed_exprs_to_registers,
                            )?;
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: regs,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Random => {
                            if args.is_some() {
                                crate::bail_parse_error!(
                                    "{} function with arguments",
                                    srf.to_string()
                                );
                            }
                            let regs = programBuilder.allocRegister();
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: regs,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Date => {
                            if let Some(args) = args {
                                for arg in args.iter() {
                                    // register containing result of each argument expression
                                    let target_reg = programBuilder.allocRegister();
                                    _ = translateExpr(
                                        programBuilder,
                                        tblRefs,
                                        arg,
                                        target_reg,
                                        precomputed_exprs_to_registers,
                                    )?;
                                }
                            }
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: destReg + 1,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Substr | ScalarFunc::Substring => {
                            let args = if let Some(args) = args {
                                if !(args.len() == 2 || args.len() == 3) {
                                    crate::bail_parse_error!(
                                        "{} function with wrong number of arguments",
                                        srf.to_string()
                                    )
                                }
                                args
                            } else {
                                crate::bail_parse_error!(
                                    "{} function with no arguments",
                                    srf.to_string()
                                );
                            };

                            let str_reg = programBuilder.allocRegister();
                            let start_reg = programBuilder.allocRegister();
                            let length_reg = programBuilder.allocRegister();

                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[0],
                                str_reg,
                                precomputed_exprs_to_registers,
                            )?;
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[1],
                                start_reg,
                                precomputed_exprs_to_registers,
                            )?;
                            if args.len() == 3 {
                                translateExpr(
                                    programBuilder,
                                    tblRefs,
                                    &args[2],
                                    length_reg,
                                    precomputed_exprs_to_registers,
                                )?;
                            }

                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: str_reg,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Hex => {
                            let args = if let Some(args) = args {
                                if args.len() != 1 {
                                    crate::bail_parse_error!(
                                        "hex function must have exactly 1 argument",
                                    );
                                }
                                args
                            } else {
                                crate::bail_parse_error!("hex function with no arguments",);
                            };
                            let regs = programBuilder.allocRegister();
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[0],
                                regs,
                                precomputed_exprs_to_registers,
                            )?;
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: regs,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::UnixEpoch => {
                            let mut start_reg = 0;
                            match args {
                                Some(args) if args.len() > 1 => {
                                    crate::bail_parse_error!("epoch function with > 1 arguments. Modifiers are not yet supported.");
                                }
                                Some(args) if args.len() == 1 => {
                                    let arg_reg = programBuilder.allocRegister();
                                    let _ = translateExpr(
                                        programBuilder,
                                        tblRefs,
                                        &args[0],
                                        arg_reg,
                                        precomputed_exprs_to_registers,
                                    )?;
                                    start_reg = arg_reg;
                                }
                                _ => {}
                            }
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Time => {
                            if let Some(args) = args {
                                for arg in args.iter() {
                                    // register containing result of each argument expression
                                    let target_reg = programBuilder.allocRegister();
                                    _ = translateExpr(
                                        programBuilder,
                                        tblRefs,
                                        arg,
                                        target_reg,
                                        precomputed_exprs_to_registers,
                                    )?;
                                }
                            }
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: destReg + 1,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Trim
                        | ScalarFunc::LTrim
                        | ScalarFunc::RTrim
                        | ScalarFunc::Round
                        | ScalarFunc::Unhex => {
                            let args = if let Some(args) = args {
                                if args.len() > 2 {
                                    crate::bail_parse_error!(
                                        "{} function with more than 2 arguments",
                                        srf.to_string()
                                    );
                                }
                                args
                            } else {
                                crate::bail_parse_error!(
                                    "{} function with no arguments",
                                    srf.to_string()
                                );
                            };

                            for arg in args.iter() {
                                let reg = programBuilder.allocRegister();
                                translateExpr(
                                    programBuilder,
                                    tblRefs,
                                    arg,
                                    reg,
                                    precomputed_exprs_to_registers,
                                )?;
                                if let ast::Expr::Literal(_) = arg {
                                    programBuilder.mark_last_insn_constant();
                                }
                            }
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: destReg + 1,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Min => {
                            let args = if let Some(args) = args {
                                if args.is_empty() {
                                    crate::bail_parse_error!(
                                        "min function with less than one argument"
                                    );
                                }
                                args
                            } else {
                                crate::bail_parse_error!("min function with no arguments");
                            };
                            for arg in args {
                                let reg = programBuilder.allocRegister();
                                let _ = translateExpr(
                                    programBuilder,
                                    tblRefs,
                                    arg,
                                    reg,
                                    precomputed_exprs_to_registers,
                                )?;
                                if let ast::Expr::Literal(_) = arg {
                                    programBuilder.mark_last_insn_constant()
                                }
                            }

                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: destReg + 1,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Max => {
                            let args = if let Some(args) = args {
                                if args.is_empty() {
                                    crate::bail_parse_error!(
                                        "max function with less than one argument"
                                    );
                                }
                                args
                            } else {
                                crate::bail_parse_error!("max function with no arguments");
                            };
                            for arg in args {
                                let reg = programBuilder.allocRegister();
                                let _ = translateExpr(
                                    programBuilder,
                                    tblRefs,
                                    arg,
                                    reg,
                                    precomputed_exprs_to_registers,
                                )?;
                                if let ast::Expr::Literal(_) = arg {
                                    programBuilder.mark_last_insn_constant()
                                }
                            }

                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: destReg + 1,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Nullif | ScalarFunc::Instr => {
                            let args = if let Some(args) = args {
                                if args.len() != 2 {
                                    crate::bail_parse_error!(
                                        "{} function must have two argument",
                                        srf.to_string()
                                    );
                                }
                                args
                            } else {
                                crate::bail_parse_error!(
                                    "{} function with no arguments",
                                    srf.to_string()
                                );
                            };

                            let first_reg = programBuilder.allocRegister();
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[0],
                                first_reg,
                                precomputed_exprs_to_registers,
                            )?;
                            let second_reg = programBuilder.allocRegister();
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[1],
                                second_reg,
                                precomputed_exprs_to_registers,
                            )?;
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: first_reg,
                                dest: destReg,
                                func: func_ctx,
                            });

                            Ok(destReg)
                        }
                        ScalarFunc::SqliteVersion => {
                            if args.is_some() {
                                crate::bail_parse_error!("sqlite_version function with arguments");
                            }

                            let output_register = programBuilder.allocRegister();
                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: output_register,
                                dest: output_register,
                                func: func_ctx,
                            });

                            programBuilder.addInsn0(Insn::Copy {
                                src_reg: output_register,
                                dst_reg: destReg,
                                amount: 1,
                            });
                            Ok(destReg)
                        }
                        ScalarFunc::Replace => {
                            let args = if let Some(args) = args {
                                if !args.len() == 3 {
                                    crate::bail_parse_error!(
                                        "function {}() requires exactly 3 arguments",
                                        srf.to_string()
                                    )
                                }
                                args
                            } else {
                                crate::bail_parse_error!(
                                    "function {}() requires exactly 3 arguments",
                                    srf.to_string()
                                );
                            };

                            let str_reg = programBuilder.allocRegister();
                            let pattern_reg = programBuilder.allocRegister();
                            let replacement_reg = programBuilder.allocRegister();

                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[0],
                                str_reg,
                                precomputed_exprs_to_registers,
                            )?;
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[1],
                                pattern_reg,
                                precomputed_exprs_to_registers,
                            )?;

                            translateExpr(
                                programBuilder,
                                tblRefs,
                                &args[2],
                                replacement_reg,
                                precomputed_exprs_to_registers,
                            )?;

                            programBuilder.addInsn0(Insn::Function {
                                constant_mask: 0,
                                start_reg: str_reg,
                                dest: destReg,
                                func: func_ctx,
                            });
                            Ok(destReg)
                        }
                    }
                }
                Func::Math(math_func) => match math_func.arity() {
                    MathFuncArity::Nullary => {
                        if args.is_some() {
                            crate::bail_parse_error!("{} function with arguments", math_func);
                        }

                        programBuilder.addInsn0(Insn::Function {
                            constant_mask: 0,
                            start_reg: 0,
                            dest: destReg,
                            func: func_ctx,
                        });
                        Ok(destReg)
                    }

                    MathFuncArity::Unary => {
                        let args = if let Some(args) = args {
                            if args.len() != 1 {
                                crate::bail_parse_error!(
                                    "{} function with not exactly 1 argument",
                                    math_func
                                );
                            }
                            args
                        } else {
                            crate::bail_parse_error!("{} function with no arguments", math_func);
                        };

                        let reg = programBuilder.allocRegister();

                        translateExpr(
                            programBuilder,
                            tblRefs,
                            &args[0],
                            reg,
                            precomputed_exprs_to_registers,
                        )?;

                        programBuilder.addInsn0(Insn::Function {
                            constant_mask: 0,
                            start_reg: reg,
                            dest: destReg,
                            func: func_ctx,
                        });
                        Ok(destReg)
                    }

                    MathFuncArity::Binary => {
                        let args = if let Some(args) = args {
                            if args.len() != 2 {
                                crate::bail_parse_error!("{} function with not exactly 2 arguments", math_func);
                            }
                            args
                        } else {
                            crate::bail_parse_error!("{} function with no arguments", math_func);
                        };

                        let reg1 = programBuilder.allocRegister();
                        let reg2 = programBuilder.allocRegister();

                        translateExpr(
                            programBuilder,
                            tblRefs,
                            &args[0],
                            reg1,
                            precomputed_exprs_to_registers,
                        )?;
                        if let ast::Expr::Literal(_) = &args[0] {
                            programBuilder.mark_last_insn_constant();
                        }

                        translateExpr(
                            programBuilder,
                            tblRefs,
                            &args[1],
                            reg2,
                            precomputed_exprs_to_registers,
                        )?;
                        if let ast::Expr::Literal(_) = &args[1] {
                            programBuilder.mark_last_insn_constant();
                        }

                        programBuilder.addInsn0(Insn::Function {
                            constant_mask: 0,
                            start_reg: destReg + 1,
                            dest: destReg,
                            func: func_ctx,
                        });
                        Ok(destReg)
                    }

                    MathFuncArity::UnaryOrBinary => {
                        let args = if let Some(args) = args {
                            if args.len() > 2 {
                                crate::bail_parse_error!("{} function with more than 2 arguments", math_func);
                            }

                            args
                        } else {
                            crate::bail_parse_error!("{} function with no arguments", math_func);
                        };

                        let regs = programBuilder.allocRegisters(args.len());

                        for (i, arg) in args.iter().enumerate() {
                            translateExpr(
                                programBuilder,
                                tblRefs,
                                arg,
                                regs + i,
                                precomputed_exprs_to_registers,
                            )?;
                        }

                        programBuilder.addInsn0(Insn::Function {
                            constant_mask: 0,
                            start_reg: regs,
                            dest: destReg,
                            func: func_ctx,
                        });
                        Ok(destReg)
                    }
                },
            }
        }
        ast::Expr::Id(_) => unreachable!("Id should be resolved to a Column before translation"),
        ast::Expr::Column {
            database: _,
            table,
            column,
            is_rowid_alias,
        } => {
            let tbl_ref = tblRefs.as_ref().unwrap().get(*table).unwrap();
            let cursor_id = programBuilder.resolveCursorId(&tbl_ref.table_identifier);
            if *is_rowid_alias {
                programBuilder.addInsn0(Insn::RowId {
                    cursor_id,
                    dest: destReg,
                });
            } else {
                programBuilder.addInsn0(Insn::Column {
                    cursor_id,
                    column: *column,
                    destReg: destReg,
                });
            }
            let column = &tbl_ref.table.columns[*column];
            maybe_apply_affinity(column.columnType, destReg, programBuilder);
            Ok(destReg)
        }
        ast::Expr::Name(_) => todo!(),
        ast::Expr::NotNull(_) => todo!(),
        ast::Expr::Parenthesized(exprs) => {
            if exprs.is_empty() {
                crate::bail_parse_error!("parenthesized expression with no arguments");
            }
            if exprs.len() == 1 {
                translateExpr(
                    programBuilder,
                    tblRefs,
                    &exprs[0],
                    destReg,
                    precomputed_exprs_to_registers,
                )?;
            } else {
                // Parenthesized expressions with multiple arguments are reserved for special cases
                // like `(a, b) IN ((1, 2), (3, 4))`.
                todo!("TODO: parenthesized expression with multiple arguments not yet supported");
            }
            Ok(destReg)
        }
        ast::Expr::Qualified(_, _) => {
            unreachable!("Qualified should be resolved to a Column before translation")
        }
        ast::Expr::Raise(_, _) => todo!(),
        ast::Expr::Subquery(_) => todo!(),
        ast::Expr::Unary(op, expr) => match (op, expr.as_ref()) {
            (
                UnaryOperator::Negative | UnaryOperator::Positive,
                ast::Expr::Literal(ast::Literal::Numeric(numeric_value)),
            ) => {
                let maybe_int = numeric_value.parse::<i64>();
                let multiplier = if let UnaryOperator::Negative = op {
                    -1
                } else {
                    1
                };
                if let Ok(value) = maybe_int {
                    programBuilder.addInsn0(Insn::Integer {
                        value: value * multiplier,
                        destReg,
                    });
                } else {
                    programBuilder.addInsn0(Insn::Real {
                        value: multiplier as f64 * numeric_value.parse::<f64>()?,
                        dest: destReg,
                    });
                }
                programBuilder.mark_last_insn_constant();
                Ok(destReg)
            }
            (UnaryOperator::Negative | UnaryOperator::Positive, _) => {
                let value = if let UnaryOperator::Negative = op {
                    -1
                } else {
                    1
                };

                let reg = programBuilder.allocRegister();
                translateExpr(
                    programBuilder,
                    tblRefs,
                    expr,
                    reg,
                    precomputed_exprs_to_registers,
                )?;
                let zero_reg = programBuilder.allocRegister();
                programBuilder.addInsn0(Insn::Integer {
                    value,
                    destReg: zero_reg,
                });
                programBuilder.mark_last_insn_constant();
                programBuilder.addInsn0(Insn::Multiply {
                    lhs: zero_reg,
                    rhs: reg,
                    dest: destReg,
                });
                Ok(destReg)
            }
            (UnaryOperator::BitwiseNot, ast::Expr::Literal(ast::Literal::Numeric(num_val))) => {
                let maybe_int = num_val.parse::<i64>();
                if let Ok(val) = maybe_int {
                    programBuilder.addInsn0(Insn::Integer {
                        value: !val,
                        destReg,
                    });
                } else {
                    let num_val = num_val.parse::<f64>()? as i64;
                    programBuilder.addInsn0(Insn::Integer {
                        value: !num_val,
                        destReg,
                    });
                }
                programBuilder.mark_last_insn_constant();
                Ok(destReg)
            }
            (UnaryOperator::BitwiseNot, ast::Expr::Literal(ast::Literal::Null)) => {
                programBuilder.addInsn0(Insn::Null {
                    dest: destReg,
                    dest_end: None,
                });
                programBuilder.mark_last_insn_constant();
                Ok(destReg)
            }
            (UnaryOperator::BitwiseNot, _) => {
                let reg = programBuilder.allocRegister();
                translateExpr(
                    programBuilder,
                    tblRefs,
                    expr,
                    reg,
                    precomputed_exprs_to_registers,
                )?;
                programBuilder.addInsn0(Insn::BitNot {
                    reg,
                    dest: destReg,
                });
                Ok(destReg)
            }
            _ => todo!(),
        },
        _ => todo!(),
    }
}

fn wrap_eval_jump_expr(
    program: &mut ProgramBuilder,
    insn: Insn,
    target_register: usize,
    if_true_label: BranchOffset,
) {
    program.addInsn0(Insn::Integer {
        value: 1, // emit True by default
        destReg: target_register,
    });
    program.addInsnWithLabelDependency(insn, if_true_label);
    program.addInsn0(Insn::Integer {
        value: 0, // emit False if we reach this point (no jump)
        destReg: target_register,
    });
    program.preassignLabelToNextInsn(if_true_label);
}

pub fn maybe_apply_affinity(col_type: ColumnType, target_register: usize, program: &mut ProgramBuilder) {
    if col_type == crate::schema::ColumnType::Real {
        program.addInsn0(Insn::RealAffinity {
            register: target_register,
        })
    }
}

pub fn translate_aggregation(
    program: &mut ProgramBuilder,
    referenced_tables: &[BTreeTableRef],
    agg: &Aggregate,
    target_register: usize,
) -> Result<usize> {
    let dest = match agg.func {
        AggFunc::Avg => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("avg bad number of arguments");
            }
            let expr = &agg.args[0];
            let expr_reg = program.allocRegister();
            let _ = translateExpr(program, Some(referenced_tables), expr, expr_reg, None)?;
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Avg,
            });
            target_register
        }
        AggFunc::Count => {
            let expr_reg = if agg.args.is_empty() {
                program.allocRegister()
            } else {
                let expr = &agg.args[0];
                let expr_reg = program.allocRegister();
                let _ = translateExpr(program, Some(referenced_tables), expr, expr_reg, None);
                expr_reg
            };
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Count,
            });
            target_register
        }
        AggFunc::GroupConcat => {
            if agg.args.len() != 1 && agg.args.len() != 2 {
                crate::bail_parse_error!("group_concat bad number of arguments");
            }

            let expr_reg = program.allocRegister();
            let delimiter_reg = program.allocRegister();

            let expr = &agg.args[0];
            let delimiter_expr: ast::Expr;

            if agg.args.len() == 2 {
                match &agg.args[1] {
                    ast::Expr::Column { .. } => {
                        delimiter_expr = agg.args[1].clone();
                    }
                    ast::Expr::Literal(ast::Literal::String(s)) => {
                        delimiter_expr = ast::Expr::Literal(ast::Literal::String(s.to_string()));
                    }
                    _ => crate::bail_parse_error!("Incorrect delimiter parameter"),
                };
            } else {
                delimiter_expr = ast::Expr::Literal(ast::Literal::String(String::from("\",\"")));
            }

            translateExpr(program, Some(referenced_tables), expr, expr_reg, None)?;
            translateExpr(
                program,
                Some(referenced_tables),
                &delimiter_expr,
                delimiter_reg,
                None,
            )?;

            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: delimiter_reg,
                func: AggFunc::GroupConcat,
            });

            target_register
        }
        AggFunc::Max => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("max bad number of arguments");
            }
            let expr = &agg.args[0];
            let expr_reg = program.allocRegister();
            let _ = translateExpr(program, Some(referenced_tables), expr, expr_reg, None)?;
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Max,
            });
            target_register
        }
        AggFunc::Min => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("min bad number of arguments");
            }
            let expr = &agg.args[0];
            let expr_reg = program.allocRegister();
            let _ = translateExpr(program, Some(referenced_tables), expr, expr_reg, None)?;
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Min,
            });
            target_register
        }
        AggFunc::StringAgg => {
            if agg.args.len() != 2 {
                crate::bail_parse_error!("string_agg bad number of arguments");
            }

            let expr_reg = program.allocRegister();
            let delimiter_reg = program.allocRegister();

            let expr = &agg.args[0];
            let delimiter_expr: ast::Expr;

            match &agg.args[1] {
                ast::Expr::Column { .. } => {
                    delimiter_expr = agg.args[1].clone();
                }
                ast::Expr::Literal(ast::Literal::String(s)) => {
                    delimiter_expr = ast::Expr::Literal(ast::Literal::String(s.to_string()));
                }
                _ => crate::bail_parse_error!("Incorrect delimiter parameter"),
            };

            translateExpr(program, Some(referenced_tables), expr, expr_reg, None)?;
            translateExpr(
                program,
                Some(referenced_tables),
                &delimiter_expr,
                delimiter_reg,
                None,
            )?;

            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: delimiter_reg,
                func: AggFunc::StringAgg,
            });

            target_register
        }
        AggFunc::Sum => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("sum bad number of arguments");
            }
            let expr = &agg.args[0];
            let expr_reg = program.allocRegister();
            let _ = translateExpr(program, Some(referenced_tables), expr, expr_reg, None)?;
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Sum,
            });
            target_register
        }
        AggFunc::Total => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("total bad number of arguments");
            }
            let expr = &agg.args[0];
            let expr_reg = program.allocRegister();
            let _ = translateExpr(program, Some(referenced_tables), expr, expr_reg, None)?;
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Total,
            });
            target_register
        }
    };
    Ok(dest)
}

pub fn translate_aggregation_groupby(
    program: &mut ProgramBuilder,
    referenced_tables: &[BTreeTableRef],
    group_by_sorter_cursor_id: usize,
    cursor_index: usize,
    agg: &Aggregate,
    target_register: usize,
) -> Result<usize> {
    let emit_column = |program: &mut ProgramBuilder, expr_reg: usize| {
        program.addInsn0(Insn::Column {
            cursor_id: group_by_sorter_cursor_id,
            column: cursor_index,
            destReg: expr_reg,
        });
    };
    let dest = match agg.func {
        AggFunc::Avg => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("avg bad number of arguments");
            }
            let expr_reg = program.allocRegister();
            emit_column(program, expr_reg);
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Avg,
            });
            target_register
        }
        AggFunc::Count => {
            let expr_reg = program.allocRegister();
            emit_column(program, expr_reg);
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Count,
            });
            target_register
        }
        AggFunc::GroupConcat => {
            if agg.args.len() != 1 && agg.args.len() != 2 {
                crate::bail_parse_error!("group_concat bad number of arguments");
            }

            let expr_reg = program.allocRegister();
            let delimiter_reg = program.allocRegister();

            let delimiter_expr: ast::Expr;

            if agg.args.len() == 2 {
                match &agg.args[1] {
                    ast::Expr::Column { .. } => {
                        delimiter_expr = agg.args[1].clone();
                    }
                    ast::Expr::Literal(ast::Literal::String(s)) => {
                        delimiter_expr = ast::Expr::Literal(ast::Literal::String(s.to_string()));
                    }
                    _ => crate::bail_parse_error!("Incorrect delimiter parameter"),
                };
            } else {
                delimiter_expr = ast::Expr::Literal(ast::Literal::String(String::from("\",\"")));
            }

            emit_column(program, expr_reg);
            translateExpr(
                program,
                Some(referenced_tables),
                &delimiter_expr,
                delimiter_reg,
                None,
            )?;

            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: delimiter_reg,
                func: AggFunc::GroupConcat,
            });

            target_register
        }
        AggFunc::Max => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("max bad number of arguments");
            }
            let expr_reg = program.allocRegister();
            emit_column(program, expr_reg);
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Max,
            });
            target_register
        }
        AggFunc::Min => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("min bad number of arguments");
            }
            let expr_reg = program.allocRegister();
            emit_column(program, expr_reg);
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Min,
            });
            target_register
        }
        AggFunc::StringAgg => {
            if agg.args.len() != 2 {
                crate::bail_parse_error!("string_agg bad number of arguments");
            }

            let expr_reg = program.allocRegister();
            let delimiter_reg = program.allocRegister();

            let delimiter_expr: ast::Expr;

            match &agg.args[1] {
                ast::Expr::Column { .. } => {
                    delimiter_expr = agg.args[1].clone();
                }
                ast::Expr::Literal(ast::Literal::String(s)) => {
                    delimiter_expr = ast::Expr::Literal(ast::Literal::String(s.to_string()));
                }
                _ => crate::bail_parse_error!("Incorrect delimiter parameter"),
            };

            emit_column(program, expr_reg);
            translateExpr(
                program,
                Some(referenced_tables),
                &delimiter_expr,
                delimiter_reg,
                None,
            )?;

            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: delimiter_reg,
                func: AggFunc::StringAgg,
            });

            target_register
        }
        AggFunc::Sum => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("sum bad number of arguments");
            }
            let expr_reg = program.allocRegister();
            emit_column(program, expr_reg);
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Sum,
            });
            target_register
        }
        AggFunc::Total => {
            if agg.args.len() != 1 {
                crate::bail_parse_error!("total bad number of arguments");
            }
            let expr_reg = program.allocRegister();
            emit_column(program, expr_reg);
            program.addInsn0(Insn::AggStep {
                acc_reg: target_register,
                col: expr_reg,
                delimiter: 0,
                func: AggFunc::Total,
            });
            target_register
        }
    };
    Ok(dest)
}
