use std::{rc::Rc, sync::Arc};

use sqlite3_parser::ast::{Expr, FunctionTail, Literal};

use crate::{
    schema::{self, Schema},
    Result, RowResult, Rows, IO,
};

pub fn normalize_ident(ident: &str) -> String {
    (if ident.starts_with('"') && ident.ends_with('"') {
        &ident[1..ident.len() - 1]
    } else {
        ident
    }).to_lowercase()
}

pub fn parse_schema_rows(rows: Option<Rows>, schema: &mut Schema, io: Arc<dyn IO>) -> Result<()> {
    if let Some(mut rows) = rows {
        loop {
            match rows.next_row()? {
                RowResult::Row(row) => {
                    let ty = row.get::<&str>(0)?;
                    if ty != "table" && ty != "index" {
                        continue;
                    }
                    match ty {
                        "table" => {
                            let root_page: i64 = row.get::<i64>(3)?;
                            let sql: &str = row.get::<&str>(4)?;
                            let table = schema::BTreeTable::from_sql(sql, root_page as usize)?;
                            schema.addTbl(Rc::new(table));
                        }
                        "index" => {
                            let root_page: i64 = row.get::<i64>(3)?;
                            match row.get::<&str>(4) {
                                Ok(sql) => {
                                    let index = schema::Index::from_sql(sql, root_page as usize)?;
                                    schema.add_index(Rc::new(index));
                                }
                                _ => continue,
                                // TODO parse auto index structures
                            }
                        }
                        _ => continue,
                    }
                }
                RowResult::IO => {
                    // TODO: How do we ensure that the I/O we submitted to read the schema is actually complete
                    io.runOnce()?;
                }
                RowResult::Done => break,
            }
        }
    }
    Ok(())
}

fn cmp_numeric_strings(num_str: &str, other: &str) -> bool {
    match (num_str.parse::<f64>(), other.parse::<f64>()) {
        (Ok(num), Ok(other)) => num == other,
        _ => num_str == other,
    }
}

const QUOTE_PAIRS: &[(char, char)] = &[('"', '"'), ('[', ']'), ('`', '`')];

pub fn check_ident_equivalency(ident1: &str, ident2: &str) -> bool {
    fn strip_quotes(identifier: &str) -> &str {
        for &(start, end) in QUOTE_PAIRS {
            if identifier.starts_with(start) && identifier.ends_with(end) {
                return &identifier[1..identifier.len() - 1];
            }
        }
        identifier
    }
    strip_quotes(ident1).eq_ignore_ascii_case(strip_quotes(ident2))
}

pub fn check_literal_equivalency(lhs: &Literal, rhs: &Literal) -> bool {
    match (lhs, rhs) {
        (Literal::Numeric(n1), Literal::Numeric(n2)) => cmp_numeric_strings(n1, n2),
        (Literal::String(s1), Literal::String(s2)) => check_ident_equivalency(s1, s2),
        (Literal::Blob(b1), Literal::Blob(b2)) => b1 == b2,
        (Literal::Keyword(k1), Literal::Keyword(k2)) => check_ident_equivalency(k1, k2),
        (Literal::Null, Literal::Null) => true,
        (Literal::CurrentDate, Literal::CurrentDate) => true,
        (Literal::CurrentTime, Literal::CurrentTime) => true,
        (Literal::CurrentTimestamp, Literal::CurrentTimestamp) => true,
        _ => false,
    }
}

/// This function is used to determine whether two expressions are logically
/// equivalent in the context of queries, even if their representations
/// differ. e.g.: `SUM(x)` and `sum(x)`, `x + y` and `y + x`
///
/// *Note*: doesn't attempt to evaluate/compute "constexpr" results
pub fn exprs_are_equivalent(expr1: &Expr, expr2: &Expr) -> bool {
    match (expr1, expr2) {
        (
            Expr::Between {
                lhs: lhs1,
                not: not1,
                start: start1,
                end: end1,
            },
            Expr::Between {
                lhs: lhs2,
                not: not2,
                start: start2,
                end: end2,
            },
        ) => {
            not1 == not2
                && exprs_are_equivalent(lhs1, lhs2)
                && exprs_are_equivalent(start1, start2)
                && exprs_are_equivalent(end1, end2)
        }
        (Expr::Binary(lhs1, op1, rhs1), Expr::Binary(lhs2, op2, rhs2)) => {
            op1 == op2
                && ((exprs_are_equivalent(lhs1, lhs2) && exprs_are_equivalent(rhs1, rhs2))
                    || (op1.is_commutative()
                        && exprs_are_equivalent(lhs1, rhs2)
                        && exprs_are_equivalent(rhs1, lhs2)))
        }
        (
            Expr::Case {
                base: base1,
                when_then_pairs: pairs1,
                else_expr: else1,
            },
            Expr::Case {
                base: base2,
                when_then_pairs: pairs2,
                else_expr: else2,
            },
        ) => {
            base1 == base2
                && pairs1.len() == pairs2.len()
                && pairs1.iter().zip(pairs2).all(|((w1, t1), (w2, t2))| {
                    exprs_are_equivalent(w1, w2) && exprs_are_equivalent(t1, t2)
                })
                && else1 == else2
        }
        (
            Expr::Cast {
                expr: expr1,
                type_name: type1,
            },
            Expr::Cast {
                expr: expr2,
                type_name: type2,
            },
        ) => {
            exprs_are_equivalent(expr1, expr2)
                && match (type1, type2) {
                    (Some(t1), Some(t2)) => t1.name.eq_ignore_ascii_case(&t2.name),
                    _ => false,
                }
        }
        (Expr::Collate(expr1, collation1), Expr::Collate(expr2, collation2)) => {
            exprs_are_equivalent(expr1, expr2) && collation1.eq_ignore_ascii_case(collation2)
        }
        (
            Expr::FunctionCall {
                name: name1,
                distinctness: distinct1,
                args: args1,
                order_by: order1,
                filter_over: filter1,
            },
            Expr::FunctionCall {
                name: name2,
                distinctness: distinct2,
                args: args2,
                order_by: order2,
                filter_over: filter2,
            },
        ) => {
            name1.0.eq_ignore_ascii_case(&name2.0)
                && distinct1 == distinct2
                && args1 == args2
                && order1 == order2
                && filter1 == filter2
        }
        (
            Expr::FunctionCallStar {
                name: name1,
                filter_over: filter1,
            },
            Expr::FunctionCallStar {
                name: name2,
                filter_over: filter2,
            },
        ) => {
            name1.0.eq_ignore_ascii_case(&name2.0)
                && match (filter1, filter2) {
                    (None, None) => true,
                    (
                        Some(FunctionTail {
                            filter_clause: fc1,
                            over_clause: oc1,
                        }),
                        Some(FunctionTail {
                            filter_clause: fc2,
                            over_clause: oc2,
                        }),
                    ) => match ((fc1, fc2), (oc1, oc2)) {
                        ((Some(fc1), Some(fc2)), (Some(oc1), Some(oc2))) => {
                            exprs_are_equivalent(fc1, fc2) && oc1 == oc2
                        }
                        ((Some(fc1), Some(fc2)), _) => exprs_are_equivalent(fc1, fc2),
                        _ => false,
                    },
                    _ => false,
                }
        }
        (Expr::NotNull(expr1), Expr::NotNull(expr2)) => exprs_are_equivalent(expr1, expr2),
        (Expr::IsNull(expr1), Expr::IsNull(expr2)) => exprs_are_equivalent(expr1, expr2),
        (Expr::Literal(lit1), Expr::Literal(lit2)) => check_literal_equivalency(lit1, lit2),
        (Expr::Id(id1), Expr::Id(id2)) => check_ident_equivalency(&id1.0, &id2.0),
        (Expr::Unary(op1, expr1), Expr::Unary(op2, expr2)) => op1 == op2 && exprs_are_equivalent(expr1, expr2),
        (Expr::Variable(var1), Expr::Variable(var2)) => var1 == var2,
        (Expr::Parenthesized(exprs1), Expr::Parenthesized(exprs2)) => {
            exprs1.len() == exprs2.len() && exprs1.iter().zip(exprs2).all(|(e1, e2)| exprs_are_equivalent(e1, e2))
        }
        (Expr::Parenthesized(exprs1), exprs2) | (exprs2, Expr::Parenthesized(exprs1)) => {
            exprs1.len() == 1 && exprs_are_equivalent(&exprs1[0], exprs2)
        }
        (Expr::Qualified(tn1, cn1), Expr::Qualified(tn2, cn2)) => {
            check_ident_equivalency(&tn1.0, &tn2.0) && check_ident_equivalency(&cn1.0, &cn2.0)
        }
        (Expr::DoublyQualified(sn1, tn1, cn1), Expr::DoublyQualified(sn2, tn2, cn2)) => {
            check_ident_equivalency(&sn1.0, &sn2.0)
                && check_ident_equivalency(&tn1.0, &tn2.0)
                && check_ident_equivalency(&cn1.0, &cn2.0)
        }
        (
            Expr::InList {
                lhs: lhs1,
                not: not1,
                rhs: rhs1,
            },
            Expr::InList {
                lhs: lhs2,
                not: not2,
                rhs: rhs2,
            },
        ) => {
            *not1 == *not2
                && exprs_are_equivalent(lhs1, lhs2)
                && rhs1.as_ref().zip(rhs2.as_ref()).map(|(list1, list2)| {
                        list1.len() == list2.len()
                            && list1.iter().zip(list2).all(|(e1, e2)| exprs_are_equivalent(e1, e2))
                    }).unwrap_or(false)
        }
        // fall back to naive equality check
        _ => expr1 == expr2,
    }
}