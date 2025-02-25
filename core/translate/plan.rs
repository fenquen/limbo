use core::fmt;
use std::{
    fmt::{Display, Formatter},
    rc::Rc,
};

use sqlite3_parser::ast;

use crate::{
    function::AggFunc,
    schema::{BTreeTable, Column, Index},
    Result,
};

#[derive(Debug)]
pub struct ResultSetColumn {
    pub expr: ast::Expr,
    // TODO: encode which aggregates (e.g. index bitmask of plan.aggregates) are present in this column
    pub contains_aggregates: bool,
}

#[derive(Debug)]
pub struct GroupBy {
    pub exprs: Vec<ast::Expr>,

    /// having clause split into a vec at 'AND' boundaries.
    pub having: Option<Vec<ast::Expr>>,
}

#[derive(Debug)]
pub struct Plan {
    /// A tree of sources (tables).
    pub srcOperator: SrcOperator,

    /// the columns inside SELECT ... FROM
    pub resultCols: Vec<ResultSetColumn>,

    /// where clause split into a vec at 'AND' boundaries.
    pub whereExprs: Option<Vec<ast::Expr>>,

    /// group by clause
    pub group_by: Option<GroupBy>,

    /// order by clause
    pub orderBys: Option<Vec<(ast::Expr, Direction)>>,

    /// all the aggregates collected from the result columns, order by, and (TODO) having clauses
    pub aggregates: Vec<Aggregate>,

    /// limit clause
    pub limit: Option<usize>,

    /// all the tables referenced in the query
    pub tblRefs: Vec<BTreeTableRef>,

    /// all the indexes available in schema
    pub indexes: Vec<Rc<Index>>,

    /// query contains a constant condition that is always false
    pub containsConstantFalseCondition: bool,
}

impl Display for Plan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.srcOperator)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IterationDirection {
    Forwards,
    Backwards,
}

impl SrcOperator {
    pub fn select_star(&self, cols: &mut Vec<ResultSetColumn>) {
        for (tblRef, col, idx) in self.select_star_helper() {
            cols.push(ResultSetColumn {
                expr: ast::Expr::Column {
                    database: None,
                    table: tblRef.table_index,
                    column: idx,
                    is_rowid_alias: col.is_rowid_alias,
                },
                contains_aggregates: false,
            });
        }
    }

    /// All this ceremony is required to deduplicate columns when joining with USING
    fn select_star_helper(&self) -> Vec<(&BTreeTableRef, &Column, usize)> {
        match self {
            SrcOperator::Join {
                left, right, using, ..
            } => {
                let mut columns = left.select_star_helper();

                // Join columns are filtered out from the right side
                // in the case of a USING join.
                if let Some(using_cols) = using {
                    let right_columns = right.select_star_helper();

                    for (table_ref, col, idx) in right_columns {
                        if !using_cols.iter().any(|using_col| col.name.eq_ignore_ascii_case(&using_col.0)) {
                            columns.push((table_ref, col, idx));
                        }
                    }
                } else {
                    columns.extend(right.select_star_helper());
                }
                columns
            }
            SrcOperator::Scan { tblRef: table_reference, .. } | SrcOperator::Search { tblRef: table_reference, .. } =>
                table_reference.table.columns.iter().enumerate().map(|(i, col)| (table_reference, col, i)).collect(),
            SrcOperator::Nothing => Vec::new(),
        }
    }
}

/// sourceOperator is a Node in the query plan that reads data from a table.
#[derive(Clone, Debug)]
pub enum SrcOperator {
    // Join operator
    // This operator is used to join two source operators.
    // It takes a left and right source operator, a list of predicates to evaluate,
    // and a boolean indicating whether it is an outer join.
    Join {
        id: usize,
        left: Box<SrcOperator>,
        right: Box<SrcOperator>,
        predicates: Option<Vec<ast::Expr>>,
        outer: bool,
        using: Option<ast::DistinctNames>,
    },
    // Scan operator
    // This operator is used to scan a table.
    // It takes a table to scan and an optional list of predicates to evaluate.
    // The predicates are used to filter rows from the table.
    // e.g. SELECT * FROM t1 WHERE t1.foo = 5
    // The iter_dir are uset to indicate the direction of the iterator.
    // The use of Option for iter_dir is aimed at implementing a conservative optimization strategy: it only pushes
    // iter_dir down to Scan when iter_dir is None, to prevent potential result set errors caused by multiple
    // assignments. for more detailed discussions, please refer to https://github.com/penberg/limbo/pull/376
    Scan {
        id: usize,
        tblRef: BTreeTableRef,
        whereExprs: Option<Vec<ast::Expr>>,
        iterDirection: Option<IterationDirection>,
    },
    // Search operator
    // This operator is used to search for a row in a table using an index
    // (i.e. a primary key or a secondary index)
    Search {
        id: usize,
        tblRef: BTreeTableRef,
        indexSearch: IndexSearch,
        predicates: Option<Vec<ast::Expr>>,
    },
    // Nothing operator
    // This operator is used to represent an empty query.
    // e.g. SELECT * from foo WHERE a!=a will eventually be optimized to Nothing.
    Nothing,
}

#[derive(Clone, Debug)]
pub struct BTreeTableRef {
    pub table: Rc<BTreeTable>,
    /// 要是用了alias的话便是alias 不然是原名
    pub table_identifier: String,
    pub table_index: usize,
}

/// An enum that represents a search operation that can use index
/// (i.e. a primary key or a secondary index)
#[derive(Clone, Debug)]
pub enum IndexSearch {
    /// 它是RowIdSearch的特例 op是equal
    RowidEq { cmp_expr: ast::Expr },

    /// 是IndexSearch特例
    RowidSearch {
        cmp_op: ast::Operator,
        cmp_expr: ast::Expr,
    },

    /// A secondary index search. Uses bytecode instructions like SeekGE, SeekGT etc.
    IndexSearch {
        index: Rc<Index>,
        cmp_op: ast::Operator,
        cmp_expr: ast::Expr,
    },
}

impl SrcOperator {
    pub fn id(&self) -> usize {
        match self {
            SrcOperator::Join { id, .. } => *id,
            SrcOperator::Scan { id, .. } => *id,
            SrcOperator::Search { id, .. } => *id,
            SrcOperator::Nothing => unreachable!(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Direction {
    Ascending,
    Descending,
}

impl Display for Direction {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Direction::Ascending => write!(f, "ASC"),
            Direction::Descending => write!(f, "DESC"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Aggregate {
    pub func: AggFunc,
    pub args: Vec<ast::Expr>,
    pub original_expr: ast::Expr,
}

impl Display for Aggregate {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let args_str = self
            .args
            .iter()
            .map(|arg| arg.to_string())
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, "{:?}({})", self.func, args_str)
    }
}

// For EXPLAIN QUERY PLAN
impl Display for SrcOperator {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        fn fmt_operator(
            operator: &SrcOperator,
            f: &mut Formatter,
            level: usize,
            last: bool,
        ) -> fmt::Result {
            let indent = if level == 0 {
                if last { "`--" } else { "|--" }.to_string()
            } else {
                format!(
                    "   {}{}",
                    "|  ".repeat(level - 1),
                    if last { "`--" } else { "|--" }
                )
            };

            match operator {
                SrcOperator::Join {
                    left,
                    right,
                    predicates,
                    outer,
                    ..
                } => {
                    let join_name = if *outer { "OUTER JOIN" } else { "JOIN" };
                    match predicates
                        .as_ref()
                        .and_then(|ps| if ps.is_empty() { None } else { Some(ps) })
                    {
                        Some(ps) => {
                            let predicates_string = ps
                                .iter()
                                .map(|p| p.to_string())
                                .collect::<Vec<String>>()
                                .join(" AND ");
                            writeln!(f, "{}{} ON {}", indent, join_name, predicates_string)?;
                        }
                        None => writeln!(f, "{}{}", indent, join_name)?,
                    }
                    fmt_operator(left, f, level + 1, false)?;
                    fmt_operator(right, f, level + 1, true)
                }
                SrcOperator::Scan {
                    tblRef: table_reference,
                    whereExprs: filter,
                    ..
                } => {
                    let table_name =
                        if table_reference.table.name == table_reference.table_identifier {
                            table_reference.table_identifier.clone()
                        } else {
                            format!(
                                "{} AS {}",
                                &table_reference.table.name, &table_reference.table_identifier
                            )
                        };
                    let filter_string = filter.as_ref().map(|f| {
                        let filters_string = f
                            .iter()
                            .map(|p| p.to_string())
                            .collect::<Vec<String>>()
                            .join(" AND ");
                        format!("FILTER {}", filters_string)
                    });
                    match filter_string {
                        Some(fs) => writeln!(f, "{}SCAN {} {}", indent, table_name, fs),
                        None => writeln!(f, "{}SCAN {}", indent, table_name),
                    }?;
                    Ok(())
                }
                SrcOperator::Search {
                    tblRef: table_reference,
                    indexSearch: search,
                    ..
                } => {
                    match search {
                        IndexSearch::RowidEq { .. } | IndexSearch::RowidSearch { .. } => writeln!(f, "{}SEARCH {} USING INTEGER PRIMARY KEY (rowid=?)", indent, table_reference.table_identifier)?,
                        IndexSearch::IndexSearch { index, .. } => writeln!(f, "{}SEARCH {} USING INDEX {}", indent, table_reference.table_identifier, index.name)?,
                    }
                    Ok(())
                }
                SrcOperator::Nothing => Ok(()),
            }
        }
        writeln!(f, "QUERY PLAN")?;
        fmt_operator(self, f, 0, true)
    }
}

/**
Returns a bitmask where each bit corresponds to a table in the `tables` vector.
If a table is referenced in the given Operator, the corresponding bit is set to 1.
Example:
  if tables = [(table1, "t1"), (table2, "t2"), (table3, "t3")],
  and the Operator is a join between table1 and table2,
  then the return value will be (in bits): 011
*/
pub fn get_table_ref_bitmask_for_operator<'a>(
    tables: &'a Vec<BTreeTableRef>,
    operator: &'a SrcOperator,
) -> Result<usize> {
    let mut table_refs_mask = 0;
    match operator {
        SrcOperator::Join { left, right, .. } => {
            table_refs_mask |= get_table_ref_bitmask_for_operator(tables, left)?;
            table_refs_mask |= get_table_ref_bitmask_for_operator(tables, right)?;
        }
        SrcOperator::Scan {
            tblRef: table_reference, ..
        } => {
            table_refs_mask |= 1
                << tables
                .iter()
                .position(|t| &t.table_identifier == &table_reference.table_identifier)
                .unwrap();
        }
        SrcOperator::Search {
            tblRef: table_reference, ..
        } => {
            table_refs_mask |= 1 << tables.iter().position(|t| &t.table_identifier == &table_reference.table_identifier).unwrap();
        }
        SrcOperator::Nothing => {}
    }
    Ok(table_refs_mask)
}

/**
Returns a bitmask where each bit corresponds to a table in the `tables` vector.
If a table is referenced in the given AST expression, the corresponding bit is set to 1.
Example:
  if tables = [(table1, "t1"), (table2, "t2"), (table3, "t3")],
  and predicate = "t1.a = t2.b"
  then the return value will be (in bits): 011
*/
pub fn getTblRefsMaskForWhereExpr<'a>(tblRefs: &'a Vec<BTreeTableRef>,
                                      whereExpr: &'a ast::Expr) -> Result<usize> {
    let mut tableRefsMask = 0;
    match whereExpr {
        ast::Expr::Binary(e1, _, e2) => {
            tableRefsMask |= getTblRefsMaskForWhereExpr(tblRefs, e1)?;
            tableRefsMask |= getTblRefsMaskForWhereExpr(tblRefs, e2)?;
        }
        ast::Expr::Column { table, .. } => tableRefsMask |= 1usize << table,
        ast::Expr::Id(_) => unreachable!("Id should be resolved to a Column before optimizer"),
        ast::Expr::Qualified(_, _) => unreachable!("Qualified should be resolved to a Column before optimizer"),
        ast::Expr::Literal(_) => {}
        ast::Expr::Like { lhs, rhs, .. } => {
            tableRefsMask |= getTblRefsMaskForWhereExpr(tblRefs, lhs)?;
            tableRefsMask |= getTblRefsMaskForWhereExpr(tblRefs, rhs)?;
        }
        ast::Expr::FunctionCall { args: Some(args), .. } => {
            for arg in args {
                tableRefsMask |= getTblRefsMaskForWhereExpr(tblRefs, arg)?;
            }
        }
        ast::Expr::InList { lhs, rhs, .. } => {
            tableRefsMask |= getTblRefsMaskForWhereExpr(tblRefs, lhs)?;
            if let Some(rhs_list) = rhs {
                for rhs_expr in rhs_list {
                    tableRefsMask |= getTblRefsMaskForWhereExpr(tblRefs, rhs_expr)?;
                }
            }
        }
        _ => {}
    }

    Ok(tableRefsMask)
}
