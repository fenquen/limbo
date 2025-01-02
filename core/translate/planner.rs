use super::{
    optimizer::Optimizable,
    plan::{
        Aggregate, BTreeTableRef, Direction, GroupBy, Plan, ResultSetColumn, SrcOperator,
    },
};
use crate::{function::Func, schema::Schema, util::normalize_ident, Result};
use sqlite3_parser::ast::{self, FromClause, JoinType, ResultColumn};

pub struct OperatorIdCounter {
    id: usize,
}

impl OperatorIdCounter {
    pub fn new() -> Self {
        Self { id: 1 }
    }

    pub fn get_next_id(&mut self) -> usize {
        let id = self.id;
        self.id += 1;
        id
    }
}

fn resolve_aggregates(expr: &ast::Expr, aggs: &mut Vec<Aggregate>) -> bool {
    if aggs.iter().any(|a| a.original_expr == *expr) {
        return true;
    }
    match expr {
        ast::Expr::FunctionCall { name, args, .. } => {
            let args_count = if let Some(args) = &args {
                args.len()
            } else {
                0
            };
            match Func::resolve_function(normalize_ident(name.0.as_str()).as_str(), args_count) {
                Ok(Func::Agg(f)) => {
                    aggs.push(Aggregate {
                        func: f,
                        args: args.clone().unwrap_or_default(),
                        original_expr: expr.clone(),
                    });
                    true
                }
                _ => {
                    let mut contains_aggregates = false;
                    if let Some(args) = args {
                        for arg in args.iter() {
                            contains_aggregates |= resolve_aggregates(arg, aggs);
                        }
                    }
                    contains_aggregates
                }
            }
        }
        ast::Expr::FunctionCallStar { name, .. } => {
            if let Ok(Func::Agg(f)) =
                Func::resolve_function(normalize_ident(name.0.as_str()).as_str(), 0)
            {
                aggs.push(Aggregate {
                    func: f,
                    args: vec![],
                    original_expr: expr.clone(),
                });
                true
            } else {
                false
            }
        }
        ast::Expr::Binary(lhs, _, rhs) => {
            let mut contains_aggregates = false;
            contains_aggregates |= resolve_aggregates(lhs, aggs);
            contains_aggregates |= resolve_aggregates(rhs, aggs);
            contains_aggregates
        }
        ast::Expr::Unary(_, expr) => {
            let mut contains_aggregates = false;
            contains_aggregates |= resolve_aggregates(expr, aggs);
            contains_aggregates
        }
        // TODO: handle other expressions that may contain aggregates
        _ => false,
    }
}

/// 对sql中的以文本形式的colName进行分析得到更为丰富的信息
fn bindColRef(expr: &mut ast::Expr, tblRefs: &[BTreeTableRef]) -> Result<()> {
    match expr {
        // id 是 literal 意义 对应 select a from table 的 a
        ast::Expr::Id(id) => {
            // true and false are special constants that are effectively aliases for 1 and 0
            // and not identifiers of columns
            if id.0.eq_ignore_ascii_case("true") || id.0.eq_ignore_ascii_case("false") {
                return Ok(());
            }

            let mut match_result = None;

            for (tblIndex, tblRef) in tblRefs.iter().enumerate() {
                let colIndex = tblRef.table.columns.iter().position(|c| c.name.eq_ignore_ascii_case(&id.0));
                if colIndex.is_some() {
                    if match_result.is_some() {
                        crate::bail_parse_error!("column {} is ambiguous", id.0);
                    }

                    let col = tblRef.table.columns.get(colIndex.unwrap()).unwrap();
                    match_result = Some((tblIndex, colIndex.unwrap(), col.primary_key));
                }
            }

            if match_result.is_none() {
                crate::bail_parse_error!("Column {} not found", id.0);
            }

            let (tbl_idx, col_idx, is_primary_key) = match_result.unwrap();
            *expr = ast::Expr::Column {
                database: None, // TODO: support different databases
                table: tbl_idx,
                column: col_idx,
                is_rowid_alias: is_primary_key,
            };

            Ok(())
        }
        ast::Expr::Qualified(tbl, id) => {
            let matching_tbl_idx = tblRefs
                .iter()
                .position(|t| t.table_identifier.eq_ignore_ascii_case(&tbl.0));
            if matching_tbl_idx.is_none() {
                crate::bail_parse_error!("Table {} not found", tbl.0);
            }
            let tbl_idx = matching_tbl_idx.unwrap();
            let col_idx = tblRefs[tbl_idx]
                .table
                .columns
                .iter()
                .position(|c| c.name.eq_ignore_ascii_case(&id.0));
            if col_idx.is_none() {
                crate::bail_parse_error!("Column {} not found", id.0);
            }
            let col = tblRefs[tbl_idx]
                .table
                .columns
                .get(col_idx.unwrap())
                .unwrap();
            *expr = ast::Expr::Column {
                database: None, // TODO: support different databases
                table: tbl_idx,
                column: col_idx.unwrap(),
                is_rowid_alias: col.is_rowid_alias,
            };
            Ok(())
        }
        ast::Expr::Between {
            lhs,
            not: _,
            start,
            end,
        } => {
            bindColRef(lhs, tblRefs)?;
            bindColRef(start, tblRefs)?;
            bindColRef(end, tblRefs)?;
            Ok(())
        }
        ast::Expr::Binary(expr, _operator, expr1) => {
            bindColRef(expr, tblRefs)?;
            bindColRef(expr1, tblRefs)?;
            Ok(())
        }
        ast::Expr::Case {
            base,
            when_then_pairs,
            else_expr,
        } => {
            if let Some(base) = base {
                bindColRef(base, tblRefs)?;
            }
            for (when, then) in when_then_pairs {
                bindColRef(when, tblRefs)?;
                bindColRef(then, tblRefs)?;
            }
            if let Some(else_expr) = else_expr {
                bindColRef(else_expr, tblRefs)?;
            }
            Ok(())
        }
        ast::Expr::Cast { expr, type_name: _ } => bindColRef(expr, tblRefs),
        ast::Expr::Collate(expr, _string) => bindColRef(expr, tblRefs),
        ast::Expr::FunctionCall {
            name: _,
            distinctness: _,
            args,
            order_by: _,
            filter_over: _,
        } => {
            if let Some(args) = args {
                for arg in args {
                    bindColRef(arg, tblRefs)?;
                }
            }
            Ok(())
        }
        // Column references cannot exist before binding
        ast::Expr::Column { .. } => unreachable!(),
        ast::Expr::DoublyQualified(_, _, _) => todo!(),
        ast::Expr::Exists(_) => todo!(),
        ast::Expr::FunctionCallStar { .. } => Ok(()),
        ast::Expr::InList { lhs, not: _, rhs } => {
            bindColRef(lhs, tblRefs)?;
            if let Some(rhs) = rhs {
                for arg in rhs {
                    bindColRef(arg, tblRefs)?;
                }
            }
            Ok(())
        }
        ast::Expr::InSelect { .. } => todo!(),
        ast::Expr::InTable { .. } => todo!(),
        ast::Expr::IsNull(expr) => {
            bindColRef(expr, tblRefs)?;
            Ok(())
        }
        ast::Expr::Like { lhs, rhs, .. } => {
            bindColRef(lhs, tblRefs)?;
            bindColRef(rhs, tblRefs)?;
            Ok(())
        }
        ast::Expr::Literal(_) => Ok(()),
        ast::Expr::Name(_) => todo!(),
        ast::Expr::NotNull(expr) => {
            bindColRef(expr, tblRefs)?;
            Ok(())
        }
        ast::Expr::Parenthesized(expr) => {
            for e in expr.iter_mut() {
                bindColRef(e, tblRefs)?;
            }
            Ok(())
        }
        ast::Expr::Raise(_, _) => todo!(),
        ast::Expr::Subquery(_) => todo!(),
        ast::Expr::Unary(_, expr) => {
            bindColRef(expr, tblRefs)?;
            Ok(())
        }
        ast::Expr::Variable(_) => todo!(),
    }
}

#[allow(clippy::extra_unused_lifetimes)]
pub fn prepareSelPlan<'a>(schema: &Schema, select: ast::Select) -> Result<Plan> {
    match select.body.select {
        ast::OneSelect::Select {
            columns: resultCols,
            from: fromClause,
            where_clause: whereExpr,
            group_by: mut groupBy,
            ..
        } => {
            if resultCols.is_empty() {
                crate::bail_parse_error!("SELECT without columns is not allowed");
            }

            let mut operatorIdCounter = OperatorIdCounter::new();

            let (srcOperator, tblRefs) = parseFromClause(schema, fromClause, &mut operatorIdCounter)?;

            let mut plan = Plan {
                srcOperator,
                resultCols: vec![],
                whereExprs: None,
                group_by: None,
                orderBys: None,
                aggregates: vec![],
                limit: None,
                tblRefs,
                indexes: schema.indexes.clone().into_values().flatten().collect(),
                containsConstantFalseCondition: false,
            };

            // Parse the WHERE clause
            if let Some(w) = whereExpr {
                let mut predicates = vec![];
                break_predicate_at_and_boundaries(w, &mut predicates);
                for expr in predicates.iter_mut() {
                    bindColRef(expr, &plan.tblRefs)?;
                }
                plan.whereExprs = Some(predicates);
            }

            let mut aggregate_expressions = Vec::new();

            for column in resultCols.clone() {
                match column {
                    ResultColumn::Star => plan.srcOperator.select_star(&mut plan.resultCols),
                    ResultColumn::TableStar(name) => {
                        let name_normalized = normalize_ident(name.0.as_str());
                        let referenced_table =
                            plan.tblRefs.iter().find(|t| t.table_identifier == name_normalized);

                        if referenced_table.is_none() {
                            crate::bail_parse_error!("Table {} not found", name.0);
                        }

                        let table_reference = referenced_table.unwrap();
                        for (idx, col) in table_reference.table.columns.iter().enumerate() {
                            plan.resultCols.push(ResultSetColumn {
                                expr: ast::Expr::Column {
                                    database: None, // TODO: support different databases
                                    table: table_reference.table_index,
                                    column: idx,
                                    is_rowid_alias: col.is_rowid_alias,
                                },
                                contains_aggregates: false,
                            });
                        }
                    }
                    // select a from table 的 a
                    ResultColumn::Expr(mut expr, _) => {
                        bindColRef(&mut expr, &plan.tblRefs)?;

                        match &expr {
                            ast::Expr::FunctionCall { name, args, .. } => {
                                let args_count = if let Some(args) = &args {
                                    args.len()
                                } else {
                                    0
                                };

                                match Func::resolve_function(normalize_ident(name.0.as_str()).as_str(), args_count) {
                                    Ok(Func::Agg(f)) => {
                                        let agg = Aggregate {
                                            func: f,
                                            args: args.as_ref().unwrap().clone(),
                                            original_expr: expr.clone(),
                                        };
                                        aggregate_expressions.push(agg.clone());
                                        plan.resultCols.push(ResultSetColumn {
                                            expr: expr.clone(),
                                            contains_aggregates: true,
                                        });
                                    }
                                    Ok(_) => {
                                        let contains_aggregates =
                                            resolve_aggregates(&expr, &mut aggregate_expressions);
                                        plan.resultCols.push(ResultSetColumn {
                                            expr: expr.clone(),
                                            contains_aggregates,
                                        });
                                    }
                                    _ => {}
                                }
                            }
                            ast::Expr::FunctionCallStar { name, .. } => {
                                if let Ok(Func::Agg(f)) = Func::resolve_function(normalize_ident(name.0.as_str()).as_str(), 0) {
                                    let agg = Aggregate {
                                        func: f,
                                        args: vec![ast::Expr::Literal(ast::Literal::Numeric("1".to_string(), ))],
                                        original_expr: expr.clone(),
                                    };

                                    aggregate_expressions.push(agg.clone());
                                    plan.resultCols.push(ResultSetColumn {
                                        expr: expr.clone(),
                                        contains_aggregates: true,
                                    });
                                } else {
                                    crate::bail_parse_error!("Invalid aggregate function: {}",name.0);
                                }
                            }
                            expr => {
                                let contains_aggregates = resolve_aggregates(expr, &mut aggregate_expressions);

                                plan.resultCols.push(ResultSetColumn {
                                    expr: expr.clone(),
                                    contains_aggregates,
                                });
                            }
                        }
                    }
                }
            }

            if let Some(mut group_by) = groupBy {
                for expr in group_by.exprs.iter_mut() {
                    bindColRef(expr, &plan.tblRefs)?;
                }

                plan.group_by = Some(GroupBy {
                    exprs: group_by.exprs,
                    having: if let Some(having) = group_by.having {
                        let mut predicates = vec![];
                        break_predicate_at_and_boundaries(having, &mut predicates);
                        for expr in predicates.iter_mut() {
                            bindColRef(expr, &plan.tblRefs)?;
                            let contains_aggregates =
                                resolve_aggregates(expr, &mut aggregate_expressions);
                            if !contains_aggregates {
                                // TODO: sqlite allows HAVING clauses with non aggregate expressions like
                                // HAVING id = 5. We should support this too eventually (I guess).
                                // sqlite3-parser does not support HAVING without group by though, so we'll
                                // need to either make a PR or add it to our vendored version.
                                crate::bail_parse_error!(
                                    "HAVING clause must contain an aggregate function"
                                );
                            }
                        }
                        Some(predicates)
                    } else {
                        None
                    },
                });
            }

            plan.aggregates = aggregate_expressions;

            // Parse the ORDER BY clause
            if let Some(order_by) = select.order_by {
                let mut key = Vec::new();

                for o in order_by {
                    // if the ORDER BY expression is a number, interpret it as an 1-indexed column number
                    // otherwise, interpret it normally as an expression
                    let mut expr =
                        if let ast::Expr::Literal(ast::Literal::Numeric(num)) = &o.expr {
                            let column_number = num.parse::<usize>()?;
                            if column_number == 0 {
                                crate::bail_parse_error!("invalid column index: {}", column_number);
                            }

                            match resultCols.get(column_number - 1) {
                                Some(ResultColumn::Expr(e, _)) => e.clone(),
                                None => crate::bail_parse_error!("invalid column index: {}", column_number),
                                _ => todo!(),
                            }
                        } else {
                            o.expr
                        };

                    bindColRef(&mut expr, &plan.tblRefs)?;
                    resolve_aggregates(&expr, &mut plan.aggregates);

                    key.push((
                        expr,
                        o.order.map_or(Direction::Ascending, |o| match o {
                            ast::SortOrder::Asc => Direction::Ascending,
                            ast::SortOrder::Desc => Direction::Descending,
                        }),
                    ));
                }

                plan.orderBys = Some(key);
            }

            // Parse the LIMIT clause
            if let Some(limit) = &select.limit {
                plan.limit = match &limit.expr {
                    ast::Expr::Literal(ast::Literal::Numeric(n)) => {
                        let l = n.parse()?;
                        Some(l)
                    }
                    _ => todo!(),
                }
            }

            // unoptimized  plan
            Ok(plan)
        }
        _ => todo!(),
    }
}

#[allow(clippy::type_complexity)]
fn parseFromClause(schema: &Schema,
                   fromClause: Option<FromClause>,
                   operator_id_counter: &mut OperatorIdCounter) -> Result<(SrcOperator, Vec<BTreeTableRef>)> {
    if fromClause.as_ref().and_then(|f| f.select.as_ref()).is_none() {
        return Ok((SrcOperator::Nothing, vec![]));
    }

    let fromClause = fromClause.unwrap();

    let firstTblRef =
        match *fromClause.select.unwrap() {
            ast::SelectTable::Table(qualifiedName, alias, _) => {
                let Some(table) = schema.getTbl(&qualifiedName.name.0) else {
                    crate::bail_parse_error!("Table {} not found", qualifiedName.name.0);
                };

                let alias = alias.map(|a| match a {
                    ast::As::As(alias) => alias,
                    ast::As::Elided(alias) => alias,
                }).map(|a| a.0);

                BTreeTableRef {
                    table: table.clone(),
                    table_identifier: alias.unwrap_or(qualifiedName.name.0),
                    table_index: 0,
                }
            }
            _ => todo!(),
        };

    let mut srcOperator = SrcOperator::Scan {
        tblRef: firstTblRef.clone(),
        whereExprs: None,
        id: operator_id_counter.get_next_id(),
        iterDirection: None,
    };

    let mut tblRefs = vec![firstTblRef];

    // 后边起的tbl的index是1了
    let mut tblIndex = 1;
    for joinedSelTbl in fromClause.joins.unwrap_or_default().into_iter() {
        let (rightSrcOperator, outer, using, whereExprs) =
            parseJoin(schema,
                      joinedSelTbl,
                      operator_id_counter,
                      &mut tblRefs,
                      tblIndex)?;

        // srcOperator不断累加
        srcOperator = SrcOperator::Join {
            left: Box::new(srcOperator),
            right: Box::new(rightSrcOperator),
            predicates: whereExprs,
            outer,
            using,
            id: operator_id_counter.get_next_id(),
        };

        tblIndex += 1;
    }

    Ok((srcOperator, tblRefs))
}

fn parseJoin(schema: &Schema,
             joinedSelTbl: ast::JoinedSelectTable,
             operatorIdCounter: &mut OperatorIdCounter,
             tblRefsCollected: &mut Vec<BTreeTableRef>,
             curTblIndex: usize) -> Result<(SrcOperator, bool, Option<ast::DistinctNames>, Option<Vec<ast::Expr>>)> {
    let ast::JoinedSelectTable {
        operator: joinOperator,
        table,
        constraint: joinConstraint,
    } = joinedSelTbl;

    let tblRef = match table {
        ast::SelectTable::Table(qualified_name, maybe_alias, _) => {
            let Some(table) = schema.getTbl(&qualified_name.name.0) else {
                crate::bail_parse_error!("Table {} not found", qualified_name.name.0);
            };

            let alias =
                maybe_alias.map(|a| match a {
                    ast::As::As(alias) => alias,
                    ast::As::Elided(alias) => alias,
                }).map(|a| a.0);

            BTreeTableRef {
                table: table.clone(),
                table_identifier: alias.unwrap_or(qualified_name.name.0),
                table_index: curTblIndex,
            }
        }
        _ => todo!(),
    };

    tblRefsCollected.push(tblRef.clone());

    let (isOuter, natureJoin) = match joinOperator {
        ast::JoinOperator::TypedJoin(Some(joinType)) => {
            let isOuter = joinType.contains(JoinType::OUTER);
            let isNature = joinType.contains(JoinType::NATURAL);
            (isOuter, isNature)
        }
        _ => (false, false),
    };

    // 使用 using 的join : 其实是 join on 的简写 select from A join B using (id) 等同 select from A join B on A.id = B.id
    // natural join: select from A natural join b, 是隐式的join 等同 select from A join B on A.id = b.id 因为id是两边否有的字段
    // 和 JOIN... ON 或 JOIN... USING）不同，不需要显式地指定连接条件。会自动查找两个表中所有名称相同且数据类型相同的列，并以这些列作为连接条件进行连接
    if natureJoin && joinConstraint.is_some() {
        // 用了nature join 不能写on了
        crate::bail_parse_error!("NATURAL JOIN cannot be combined with ON or USING clause");
    }

    let joinConstraint =
        // 使用了nature join的话 需要找到实际 join的字段 以using的形式表达
        if natureJoin {
            let leftTblRefs = &tblRefsCollected[..curTblIndex];
            assert!(!leftTblRefs.is_empty());

            let rightCols = &tblRefsCollected[curTblIndex].table.columns;

            let mut colNamesInUsing = None;

            // TODO: O(n^2) maybe not great for large tables or big multiway joins
            for rightCol in rightCols.iter() {
                let mut found = false;

                'a:
                for leftTblRef in leftTblRefs.iter() {
                    for leftCol in leftTblRef.table.columns.iter() {
                        // 要得到两个表名字相同的col的
                        if leftCol.name == rightCol.name {
                            if colNamesInUsing.is_none() {
                                colNamesInUsing = Some(ast::DistinctNames::new(ast::Name(leftCol.name.clone())));
                            } else {
                                colNamesInUsing.as_mut().unwrap().insert(ast::Name(leftCol.name.clone())).unwrap();
                            }

                            found = true;
                            break 'a;
                        }
                    }
                }
            }

            if colNamesInUsing.is_none() {
                crate::bail_parse_error!("No columns found to NATURAL join on");
            }

            Some(ast::JoinConstraint::Using(colNamesInUsing.unwrap()))
        } else {
            joinConstraint
        };


    // 对应 on a.id = b.id , using(id)
    let mut joinOnExprs = None;

    // select from a join b using (id) 等同 select from a join b on a.id = b.id
    // using 使用的标识符列表
    let mut colNamesInUsing = None;

    if let Some(joinConstraint) = joinConstraint {
        match joinConstraint {
            // 普通的join on
            ast::JoinConstraint::On(expr) => {
                let mut preds = vec![];

                // 读取 a.id  = b.id and b.id = d.id 的 a.id = b.id, b.id = d.id
                break_predicate_at_and_boundaries(expr, &mut preds);

                for predicate in preds.iter_mut() {
                    bindColRef(predicate, tblRefsCollected)?;
                }

                joinOnExprs = Some(preds);
            }
            // join 使用 using 还是要将其变为和 join on 相同
            ast::JoinConstraint::Using(colNamesInUsing0) => {
                // USING join is replaced with a list of equality predicates
                let mut joinOnExprs0 = vec![];

                for colNameInUsing in colNamesInUsing0.iter() {
                    let colNameInUsing = normalize_ident(colNameInUsing.0.as_str());

                    let leftTblRefs = &tblRefsCollected[..curTblIndex];
                    assert!(!leftTblRefs.is_empty());

                    let rightTblRef = &tblRefsCollected[curTblIndex];

                    // using对应的字段名是两表都有的 到两的表是挨个比对colName
                    let leftCol = {
                        let mut leftCol = None;

                        for (leftTblIndex, leftTblRef) in leftTblRefs.iter().enumerate() {
                            leftCol = leftTblRef.table.columns.iter().enumerate().find(|(_, col)| col.name == colNameInUsing).map(|(colIndex, col)| (leftTblIndex, colIndex, col));
                            if leftCol.is_some() {
                                break;
                            }
                        }

                        if leftCol.is_none() {
                            crate::bail_parse_error!("cannot join using column {} - column not present in all tables",colNameInUsing);
                        }

                        leftCol.unwrap()
                    };

                    let rightCol = {
                        let rightCol = rightTblRef.table.columns.iter().enumerate().find(|(_, col)| col.name == colNameInUsing);
                        if rightCol.is_none() {
                            crate::bail_parse_error!("cannot join using column {} - column not present in all tables", colNameInUsing);
                        }

                        rightCol.unwrap()
                    };

                    let (leftTblIndex, leftColIndex, leftCol) = leftCol;
                    let (rightColIndex, rightCol) = rightCol;

                    // 还是要要变为传统的on形式
                    joinOnExprs0.push(ast::Expr::Binary(
                        Box::new(ast::Expr::Column {
                            database: None,
                            table: leftTblIndex,
                            column: leftColIndex,
                            is_rowid_alias: leftCol.is_rowid_alias,
                        }),
                        ast::Operator::Equals,
                        Box::new(ast::Expr::Column {
                            database: None,
                            table: rightTblRef.table_index,
                            column: rightColIndex,
                            is_rowid_alias: rightCol.is_rowid_alias,
                        }),
                    ));
                }

                joinOnExprs = Some(joinOnExprs0);

                colNamesInUsing = Some(colNamesInUsing0);
            }
        }
    }

    Ok((
        SrcOperator::Scan {
            tblRef: tblRef.clone(),
            whereExprs: None,
            id: operatorIdCounter.get_next_id(),
            iterDirection: None,
        },
        isOuter,
        colNamesInUsing,
        joinOnExprs,
    ))
}

fn break_predicate_at_and_boundaries(predicate: ast::Expr, out: &mut Vec<ast::Expr>) {
    match predicate {
        ast::Expr::Binary(left, ast::Operator::And, right) => {
            break_predicate_at_and_boundaries(*left, out);
            break_predicate_at_and_boundaries(*right, out);
        }
        _ => out.push(predicate),
    }
}
