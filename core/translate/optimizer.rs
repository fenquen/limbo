use std::rc::Rc;

use sqlite3_parser::ast;

use crate::{schema::Index, Result};

use super::plan::{
    getTblRefsMaskForWhereExpr, get_table_ref_bitmask_for_operator, BTreeTableRef,
    Direction, IterationDirection, Plan, IndexSearch, SrcOperator,
};


/// Make a few passes over the plan to optimize it.
// TODO: these could probably be done in less passes, but having them separate makes them easier to understand
pub fn optimize_plan(mut selPlan: Plan) -> Result<Plan> {
    // graph 实现
    if let ConstantCondEliminationResult::ImpossibleCondition =
        eliminate_constants(&mut selPlan.srcOperator, &mut selPlan.whereExprs)? {
        selPlan.containsConstantFalseCondition = true;
        return Ok(selPlan);
    }

    pushWhereExprs(&mut selPlan.srcOperator,
                   &mut selPlan.whereExprs,
                   &selPlan.tblRefs)?;

    // graph 实现
    tryIndex(&mut selPlan.srcOperator,
             &selPlan.tblRefs,
             &selPlan.indexes)?;

    eliminateUnnecessaryOrderBy(&mut selPlan.srcOperator,
                                &mut selPlan.orderBys,
                                &selPlan.tblRefs,
                                &selPlan.indexes)?;

    Ok(selPlan)
}

/// SELECT * FROM t1 JOIN t2 JOIN t3 WHERE t1.a = t2.a AND t2.b = t3.b AND t1.c = 1
/// the predicate t1.c = 1 can be pushed to t1 and will be evaluated in the first (outermost) loop,
/// the predicate t1.a = t2.a can be pushed to t2 and will be evaluated in the second loop
/// while t2.b = t3.b will be evaluated in the third loop.
fn pushWhereExprs(srcOperator: &mut SrcOperator,
                  whereExprs: &mut Option<Vec<ast::Expr>>,
                  tblRefs: &Vec<BTreeTableRef>) -> Result<()> {
    // First try to push down any predicates from the WHERE clause
    if let Some(predicates) = whereExprs {
        let mut i = 0;

        while i < predicates.len() {
            let whereExpr = predicates[i].take_ownership();

            // If predicate was successfully pushed (None returned), remove it from WHERE
            let Some(predicate) = pushWhereExpr(srcOperator, whereExpr, tblRefs)? else {
                predicates.remove(i);
                continue;
            };

            predicates[i] = predicate;

            i += 1;
        }

        // Clean up empty WHERE clause
        if predicates.is_empty() {
            *whereExprs = None;
        }
    }

    match srcOperator {
        SrcOperator::Join {
            left,
            right,
            predicates,
            outer,
            ..
        } => {
            // Recursively push predicates down both sides of join
            pushWhereExprs(left, whereExprs, tblRefs)?;
            pushWhereExprs(right, whereExprs, tblRefs)?;

            if predicates.is_none() {
                return Ok(());
            }

            let predicates = predicates.as_mut().unwrap();

            let mut i = 0;
            while i < predicates.len() {
                let predicate_owned = predicates[i].take_ownership();

                // For a join like SELECT * FROM left INNER JOIN right ON left.id = right.id AND left.name = 'foo'
                // the predicate 'left.name = 'foo' can already be evaluated in the outer loop (left side of join)
                // because the row can immediately be skipped if left.name != 'foo'.
                // But for a LEFT JOIN, we can't do this since we need to ensure that all rows from the left table are included,
                // even if there are no matching rows from the right table. This is why we can't push LEFT JOIN predicates to the left side.
                let push_result = if *outer {
                    Some(predicate_owned)
                } else {
                    pushWhereExpr(left, predicate_owned, tblRefs)?
                };

                // Try pushing to left side first (see comment above for reasoning)
                let Some(predicate) = push_result else {
                    predicates.remove(i);
                    continue;
                };

                // Then try right side
                let Some(predicate) = pushWhereExpr(right, predicate, tblRefs)? else {
                    predicates.remove(i);
                    continue;
                };

                // If neither side could take it, keep in join predicates (not sure if this actually happens in practice)
                // this is effectively the same as pushing to the right side, so maybe it could be removed and assert here
                // that we don't reach this code
                predicates[i] = predicate;
                i += 1;
            }

            Ok(())
        }
        _ => Ok(())
    }
}

/// try to use index
fn tryIndex(srcOperator: &mut SrcOperator,
            tblRefs: &[BTreeTableRef],
            indexesInSchema: &[Rc<Index>]) -> Result<()> {
    match srcOperator {
        SrcOperator::Scan { tblRef, whereExprs, id, .. } => {
            if whereExprs.is_none() {
                return Ok(());
            }

            let whereExprs = whereExprs.as_mut().unwrap();

            for i in 0..whereExprs.len() {
                let whereExpr = whereExprs[i].take_ownership();
                let whereExprTblIndex =
                    tblRefs.iter().position(|t| { Rc::ptr_eq(&t.table, &tblRef.table) && t.table_identifier == tblRef.table_identifier }).unwrap();

                match extractIndexSearchExpr(whereExpr, whereExprTblIndex, tblRefs, indexesInSchema)? {
                    Either::Left(non_index_using_expr) => whereExprs[i] = non_index_using_expr,
                    Either::Right(indexSearch) => {
                        whereExprs.remove(i);

                        // 原来的scan换为index search了
                        *srcOperator = SrcOperator::Search {
                            id: *id,
                            tblRef: tblRef.clone(),
                            predicates: Some(whereExprs.clone()),
                            indexSearch: indexSearch,
                        };

                        return Ok(());
                    }
                }
            }

            Ok(())
        }
        SrcOperator::Join { left, right, .. } => {
            tryIndex(left, tblRefs, indexesInSchema)?;
            tryIndex(right, tblRefs, indexesInSchema)?;
            Ok(())
        }
        _ => Ok(()),
    }
}

pub fn extractIndexSearchExpr(whereExpr: ast::Expr,
                              whereExprTblIndex: usize,
                              referenced_tables: &[BTreeTableRef],
                              available_indexes: &[Rc<Index>]) -> Result<Either<ast::Expr, IndexSearch>> {
    match whereExpr {
        ast::Expr::Binary(mut leftExpr, operator, mut rightExpr) => {
            if leftExpr.isPrimaryKeyCol(whereExprTblIndex) {
                match operator {
                    ast::Operator::Equals => return Ok(Either::Right(IndexSearch::RowidEq { cmp_expr: *rightExpr })),
                    ast::Operator::Greater
                    | ast::Operator::GreaterEquals
                    | ast::Operator::Less
                    | ast::Operator::LessEquals => {
                        return Ok(Either::Right(IndexSearch::RowidSearch {
                            cmp_op: operator,
                            cmp_expr: *rightExpr,
                        }));
                    }
                    _ => {}
                }
            }

            if rightExpr.isPrimaryKeyCol(whereExprTblIndex) {
                match operator {
                    ast::Operator::Equals => return Ok(Either::Right(IndexSearch::RowidEq { cmp_expr: *leftExpr })),
                    ast::Operator::Greater
                    | ast::Operator::GreaterEquals
                    | ast::Operator::Less
                    | ast::Operator::LessEquals => {
                        return Ok(Either::Right(IndexSearch::RowidSearch {
                            cmp_op: operator,
                            cmp_expr: *leftExpr,
                        }));
                    }
                    _ => {}
                }
            }

            if let Some(index_index) = leftExpr.getIndex(whereExprTblIndex, referenced_tables, available_indexes)? {
                match operator {
                    ast::Operator::Equals
                    | ast::Operator::Greater
                    | ast::Operator::GreaterEquals
                    | ast::Operator::Less
                    | ast::Operator::LessEquals => {
                        return Ok(Either::Right(IndexSearch::IndexSearch {
                            index: available_indexes[index_index].clone(),
                            cmp_op: operator,
                            cmp_expr: *rightExpr,
                        }));
                    }
                    _ => {}
                }
            }

            if let Some(index_index) = rightExpr.getIndex(whereExprTblIndex, referenced_tables, available_indexes)? {
                match operator {
                    ast::Operator::Equals
                    | ast::Operator::Greater
                    | ast::Operator::GreaterEquals
                    | ast::Operator::Less
                    | ast::Operator::LessEquals => {
                        return Ok(Either::Right(IndexSearch::IndexSearch {
                            index: available_indexes[index_index].clone(),
                            cmp_op: operator,
                            cmp_expr: *leftExpr,
                        }));
                    }
                    _ => {}
                }
            }

            Ok(Either::Left(ast::Expr::Binary(leftExpr, operator, rightExpr)))
        }
        _ => Ok(Either::Left(whereExpr)),
    }
}

fn eliminateUnnecessaryOrderBy(srcOperator: &mut SrcOperator,
                               orderBy: &mut Option<Vec<(ast::Expr, Direction)>>,
                               tblRefs: &[BTreeTableRef],
                               indexesInSchema: &Vec<Rc<Index>>) -> Result<()> {
    if orderBy.is_none() {
        return Ok(());
    }

    let orderBys = orderBy.as_mut().unwrap();

    // 目前还不能应对多个order by
    if orderBys.len() != 1 {
        // TODO: handle multiple order by keys
        return Ok(());
    }

    let (key, direction) = orderBys.first_mut().unwrap();

    // 如果 要排序的字段是 index, 下压
    if srcOperatorAlreadyOrdered(srcOperator, key, tblRefs, indexesInSchema)? {
        match srcOperator {
            SrcOperator::Scan { iterDirection: iter_dir, .. } => {
                if iter_dir.is_none() {
                    match direction {
                        Direction::Ascending => *iter_dir = Some(IterationDirection::Forwards),
                        Direction::Descending => *iter_dir = Some(IterationDirection::Backwards),
                    }
                }
            }
            _ => todo!(),
        }

        *orderBy = None;
    }

    Ok(())
}

fn srcOperatorAlreadyOrdered(srcOperator: &mut SrcOperator,
                             key: &mut ast::Expr,
                             tblRefs: &[BTreeTableRef],
                             indexesInSchema: &Vec<Rc<Index>>) -> Result<bool> {
    match srcOperator {
        SrcOperator::Scan { tblRef, .. } => Ok(key.isPrimaryKeyCol(tblRef.table_index)),
        SrcOperator::Search { tblRef, indexSearch: search, .. } =>
            match search {
                IndexSearch::RowidEq { .. } => Ok(key.isPrimaryKeyCol(tblRef.table_index)),
                IndexSearch::RowidSearch { .. } => Ok(key.isPrimaryKeyCol(tblRef.table_index)),
                IndexSearch::IndexSearch { index, .. } => {
                    let index_idx =
                        key.getIndex(tblRef.table_index,
                                     tblRefs,
                                     indexesInSchema)?;

                    Ok(index_idx.map(|i| Rc::ptr_eq(&indexesInSchema[i], index)).unwrap_or(false))
                }
            },
        SrcOperator::Join { left, .. } => srcOperatorAlreadyOrdered(left, key, tblRefs, indexesInSchema),
        _ => Ok(false),
    }
}

#[derive(Debug, PartialEq, Clone)]
enum ConstantCondEliminationResult {
    Continue,
    /// where 1=0
    ImpossibleCondition,
}

// removes predicates that are always true
// returns a ConstantEliminationResult indicating whether any predicates are always false
fn eliminate_constants(operator: &mut SrcOperator,
                       where_clause: &mut Option<Vec<ast::Expr>>) -> Result<ConstantCondEliminationResult> {
    if let Some(predicates) = where_clause {
        let mut i = 0;
        while i < predicates.len() {
            let whereExpr = &predicates[i];

            if whereExpr.is_always_true()? {
                predicates.remove(i);
            } else if whereExpr.is_always_false()? {
                // any false predicate in a list of conjuncts (AND-ed predicates) will make the whole list false
                predicates.truncate(0);
                return Ok(ConstantCondEliminationResult::ImpossibleCondition);
            }

            i += 1;
        }
    }
    match operator {
        SrcOperator::Join {
            left,
            right,
            predicates,
            outer,
            ..
        } => {
            if eliminate_constants(left, where_clause)? == ConstantCondEliminationResult::ImpossibleCondition {
                return Ok(ConstantCondEliminationResult::ImpossibleCondition);
            }

            if eliminate_constants(right, where_clause)? == ConstantCondEliminationResult::ImpossibleCondition && !*outer {
                return Ok(ConstantCondEliminationResult::ImpossibleCondition);
            }

            if predicates.is_none() {
                return Ok(ConstantCondEliminationResult::Continue);
            }

            let predicates = predicates.as_mut().unwrap();

            let mut i = 0;
            while i < predicates.len() {
                let predicate = &mut predicates[i];
                if predicate.is_always_true()? {
                    predicates.remove(i);
                } else if predicate.is_always_false()? {
                    if !*outer {
                        predicates.truncate(0);
                        return Ok(ConstantCondEliminationResult::ImpossibleCondition);
                    }
                    // in an outer join, we can't skip rows, so just replace all constant false predicates with 0
                    // so we don't later have to evaluate anything more complex or special-case the identifiers true and false
                    // which are just aliases for 1 and 0
                    *predicate = ast::Expr::Literal(ast::Literal::Numeric("0".to_string()));
                    i += 1;
                } else {
                    i += 1;
                }
            }

            Ok(ConstantCondEliminationResult::Continue)
        }
        SrcOperator::Scan { whereExprs: predicates, .. } => {
            if let Some(ps) = predicates {
                let mut i = 0;
                while i < ps.len() {
                    let predicate = &ps[i];
                    if predicate.is_always_true()? {
                        // true predicates can be removed since they don't affect the result
                        ps.remove(i);
                    } else if predicate.is_always_false()? {
                        // any false predicate in a list of conjuncts (AND-ed predicates) will make the whole list false
                        ps.truncate(0);
                        return Ok(ConstantCondEliminationResult::ImpossibleCondition);
                    } else {
                        i += 1;
                    }
                }

                if ps.is_empty() {
                    *predicates = None;
                }
            }
            Ok(ConstantCondEliminationResult::Continue)
        }
        SrcOperator::Search { predicates, .. } => {
            if let Some(predicates) = predicates {
                let mut i = 0;
                while i < predicates.len() {
                    let predicate = &predicates[i];
                    if predicate.is_always_true()? {
                        // true predicates can be removed since they don't affect the result
                        predicates.remove(i);
                    } else if predicate.is_always_false()? {
                        // any false predicate in a list of conjuncts (AND-ed predicates) will make the whole list false
                        predicates.truncate(0);
                        return Ok(ConstantCondEliminationResult::ImpossibleCondition);
                    } else {
                        i += 1;
                    }
                }
            }

            Ok(ConstantCondEliminationResult::Continue)
        }
        SrcOperator::Nothing => Ok(ConstantCondEliminationResult::Continue),
    }
}


/// Push a single predicate down the tree, as far as possible.
/// Returns Ok(None) if the predicate was pushed, otherwise returns itself as Ok(Some(predicate))
fn pushWhereExpr(srcOperator: &mut SrcOperator,
                 whereExpr: ast::Expr,
                 tblRefs: &Vec<BTreeTableRef>) -> Result<Option<ast::Expr>> {
    match srcOperator {
        SrcOperator::Scan { whereExprs, tblRef, .. } => {
            // Find position of this table in referenced_tables array
            let tblIndex = tblRefs.iter().position(|t| t.table_identifier == tblRef.table_identifier).unwrap();

            // 这个的whereExpr用到了sql中的哪些table
            let tblRefsMask = getTblRefsMaskForWhereExpr(tblRefs, &whereExpr)?;

            // SELECT * FROM t1 JOIN t2 JOIN t3
            // t1 is position 0 (001), t2 is position 1 (010), t3 is position 2 (100)
            // To push a predicate to a given table, it can only reference that table and tables to its left
            // Example: For table t2 at position 1 (bit 010):
            // - Can push: 011 (t2 + t1), 001 (just t1), 010 (just t2)
            // - Can't push: 110 (t2 + t3)
            // 意味着whereExpr对应的字段是在右边的表上
            if tblRefsMask >= 1 << (tblIndex + 1) {
                return Ok(Some(whereExpr));
            }

            // whereExpr 落地到这个表
            if whereExprs.is_none() {
                whereExprs.replace(vec![whereExpr]);
            } else {
                whereExprs.as_mut().unwrap().push(whereExpr);
            }

            Ok(None)
        }
        SrcOperator::Join {
            left,
            right,
            predicates: join_on_preds,
            outer,
            ..
        } => {
            // Try pushing to left side first
            let push_result_left = pushWhereExpr(left, whereExpr, tblRefs)?;
            if push_result_left.is_none() {
                return Ok(None);
            }

            // Then try right side
            let push_result_right = pushWhereExpr(right, push_result_left.unwrap(), tblRefs)?;
            if push_result_right.is_none() {
                return Ok(None);
            }

            // For LEFT JOIN, predicates must stay at join level
            if *outer {
                return Ok(Some(push_result_right.unwrap()));
            }

            let pred = push_result_right.unwrap();

            // Get bitmasks for tables referenced in predicate and both sides of join
            let table_refs_bitmask = getTblRefsMaskForWhereExpr(tblRefs, &pred)?;
            let left_bitmask = get_table_ref_bitmask_for_operator(tblRefs, left)?;
            let right_bitmask = get_table_ref_bitmask_for_operator(tblRefs, right)?;

            // If predicate doesn't reference tables from both sides, it can't be a join condition
            if table_refs_bitmask & left_bitmask == 0 || table_refs_bitmask & right_bitmask == 0 {
                return Ok(Some(pred));
            }

            // Add as join predicate since it references both sides
            if join_on_preds.is_none() {
                join_on_preds.replace(vec![pred]);
            } else {
                join_on_preds.as_mut().unwrap().push(pred);
            }

            Ok(None)
        }
        // Search nodes don't exist yet at this point; Scans are transformed to Search in use_indexes()
        SrcOperator::Search { .. } => unreachable!(),
        SrcOperator::Nothing => Ok(Some(whereExpr)),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstantPredicate {
    AlwaysTrue,
    AlwaysFalse,
}


// Helper trait for expressions that can be optimized Implemented for ast::Expr
pub trait Optimizable {
    // if the expression is a constant expression e.g. '1', returns the constant condition
    fn checkConstant(&self) -> Result<Option<ConstantPredicate>>;
    fn isPrimaryKeyCol(&self, table_index: usize) -> bool;
    fn getIndex(&mut self,
                table_index: usize,
                referenced_tables: &[BTreeTableRef],
                available_indexes: &[Rc<Index>]) -> Result<Option<usize>>;

    fn is_always_true(&self) -> Result<bool> {
        Ok(self.checkConstant()?.map_or(false, |c| c == ConstantPredicate::AlwaysTrue))
    }

    fn is_always_false(&self) -> Result<bool> {
        Ok(self.checkConstant()?.map_or(false, |c| c == ConstantPredicate::AlwaysFalse))
    }
}

impl Optimizable for ast::Expr {
    fn checkConstant(&self) -> Result<Option<ConstantPredicate>> {
        match self {
            ast::Expr::Id(id) => {
                // true and false are special constants that are effectively aliases for 1 and 0
                if id.0.eq_ignore_ascii_case("true") {
                    return Ok(Some(ConstantPredicate::AlwaysTrue));
                }

                if id.0.eq_ignore_ascii_case("false") {
                    return Ok(Some(ConstantPredicate::AlwaysFalse));
                }

                Ok(None)
            }
            ast::Expr::Literal(lit) => match lit {
                ast::Literal::Null => Ok(Some(ConstantPredicate::AlwaysFalse)),
                ast::Literal::Numeric(b) => {
                    if let Ok(int_value) = b.parse::<i64>() {
                        return Ok(Some(if int_value == 0 {
                            ConstantPredicate::AlwaysFalse
                        } else {
                            ConstantPredicate::AlwaysTrue
                        }));
                    }
                    if let Ok(float_value) = b.parse::<f64>() {
                        return Ok(Some(if float_value == 0.0 {
                            ConstantPredicate::AlwaysFalse
                        } else {
                            ConstantPredicate::AlwaysTrue
                        }));
                    }

                    Ok(None)
                }
                ast::Literal::String(s) => {
                    let without_quotes = s.trim_matches('\'');
                    if let Ok(int_value) = without_quotes.parse::<i64>() {
                        return Ok(Some(if int_value == 0 {
                            ConstantPredicate::AlwaysFalse
                        } else {
                            ConstantPredicate::AlwaysTrue
                        }));
                    }

                    if let Ok(float_value) = without_quotes.parse::<f64>() {
                        return Ok(Some(if float_value == 0.0 {
                            ConstantPredicate::AlwaysFalse
                        } else {
                            ConstantPredicate::AlwaysTrue
                        }));
                    }

                    Ok(Some(ConstantPredicate::AlwaysFalse))
                }
                _ => Ok(None),
            },
            ast::Expr::Unary(op, expr) => {
                if *op == ast::UnaryOperator::Not {
                    let trivial = expr.checkConstant()?;
                    return Ok(trivial.map(|t| match t {
                        ConstantPredicate::AlwaysTrue => ConstantPredicate::AlwaysFalse,
                        ConstantPredicate::AlwaysFalse => ConstantPredicate::AlwaysTrue,
                    }));
                }

                if *op == ast::UnaryOperator::Negative {
                    let trivial = expr.checkConstant()?;
                    return Ok(trivial);
                }

                Ok(None)
            }
            ast::Expr::InList { lhs: _, not, rhs } => {
                if rhs.is_none() {
                    return Ok(Some(if *not {
                        ConstantPredicate::AlwaysTrue
                    } else {
                        ConstantPredicate::AlwaysFalse
                    }));
                }
                let rhs = rhs.as_ref().unwrap();
                if rhs.is_empty() {
                    return Ok(Some(if *not {
                        ConstantPredicate::AlwaysTrue
                    } else {
                        ConstantPredicate::AlwaysFalse
                    }));
                }

                Ok(None)
            }
            ast::Expr::Binary(lhs, op, rhs) => {
                let lhs_trivial = lhs.checkConstant()?;
                let rhs_trivial = rhs.checkConstant()?;
                match op {
                    ast::Operator::And => {
                        if lhs_trivial == Some(ConstantPredicate::AlwaysFalse) || rhs_trivial == Some(ConstantPredicate::AlwaysFalse) {
                            return Ok(Some(ConstantPredicate::AlwaysFalse));
                        }

                        if lhs_trivial == Some(ConstantPredicate::AlwaysTrue) && rhs_trivial == Some(ConstantPredicate::AlwaysTrue) {
                            return Ok(Some(ConstantPredicate::AlwaysTrue));
                        }

                        Ok(None)
                    }
                    ast::Operator::Or => {
                        if lhs_trivial == Some(ConstantPredicate::AlwaysTrue) || rhs_trivial == Some(ConstantPredicate::AlwaysTrue) {
                            return Ok(Some(ConstantPredicate::AlwaysTrue));
                        }
                        if lhs_trivial == Some(ConstantPredicate::AlwaysFalse) && rhs_trivial == Some(ConstantPredicate::AlwaysFalse) {
                            return Ok(Some(ConstantPredicate::AlwaysFalse));
                        }

                        Ok(None)
                    }
                    _ => Ok(None),
                }
            }
            _ => Ok(None),
        }
    }

    fn isPrimaryKeyCol(&self, table_index: usize) -> bool {
        match self {
            ast::Expr::Column { table, is_rowid_alias, .. } => *is_rowid_alias && *table == table_index,
            _ => false,
        }
    }

    // try to 得到对应index的
    fn getIndex(&mut self,
                tblIndex: usize, // 对应的tbl的index
                tblRefs: &[BTreeTableRef],
                indexesInSchema: &[Rc<Index>]) -> Result<Option<usize>> {
        match self {
            ast::Expr::Column { table, column, .. } => {
                // column不是tblIndex的对应的表的
                if *table != tblIndex {
                    return Ok(None);
                }

                for (idx, index) in indexesInSchema.iter().enumerate() {
                    if index.table_name == tblRefs[*table].table.name {
                        let column = tblRefs[*table].table.columns.get(*column).unwrap();
                        if index.columns.first().unwrap().name == column.name {
                            return Ok(Some(idx));
                        }
                    }
                }

                Ok(None)
            }
            ast::Expr::Binary(lhs, op, rhs) => {
                let lhs_index = lhs.getIndex(tblIndex, tblRefs, indexesInSchema)?;
                if lhs_index.is_some() {
                    return Ok(lhs_index);
                }

                let rhs_index = rhs.getIndex(tblIndex, tblRefs, indexesInSchema)?;
                if rhs_index.is_some() {
                    // 1 = id 需要调换left和right
                    let lhs_new = rhs.take_ownership();
                    let rhs_new = lhs.take_ownership();
                    *self = ast::Expr::Binary(Box::new(lhs_new), *op, Box::new(rhs_new));
                    return Ok(rhs_index);
                }

                Ok(None)
            }
            _ => Ok(None),
        }
    }
}

pub enum Either<T, U> {
    Left(T),
    Right(U),
}

trait TakeOwnership {
    fn take_ownership(&mut self) -> Self;
}

impl TakeOwnership for ast::Expr {
    fn take_ownership(&mut self) -> Self {
        std::mem::replace(self, ast::Expr::Literal(ast::Literal::Null))
    }
}

impl TakeOwnership for SrcOperator {
    fn take_ownership(&mut self) -> Self {
        std::mem::replace(self, SrcOperator::Nothing)
    }
}
