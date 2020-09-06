use crate::expression::Expression;
use crate::parser::AstNode;
use crate::utils::Interruptor;
use crate::variable::{PrettyVariablePool, Variable, VariablePool};

use log::{info, trace};
use std::error;
use std::fmt;

use std::collections::{HashMap, HashSet};
use std::vec::Vec;

#[derive(Default)]
pub struct ReduceStats {
    alpha: u32,
    beta: u32,
}

impl ReduceStats {
    pub fn alpha(&self) -> u32 {
        self.alpha
    }

    pub fn beta(&self) -> u32 {
        self.beta
    }

    pub fn is_finished(&self) -> bool {
        self.alpha == 0 && self.beta == 0
    }

    pub fn combine(lhs: &Self, rhs: &Self) -> Self {
        Self {
            alpha: lhs.alpha + rhs.alpha,
            beta: lhs.beta + rhs.beta,
        }
    }

    pub fn new(alpha: u32, beta: u32) -> Self {
        Self { alpha, beta }
    }
}

pub struct Runtime {
    pub macros: HashMap<Variable, Expression>,
    max_reductions: u32,
    max_size: u32,
    max_depth: u32,
    last_output: Option<Expression>,
    pool: Box<dyn VariablePool>,
}

#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    IterationsExceeded(Expression, u32),
    DepthExceeded(Expression, u32),
    SizeExceeded(Expression, u32),
    Terminated(Expression, u32),
    NoLastOutput,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::IterationsExceeded(_, cnt) => write!(f, "Exceeded limit of {} iterations.", cnt),
            Error::DepthExceeded(_, cnt) => {
                write!(f, "Intermediary expression exceeded depth limit ({}).", cnt)
            }
            Error::SizeExceeded(_, cnt) => {
                write!(f, "Intermediary expression exceeded size limit ({})", cnt)
            }
            Error::Terminated(_, cnt) => write!(f, "Terminated after {} iterations.", cnt),
            Error::NoLastOutput => write!(f, "There is no last output to use"),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        None
    }
}

impl Runtime {
    pub fn new(pool: Box<dyn VariablePool>) -> Self {
        Self {
            macros: HashMap::new(),
            max_reductions: 100,
            max_depth: 1000,
            max_size: 1000,
            last_output: None,
            pool,
        }
    }

    fn reindex(&self, expression: &Expression) -> Expression {
        let mut pool = PrettyVariablePool::new();
        let mut taken_names = Vec::new();
        let mut replacements = HashMap::new();
        self.reindex_impl(
            expression,
            0,
            &mut pool,
            &mut taken_names,
            &mut replacements,
        )
    }

    fn reindex_impl(
        &self,
        expression: &Expression,
        depth: usize,
        pool: &mut dyn VariablePool,
        taken_names: &mut Vec<Variable>,
        replacements: &mut HashMap<Variable, Variable>,
    ) -> Expression {
        match expression {
            Expression::Variable(var) => Expression::Variable(match replacements.get(var) {
                None => var.clone(),
                Some(rep) => rep.clone(),
            }),
            Expression::Apply(lhs, rhs) => Expression::Apply(
                box self.reindex_impl(lhs.as_ref(), depth, pool, taken_names, replacements),
                box self.reindex_impl(rhs.as_ref(), depth, pool, taken_names, replacements),
            ),
            Expression::Lambda(var, body) => {
                let replacement = if depth == taken_names.len() {
                    let var = pool.next_anon();
                    taken_names.push(var.clone());
                    var
                } else {
                    taken_names[depth].clone()
                };

                replacements.insert(var.clone(), replacement.clone());
                let result = Expression::Lambda(
                    replacement,
                    box self.reindex_impl(
                        body.as_ref(),
                        depth + 1,
                        pool,
                        taken_names,
                        replacements,
                    ),
                );
                replacements.remove(&var);
                result
            }
        }
    }

    fn reduce(&mut self, expr: &Expression) -> (Expression, ReduceStats) {
        match expr {
            Expression::Variable(_) => (expr.clone(), ReduceStats::default()),
            Expression::Apply(lhs, rhs) => match lhs.as_ref() {
                Expression::Lambda(lhs_var, lhs_body) => {
                    let left_vars = lhs.as_ref().variables();
                    let right_vars = rhs.as_ref().variables();

                    let replacements: HashMap<Variable, Variable> = left_vars
                        .intersection(&right_vars)
                        .map(|color| (color.clone(), self.pool.next_named(color.value())))
                        .collect();

                    if replacements.is_empty() {
                        (
                            lhs_body.beta_reduce(&lhs_var, rhs.as_ref()),
                            ReduceStats::new(0, 1),
                        )
                    } else {
                        (
                            lhs_body.beta_reduce(&lhs_var, &rhs.alpha_reduce(&replacements)),
                            ReduceStats::new(1, 1),
                        )
                    }
                }
                _ => {
                    let (lhs, lhs_stats) = self.reduce(lhs.as_ref());
                    let (rhs, rhs_stats) = self.reduce(rhs.as_ref());
                    (
                        Expression::Apply(box lhs, box rhs),
                        ReduceStats::combine(&lhs_stats, &rhs_stats),
                    )
                }
            },
            Expression::Lambda(var, body) => {
                let (body, stats) = self.reduce(body.as_ref());
                (Expression::Lambda(var.clone(), box body), stats)
            }
        }
    }

    fn reduce_full(&mut self, expression: Expression) -> Result<Expression, Error> {
        let mut result = expression;
        let mut overall_stats = ReduceStats::default();
        let interruptor = Interruptor::register().unwrap();

        for i in 1..self.max_reductions {
            let (reduced, reduce_stats) = self.reduce(&result);
            let expr_stats = reduced.stats();

            if expr_stats.size() > self.max_size {
                return Err(Error::SizeExceeded(result, expr_stats.size()));
            }

            if expr_stats.depth() > self.max_depth {
                return Err(Error::DepthExceeded(result, expr_stats.depth()));
            }

            if interruptor.check() {
                return Err(Error::Terminated(result, i));
            }

            if reduce_stats.is_finished() {
                if i > 1 {
                    // If expression was already reduced, we print nothing
                    info!(
                        "Reduced in {} iterations, total α: {}, total β: {}",
                        i,
                        overall_stats.alpha(),
                        overall_stats.beta()
                    );
                }
                return Ok(reduced);
            }

            overall_stats = ReduceStats::combine(&overall_stats, &reduce_stats);

            trace!(
                "iteration: {}\tα: {}\tβ: {}\ttotal α: {}\ttotal β: {}",
                i,
                reduce_stats.alpha(),
                reduce_stats.beta(),
                overall_stats.alpha(),
                overall_stats.beta()
            );
            result = reduced;
        }

        Err(Error::IterationsExceeded(result, self.max_reductions))
    }

    fn macro_replace_impl(
        &mut self,
        expression: &Expression,
        variables: &mut HashSet<Variable>,
    ) -> Result<Expression, Error> {
        match expression {
            Expression::Variable(var) => {
                if variables.contains(&var) {
                    Ok(Expression::Variable(var.clone()))
                } else {
                    let replacement = if var.value() == "@" {
                        Some(
                            self.last_output
                                .as_ref()
                                .ok_or(Error::NoLastOutput)?
                                .clone(),
                        )
                    } else {
                        self.macros.get(&var).cloned()
                    };

                    match replacement {
                        Some(replacement) => {
                            // Do an alpha reduction of the macro if there are already bound variables with the same name in the current context
                            let replacements: HashMap<Variable, Variable> = replacement
                                .variables()
                                .intersection(&variables)
                                .map(|color| (color.clone(), self.pool.next_named(color.value())))
                                .collect();

                            if replacements.is_empty() {
                                Ok(replacement)
                            } else {
                                Ok(replacement.alpha_reduce(&replacements))
                            }
                        }
                        _ => Ok(Expression::Variable(var.clone())),
                    }
                }
            }
            Expression::Apply(lhs, rhs) => Ok(Expression::Apply(
                box self.macro_replace_impl(lhs.as_ref(), variables)?,
                box self.macro_replace_impl(rhs.as_ref(), variables)?,
            )),
            Expression::Lambda(var, body) => {
                variables.insert(var.clone());
                let result = Expression::Lambda(
                    var.clone(),
                    box self.macro_replace_impl(body.as_ref(), variables)?,
                );
                variables.remove(&var);
                Ok(result)
            }
        }
    }

    fn macro_replace(&mut self, expression: &Expression) -> Result<Expression, Error> {
        let mut variables = HashSet::new();
        self.macro_replace_impl(expression, &mut variables)
    }

    pub fn eval(&mut self, what: &AstNode) -> Result<Option<Expression>, Error> {
        match what {
            AstNode::Reduce(expression) => {
                let replaced = self.macro_replace(expression)?;
                let reduced = self.reduce_full(replaced)?;
                let reindexed = self.reindex(&reduced);
                self.last_output = Some(reindexed);

                Ok(self.last_output.clone())
            }
            AstNode::Define(var, expression) => {
                let reduced_macro = self.macro_replace(&expression)?;
                self.macros.insert(var.to_owned(), reduced_macro);
                Ok(None)
            }
            AstNode::SetMaxReductions(limit) => {
                self.max_reductions = *limit;
                Ok(None)
            }
            AstNode::SetMaxSize(limit) => {
                self.max_size = *limit;
                Ok(None)
            }
            AstNode::SetMaxDepth(limit) => {
                self.max_depth = *limit;
                Ok(None)
            }
            AstNode::Dump => {
                for (name, expr) in &self.macros {
                    println!("#define {} {}", name, expr);
                }
                Ok(None)
            }
            AstNode::Nothing => Ok(None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::variable::DefaultVariablePool;
    use assert_matches::assert_matches;

    #[test]
    fn reduce_expression() {
        let mut runtime = Runtime::new(box DefaultVariablePool::default());

        let identity = box Expression::Lambda(
            Variable::new("x".to_owned(), 0),
            box Expression::Variable(Variable::new("x".to_owned(), 0)),
        );
        let apply = Expression::Apply(
            identity,
            box Expression::Variable(Variable::new("y".to_owned(), 0)),
        );

        assert_matches!(
            runtime.eval(&AstNode::Reduce(apply)),
            Ok(Some(Expression::Variable(_)))
        );
    }

    #[test]
    fn last_output() {
        let mut runtime = Runtime::new(box DefaultVariablePool::default());

        let identity = Expression::Lambda(
            Variable::new("x".to_owned(), 0),
            box Expression::Variable(Variable::new("x".to_owned(), 0)),
        );
        runtime.eval(&AstNode::Reduce(identity)).unwrap();

        let last_output = Expression::Variable(Variable::new("@".to_owned(), 0));

        assert_matches!(
            runtime.eval(&AstNode::Reduce(last_output)),
            Ok(Some(Expression::Lambda(_, box Expression::Variable(_))))
        );
    }

    #[test]
    fn iterations_exceeded() {
        let mut runtime = Runtime::new(box DefaultVariablePool::default());

        let omega = box Expression::Lambda(
            Variable::new("x".to_owned(), 0),
            box Expression::Apply(
                box Expression::Variable(Variable::new("x".to_owned(), 0)),
                box Expression::Variable(Variable::new("x".to_owned(), 0)),
            ),
        );
        let omega_2 = Expression::Apply(omega.clone(), omega.clone());

        assert_matches!(
            runtime.eval(&AstNode::Reduce(omega_2)),
            Err(Error::IterationsExceeded(_, 100))
        );
    }

    #[test]
    fn depth_exceeded() {
        let mut runtime = Runtime::new(box DefaultVariablePool::default());
        runtime.eval(&AstNode::SetMaxReductions(10000)).unwrap();

        let fix_part = box Expression::Lambda(
            Variable::new("x".to_owned(), 0),
            box Expression::Apply(
                box Expression::Variable(Variable::new("f".to_owned(), 0)),
                box Expression::Apply(
                    box Expression::Variable(Variable::new("x".to_owned(), 0)),
                    box Expression::Variable(Variable::new("x".to_owned(), 0)),
                ),
            ),
        );

        let fix = Expression::Lambda(
            Variable::new("f".to_owned(), 0),
            box Expression::Apply(fix_part.clone(), fix_part.clone()),
        );

        assert_matches!(
            runtime.eval(&AstNode::Reduce(fix)),
            Err(Error::SizeExceeded(_, 1002))
        );
    }
}
