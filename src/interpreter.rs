use expression::Expression;
use parser::AstNode;
use variable::{PrettyVariablePool, Variable, VariablePool};

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
        return self.alpha == 0 && self.beta == 0;
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

pub struct Interpreter<'a> {
    macros: HashMap<Variable, Expression>,
    max_reductions: u32,
    max_size: u32,
    max_depth: u32,
    pool: &'a mut VariablePool,
}

impl<'a> Interpreter<'a> {
    pub fn new(pool: &'a mut VariablePool) -> Self {
        Self {
            macros: HashMap::new(),
            max_reductions: 100,
            max_depth: 1000,
            max_size: 1000,
            pool,
        }
    }

    fn reindex(&self, expression: &Expression) -> Expression {
        let mut pool = PrettyVariablePool::new();
        let mut taken_names = Vec::new();
        let mut replacements = HashMap::new();
        self.reindex_impl(expression, 0, &mut pool, &mut taken_names, &mut replacements)
    }

    fn reindex_impl(
        &self,
        expression: &Expression,
        depth: usize,
        pool: &mut VariablePool,
        taken_names: &mut Vec<Variable>,
        replacements: &mut HashMap<Variable, Variable>,
    ) -> Expression {
        match expression {
            Expression::Variable(var) => Expression::Variable(match replacements.get(var) {
                None => var.clone(),
                Some(rep) => rep.clone(),
            }),
            Expression::Apply(lhs, rhs) => Expression::Apply(
                Box::new(self.reindex_impl(lhs.as_ref(), depth, pool, taken_names, replacements)),
                Box::new(self.reindex_impl(rhs.as_ref(), depth, pool, taken_names, replacements)),
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
                    replacement.clone(),
                    Box::new(self.reindex_impl(body.as_ref(), depth + 1, pool, taken_names, replacements)),
                );
                replacements.remove(&var);
                result
            }
        }
    }

    fn reduce(&mut self, n: &Expression) -> (Expression, ReduceStats) {
        match n {
            Expression::Variable(var) => (Expression::Variable(var.clone()), ReduceStats::default()),
            Expression::Apply(lhs, rhs) => match lhs.as_ref() {
                Expression::Lambda(lhs_var, lhs_body) => {
                    let left_vars = lhs.as_ref().variables();
                    let right_vars = rhs.as_ref().variables();

                    let mut replacements: HashMap<Variable, Variable> = left_vars
                        .intersection(&right_vars)
                        .map(|color| (color.clone(), self.pool.next_named(color.value())))
                        .collect();

                    if replacements.is_empty() {
                        (lhs_body.beta_reduce(lhs_var, rhs), ReduceStats::new(0, 1))
                    } else {
                        (
                            lhs_body.beta_reduce(lhs_var, &rhs.alpha_reduce(&replacements)),
                            ReduceStats::new(1, 1),
                        )
                    }
                }
                _ => {
                    let (lhs, lhs_stats) = self.reduce(lhs.as_ref());
                    let (rhs, rhs_stats) = self.reduce(rhs.as_ref());

                    (
                        Expression::Apply(Box::new(lhs), Box::new(rhs)),
                        ReduceStats::combine(&lhs_stats, &rhs_stats),
                    )
                }
            },
            Expression::Lambda(var, body) => {
                let (body, stats) = self.reduce(body.as_ref());
                (Expression::Lambda(var.clone(), Box::new(body)), stats)
            }
        }
    }

    fn reduce_full(&mut self, expression: Expression) -> Result<Expression, ()> {
        let mut result = expression;
        let mut overall_stats = ReduceStats::default();

        for i in 1..self.max_reductions {
            let (reduced, reduce_stats) = self.reduce(&result);
            let expr_stats = reduced.stats();

            if expr_stats.size() > self.max_size {
                warn!(
                    "Intermediary expression exceeded the size limit {} (limit={})",
                    expr_stats.size(),
                    self.max_size
                );
                return Err(());
            }

            if expr_stats.depth() > self.max_depth {
                warn!(
                    "Intermediary expression exceeded the depth limit {} (limit={})",
                    expr_stats.depth(),
                    self.max_depth
                );
                return Err(());
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

        warn!("Iteration limit exceeded (limit={})", self.max_reductions);
        Err(())
    }

    fn macro_replace_impl(&mut self, expression: &Expression, variables: &mut HashSet<Variable>) -> Expression {
        match expression {
            Expression::Variable(var) => {
                if variables.contains(&var) {
                    // If the macro is a bound variable, do not replace it
                    Expression::Variable(var.clone())
                } else {
                    match self.macros.get(var).cloned() {
                        Some(replacement) => {
                            // Do an alpha reduction of the macro if there are already bound variables with the same name in the current context
                            let mut replacements: HashMap<Variable, Variable> = replacement
                                .variables()
                                .intersection(&variables)
                                .map(|color| (color.clone(), self.pool.next_named(color.value())))
                                .collect();

                            if replacements.is_empty() {
                                replacement
                            } else {
                                replacement.alpha_reduce(&replacements)
                            }
                        }
                        _ => Expression::Variable(var.clone()),
                    }
                }
            }
            Expression::Apply(lhs, rhs) => Expression::Apply(
                Box::new(self.macro_replace_impl(lhs.as_ref(), variables)),
                Box::new(self.macro_replace_impl(rhs.as_ref(), variables)),
            ),
            Expression::Lambda(var, body) => {
                variables.insert(var.clone());
                let result = Expression::Lambda(var.clone(), Box::new(self.macro_replace_impl(body.as_ref(), variables)));
                variables.remove(&var);
                result
            }
        }
    }

    fn macro_replace(&mut self, expression: &Expression) -> Expression {
        let mut variables = HashSet::new();
        self.macro_replace_impl(expression, &mut variables)
    }

    pub fn eval(&mut self, what: &AstNode) {
        match what {
            AstNode::Reduce(expression) => {
                let replaced = self.macro_replace(expression);
                match self.reduce_full(replaced) {
                    Ok(reduced) => println!("{}", self.reindex(&reduced)),
                    Err(_) => {
                        println!("!error");
                    }
                }
            }
            AstNode::Define(var, expression) => {
                let reduced_macro = self.macro_replace(expression);
                self.macros.insert(var.to_owned(), reduced_macro);
            }
            AstNode::SetMaxReductions(limit) => {
                self.max_reductions = *limit;
            }
            AstNode::SetMaxSize(limit) => {
                self.max_size = *limit;
            }
            AstNode::SetMaxDepth(limit) => {
                self.max_depth = *limit;
            }
            AstNode::Dump => {
                for (name, expr) in &self.macros {
                    println!("#define {} {}", name, expr);
                }
            }            
            AstNode::Nothing => (),
        }
    }
}
