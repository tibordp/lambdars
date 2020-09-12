use crate::variable::Variable;
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expression {
    Variable(Variable),
    Apply(Box<Expression>, Box<Expression>),
    Lambda(Variable, Box<Expression>),
}

impl fmt::Display for Expression {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        if fmt.alternate() {
            self.fmt_impl_javascript(fmt, true)
        } else {
            self.fmt_impl(fmt, true, false)
        }
    }
}

impl Expression {
    fn check_variables(
        lhs: &Variable,
        rhs: &Variable,
        is_lambda: bool,
        replacements: &mut HashMap<Variable, Variable>,
    ) -> bool {
        use std::collections::hash_map::Entry;
        match replacements.entry(lhs.clone()) {
            Entry::Occupied(what) => what.get() == rhs,
            Entry::Vacant(what) => {
                is_lambda && {
                    what.insert(rhs.clone());
                    true
                }
            }
        }
    }

    fn alpha_equivalent_impl(
        &self,
        other: &Expression,
        replacements: &mut HashMap<Variable, Variable>,
    ) -> bool {
        match (self, other) {
            (Expression::Lambda(l_var, l_body), Expression::Lambda(r_var, r_body)) => {
                Self::check_variables(l_var, r_var, true, replacements)
                    && l_body.alpha_equivalent_impl(r_body, replacements)
            }
            (Expression::Variable(lhs), Expression::Variable(rhs)) => {
                Self::check_variables(lhs, rhs, false, replacements)
            }
            (Expression::Apply(l_lhs, l_rhs), Expression::Apply(r_lhs, r_rhs)) => {
                l_lhs.alpha_equivalent_impl(r_lhs, replacements)
                    && l_rhs.alpha_equivalent_impl(r_rhs, replacements)
            }
            _ => false,
        }
    }

    pub fn alpha_equivalent(&self, other: &Expression) -> bool {
        self.alpha_equivalent_impl(other, &mut HashMap::new())
    }

    fn bound_variables_impl(&self, variables: &mut HashSet<Variable>) {
        match self {
            Expression::Variable(_) => (),
            Expression::Apply(lhs, rhs) => {
                lhs.bound_variables_impl(variables);
                rhs.bound_variables_impl(variables);
            }
            Expression::Lambda(var, body) => {
                variables.insert(var.clone());
                body.bound_variables_impl(variables);
            }
        }
    }

    pub fn bound_variables(&self) -> HashSet<Variable> {
        let mut result = HashSet::new();
        self.bound_variables_impl(&mut result);
        result
    }

    fn free_variables_impl(
        &self,
        bound_variables: &mut HashSet<Variable>,
        free_variables: &mut HashSet<Variable>,
    ) {
        match self {
            Expression::Variable(var) => {
                if !bound_variables.contains(var) {
                    free_variables.insert(var.clone());
                }
            }
            Expression::Apply(lhs, rhs) => {
                lhs.free_variables_impl(bound_variables, free_variables);
                rhs.free_variables_impl(bound_variables, free_variables);
            }
            Expression::Lambda(var, body) => {
                bound_variables.insert(var.clone());
                body.free_variables_impl(bound_variables, free_variables);
                bound_variables.remove(var);
            }
        }
    }

    pub fn free_variables(&self) -> HashSet<Variable> {
        let mut bound_variables = HashSet::new();
        let mut result = HashSet::new();
        self.free_variables_impl(&mut bound_variables, &mut result);
        result
    }

    pub fn alpha_reduce(&self, replacements: &HashMap<Variable, Variable>) -> Expression {
        match self {
            Expression::Variable(var) => Expression::Variable(match replacements.get(var) {
                None => var.clone(),
                Some(rep) => rep.clone(),
            }),
            Expression::Apply(lhs, rhs) => Expression::Apply(
                box lhs.alpha_reduce(replacements),
                box rhs.alpha_reduce(replacements),
            ),
            Expression::Lambda(var, body) => Expression::Lambda(
                match replacements.get(var) {
                    None => var.clone(),
                    Some(rep) => rep.clone(),
                },
                box body.alpha_reduce(replacements),
            ),
        }
    }

    pub fn stats(&self) -> ExpressionStats {
        let child_stats = match self {
            Expression::Variable(_) => ExpressionStats::default(),
            Expression::Apply(lhs, rhs) => ExpressionStats::combine(&lhs.stats(), &rhs.stats()),
            Expression::Lambda(_, body) => body.stats(),
        };

        child_stats.next()
    }

    pub fn beta_reduce(&self, variable: &Variable, replacement: &Expression) -> Expression {
        match self {
            Expression::Variable(var) => {
                if var == variable {
                    replacement.clone()
                } else {
                    Expression::Variable(var.clone())
                }
            }
            Expression::Apply(lhs, rhs) => Expression::Apply(
                box lhs.beta_reduce(variable, replacement),
                box rhs.beta_reduce(variable, replacement),
            ),
            Expression::Lambda(var, body) => {
                Expression::Lambda(var.clone(), box body.beta_reduce(variable, replacement))
            }
        }
    }

    fn fmt_impl_javascript(&self, fmt: &mut fmt::Formatter, lambda_parent: bool) -> fmt::Result {
        match self {
            Expression::Variable(var) => write!(fmt, "{}", var),
            Expression::Apply(lhs, rhs) => {
                lhs.fmt_impl_javascript(fmt, false)?;
                fmt.write_str("(")?;
                rhs.fmt_impl_javascript(fmt, true)?;
                fmt.write_str(")")?;
                Ok(())
            }
            Expression::Lambda(var, body) => {
                if !lambda_parent {
                    fmt.write_str("(")?
                }
                write!(fmt, "{}", var)?;
                fmt.write_str(" => ")?;
                body.fmt_impl_javascript(fmt, true)?;

                if !lambda_parent {
                    fmt.write_str(")")?
                }
                Ok(())
            }
        }
    }

    fn fmt_impl(&self, fmt: &mut fmt::Formatter, lambda_parent: bool, is_rhs: bool) -> fmt::Result {
        match self {
            Expression::Variable(var) => write!(fmt, "{}", var),
            Expression::Apply(lhs, rhs) => {
                if is_rhs {
                    fmt.write_str("(")?;
                }

                lhs.fmt_impl(fmt, false, false)?;
                fmt.write_str(" ")?;
                rhs.fmt_impl(fmt, false, true)?;

                if is_rhs {
                    fmt.write_str(")")?
                }
                Ok(())
            }
            Expression::Lambda(var, body) => {
                if is_rhs || !lambda_parent {
                    fmt.write_str("(")?
                }
                fmt.write_str("λ")?;
                write!(fmt, "{}", var)?;
                fmt.write_str(".")?;
                body.fmt_impl(fmt, true, false)?;

                if is_rhs || !lambda_parent {
                    fmt.write_str(")")?
                }
                Ok(())
            }
        }
    }
}

#[derive(Default)]
pub struct ExpressionStats {
    size: u32,
    depth: u32,
}

impl ExpressionStats {
    pub fn size(&self) -> u32 {
        self.size
    }

    pub fn depth(&self) -> u32 {
        self.depth
    }

    pub fn combine(lhs: &Self, rhs: &Self) -> Self {
        Self {
            size: lhs.size + rhs.size,
            depth: ::std::cmp::max(lhs.depth, rhs.depth),
        }
    }

    pub fn next(&self) -> Self {
        Self {
            size: self.size + 1,
            depth: self.depth + 1,
        }
    }
}
