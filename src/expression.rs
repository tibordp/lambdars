use std::collections::{HashMap, HashSet};
use std::fmt;
use variable::Variable;

#[derive(Debug)]
pub enum Expression {
    Variable(Variable),
    Apply(Box<Expression>, Box<Expression>),
    Lambda(Variable, Box<Expression>),
}

impl Clone for Expression {
    fn clone(&self) -> Expression {
        match self {
            Expression::Variable(var) => Expression::Variable(var.clone()),
            Expression::Apply(lhs, rhs) => Expression::Apply(Box::new(lhs.as_ref().clone()), Box::new(rhs.as_ref().clone())),
            Expression::Lambda(var, body) => Expression::Lambda(var.clone(), Box::new(body.as_ref().clone())),
        }
    }
}

impl fmt::Display for Expression {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.fmt_impl(fmt, true, false)
    }
}

impl Expression {
    fn variables_impl(&self, variables: &mut HashSet<Variable>) {
        match self {
            Expression::Variable(_) => (),
            Expression::Apply(lhs, rhs) => {
                lhs.as_ref().variables_impl(variables);
                rhs.as_ref().variables_impl(variables);
            }
            Expression::Lambda(var, body) => {
                variables.insert(var.clone());
                body.as_ref().variables_impl(variables);
            }
        }
    }

    pub fn variables(&self) -> HashSet<Variable> {
        let mut result = HashSet::new();
        self.variables_impl(&mut result);
        result
    }

    pub fn alpha_reduce(&self, replacements: &HashMap<Variable, Variable>) -> Expression {
        match self {
            Expression::Variable(var) => Expression::Variable(match replacements.get(var) {
                None => var.clone(),
                Some(rep) => rep.clone(),
            }),
            Expression::Apply(lhs, rhs) => Expression::Apply(
                Box::new(lhs.as_ref().alpha_reduce(replacements)),
                Box::new(rhs.as_ref().alpha_reduce(replacements)),
            ),
            Expression::Lambda(var, body) => Expression::Lambda(
                match replacements.get(var) {
                    None => var.clone(),
                    Some(rep) => rep.clone(),
                },
                Box::new(body.as_ref().alpha_reduce(replacements)),
            ),
        }
    }

    pub fn stats(&self) -> ExpressionStats {
        let child_stats = match self {
            Expression::Variable(_) => ExpressionStats::default(),
            Expression::Apply(lhs, rhs) => ExpressionStats::combine(&lhs.as_ref().stats(), &rhs.as_ref().stats()),
            Expression::Lambda(_, body) => body.as_ref().stats(),
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
                Box::new(lhs.as_ref().beta_reduce(variable, replacement)),
                Box::new(rhs.as_ref().beta_reduce(variable, replacement)),
            ),
            Expression::Lambda(var, body) => Expression::Lambda(var.clone(), Box::new(body.as_ref().beta_reduce(variable, replacement))),
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