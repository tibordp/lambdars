mod expr {
    use std::collections::{HashMap, HashSet};
    use std::fmt;

    #[derive(PartialEq, Eq, Hash, Clone)]
    pub struct BoundVariable {
        pub value: String,
        pub index: u32,
    }

    impl fmt::Display for BoundVariable {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            fmt.write_str(&self.value)?;
            if self.index != 0 {
                write!(fmt, "${}", self.index)?
            }
            Ok(())
        }
    }

    pub enum Expr {
        Variable(BoundVariable),
        Apply(Box<Expr>, Box<Expr>),
        Lambda(BoundVariable, Box<Expr>),
    }

    impl Clone for Expr {
        fn clone(&self) -> Expr {
            match self {
                Expr::Variable(var) => Expr::Variable(var.clone()),
                Expr::Apply(lhs, rhs) => Expr::Apply(Box::new(lhs.as_ref().clone()), Box::new(rhs.as_ref().clone())),
                Expr::Lambda(var, body) => Expr::Lambda(var.clone(), Box::new(body.as_ref().clone())),
            }
        }
    }

    impl Expr {
        fn bound_variables_impl(&self, variables: &mut HashSet<BoundVariable>) {
            match self {
                Expr::Variable(_) => (),
                Expr::Apply(lhs, rhs) => {
                    lhs.as_ref().bound_variables_impl(variables);
                    rhs.as_ref().bound_variables_impl(variables);
                }
                Expr::Lambda(var, body) => {
                    variables.insert(var.clone());
                    body.as_ref().bound_variables_impl(variables);
                }
            }
        }

        pub fn bound_variables(&self) -> HashSet<BoundVariable> {
            let mut result = HashSet::new();
            self.bound_variables_impl(&mut result);
            result
        }

        pub fn alpha_reduce(&self, replacements: &HashMap<BoundVariable, BoundVariable>) -> Expr {
            match self {
                Expr::Variable(var) => Expr::Variable(match replacements.get(var) {
                    None => var.clone(),
                    Some(rep) => rep.clone(),
                }),
                Expr::Apply(lhs, rhs) => Expr::Apply(
                    Box::new(lhs.as_ref().alpha_reduce(replacements)),
                    Box::new(rhs.as_ref().alpha_reduce(replacements)),
                ),
                Expr::Lambda(var, body) => Expr::Lambda(
                    match replacements.get(var) {
                        None => var.clone(),
                        Some(rep) => rep.clone(),
                    },
                    Box::new(body.as_ref().alpha_reduce(replacements)),
                ),
            }
        }

        pub fn beta_reduce(&self, variable: &BoundVariable, replacement: &Expr) -> Expr {
            match self {
                Expr::Variable(var) => {
                    if var == variable {
                        replacement.clone()
                    } else {
                        Expr::Variable(var.clone())
                    }
                }
                Expr::Apply(lhs, rhs) => Expr::Apply(
                    Box::new(lhs.as_ref().beta_reduce(variable, replacement)),
                    Box::new(rhs.as_ref().beta_reduce(variable, replacement)),
                ),
                Expr::Lambda(var, body) => Expr::Lambda(var.clone(), Box::new(body.as_ref().beta_reduce(variable, replacement))),
            }
        }

        fn macro_replace_impl(&self, bound_variables: &mut HashSet<BoundVariable>, replacements: &HashMap<BoundVariable, Expr>) -> Expr {
            match self {
                Expr::Variable(var) => {
                    if bound_variables.contains(&var) {
                        Expr::Variable(var.clone())
                    } else {
                        match replacements.get(var) {
                            Some(replacement) => replacement.clone(),
                            _ => Expr::Variable(var.clone()),
                        }
                    }
                }
                Expr::Apply(lhs, rhs) => Expr::Apply(
                    Box::new(lhs.as_ref().macro_replace_impl(bound_variables, replacements)),
                    Box::new(rhs.as_ref().macro_replace_impl(bound_variables, replacements)),
                ),
                Expr::Lambda(var, body) => {
                    bound_variables.insert(var.clone());
                    let result = Expr::Lambda(
                        var.clone(),
                        Box::new(body.as_ref().macro_replace_impl(bound_variables, replacements)),
                    );
                    bound_variables.remove(&var);
                    result
                }
            }
        }

        pub fn macro_replace(&self, replacements: &HashMap<BoundVariable, Expr>) -> Expr {
            let mut bound_variables = HashSet::new();
            self.macro_replace_impl(&mut bound_variables, replacements)
        }

        fn fmt_impl(&self, fmt: &mut fmt::Formatter, lambda_parent: bool, is_rhs: bool) -> fmt::Result {
            match self {
                Expr::Variable(var) => write!(fmt, "{}", var),
                Expr::Apply(lhs, rhs) => {
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
                Expr::Lambda(var, body) => {
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

    impl fmt::Display for Expr {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            self.fmt_impl(fmt, true, false)
        }
    }
}

mod parser {
    use expr::*;
    use std::iter;

    pub enum Node {
        Define(BoundVariable, Expr),
        Reduce(Expr),
    }

    #[derive(Debug, Clone)]
    pub enum Token {
        OpenParen,
        CloseParen,
        Lambda,
        Dot,
        Identifier(String),
        Command(String),
    }

    pub struct Tokenizer<T>
    where
        T: Iterator<Item = char>,
    {
        iter: iter::Peekable<T>,
    }

    impl<T: Iterator<Item = char>> Tokenizer<T> {
        pub fn new(it: T) -> Self {
            Self { iter: it.peekable() }
        }
    }

    impl<T: Iterator<Item = char>> Iterator for Tokenizer<T> {
        type Item = Token;
        fn next(&mut self) -> Option<Token> {
            let result = match self.iter.peek().cloned() {
                Some('λ') | Some('\\') => {
                    self.iter.next();
                    Some(Token::Lambda)
                }

                Some('(') => {
                    self.iter.next();
                    Some(Token::OpenParen)
                }
                Some(')') => {
                    self.iter.next();
                    Some(Token::CloseParen)
                }
                Some('.') => {
                    self.iter.next();
                    Some(Token::Dot)
                }
                Some('#') => {
                    let mut iden = String::default();
                    self.iter.next();
                    loop {
                        match self.iter.peek().cloned() {
                            Some(ch) => match ch {
                                'A'...'Z' | 'a'...'z' | '_' | '0'...'9' => iden.push(self.iter.next().unwrap()),
                                _ => break,
                            },
                            None => break,
                        }
                    }
                    Some(Token::Command(iden))
                }
                Some('A'...'Z') | Some('a'...'z') | Some('_') | Some('0'...'9') => {
                    let mut iden = String::default();
                    loop {
                        match self.iter.peek().cloned() {
                            Some(ch) => match ch {
                                'A'...'Z' | 'a'...'z' | '_' | '0'...'9' => iden.push(self.iter.next().unwrap()),
                                _ => break,
                            },
                            None => break,
                        }
                    }
                    Some(Token::Identifier(iden))
                }
                Some(_) => {
                    self.iter.next();
                    self.next()
                }
                None => None,
            };
            result
        }
    }

    macro_rules! assert_token {
        ($v:expr, $p:pat) => {
            match $v {
                Some($p) => Ok(()),
                Some(tok) => Err(ParseError::UnexpectedToken(tok)),
                None => Err(ParseError::Unterminated),
            }
        };
    }

    #[derive(Debug)]
    pub enum ParseError {
        UnexpectedToken(Token),
        UnknownCommand(String),
        Unterminated,
    }

    pub fn get_variable(tok: Option<Token>) -> Result<BoundVariable, ParseError> {
        match tok {
            Some(Token::Identifier(id)) => Ok(BoundVariable {
                value: id.to_owned(),
                index: 0,
            }),
            Some(tok) => Err(ParseError::UnexpectedToken(tok)),
            _ => Err(ParseError::Unterminated),
        }
    }

    pub fn parse_lambda<T: Iterator<Item = Token>>(it: &mut iter::Peekable<T>) -> Result<Expr, ParseError> {
        assert_token!(it.next(), Token::Lambda)?;
        let variable = get_variable(it.next())?;
        assert_token!(it.next(), Token::Dot)?;
        let expression = parse_expr(it, false)?;
        Ok(Expr::Lambda(variable, Box::new(expression)))
    }

    pub fn parse_paren<T: Iterator<Item = Token>>(it: &mut iter::Peekable<T>) -> Result<Expr, ParseError> {
        assert_token!(it.next(), Token::OpenParen)?;
        parse_expr(it, true)
    }

    pub fn parse_variable_expr<T: Iterator<Item = Token>>(it: &mut iter::Peekable<T>) -> Result<Expr, ParseError> {
        let variable = get_variable(it.next())?;
        Ok(Expr::Variable(variable))
    }

    pub fn parse_expr<T: Iterator<Item = Token>>(it: &mut iter::Peekable<T>, parentheses: bool) -> Result<Expr, ParseError> {
        let mut result: Option<Expr> = None;

        loop {
            let subexpr: Result<Expr, ParseError> = match it.peek().cloned() {
                Some(Token::OpenParen) => parse_paren(it),
                Some(Token::CloseParen) => break,
                Some(Token::Lambda) => parse_lambda(it),
                Some(Token::Identifier(_)) => parse_variable_expr(it),
                _ => break,
            };

            result = match result {
                Some(expr) => Some(Expr::Apply(Box::new(expr), Box::new(subexpr?))),
                _ => Some(subexpr?),
            }
        }

        if parentheses {
            assert_token!(it.next(), Token::CloseParen)?;
        }

        if let Some(e) = result {
            Ok(e)
        } else {
            Err(ParseError::Unterminated)
        }
    }

    pub fn parse_define<T: Iterator<Item = Token>>(it: &mut iter::Peekable<T>) -> Result<Node, ParseError> {
        it.next();
        let variable = get_variable(it.next())?;
        let expression = parse_expr(it, false)?;
        Ok(Node::Define(variable, expression))
    }

    pub fn parse<T: Iterator<Item = Token>>(it: &mut iter::Peekable<T>) -> Result<Node, ParseError> {
        match it.peek().cloned() {
            Some(Token::Command(s)) => match s.as_ref() {
                "define" => parse_define(it),
                s => Err(ParseError::UnknownCommand(s.to_owned())),
            },
            Some(Token::OpenParen) | Some(Token::CloseParen) | Some(Token::Lambda) | Some(Token::Identifier(_)) => {
                parse_expr(it, false).map(Node::Reduce)
            }
            Some(tok) => Err(ParseError::UnexpectedToken(tok)),
            None => Err(ParseError::Unterminated),
        }
    }
}

mod reducer {
    use expr::*;
    use std::collections::HashMap;

    pub trait VariablePool {
        fn next_named(&mut self, &str) -> BoundVariable;
        fn next_anon(&mut self) -> BoundVariable;
    }

    pub struct DefaultVariablePool {
        index: u32,
    }

    impl DefaultVariablePool {
        pub fn new() -> Self {
            Self { index: 1 }
        }
    }

    impl VariablePool for DefaultVariablePool {
        fn next_named(&mut self, s: &str) -> BoundVariable {
            let result = BoundVariable {
                value: s.to_owned(),
                index: self.index,
            };
            self.index += 1;
            result
        }
        fn next_anon(&mut self) -> BoundVariable {
            let result = BoundVariable {
                value: "$tmp".to_owned(),
                index: self.index,
            };
            self.index += 1;
            result
        }
    }

    pub struct Reducer<'a> {
        pool: &'a mut VariablePool,
    }

    impl<'a> Reducer<'a> {
        pub fn reduce(&mut self, n: &Expr) -> (Expr, u32, u32) {
            let mut alpha_reductions = 0;
            let mut beta_reductions = 0;

            let expr = match n {
                Expr::Variable(var) => Expr::Variable(var.clone()),
                Expr::Apply(lhs, rhs) => match lhs.as_ref() {
                    Expr::Lambda(lhs_var, lhs_body) => {
                        let left_vars = lhs.as_ref().bound_variables();
                        let right_vars = rhs.as_ref().bound_variables();

                        let mut replacements: HashMap<BoundVariable, BoundVariable> = left_vars
                            .intersection(&right_vars)
                            .map(|color| (color.clone(), self.pool.next_named(&color.value)))
                            .collect();

                        beta_reductions += 1;
                        if replacements.is_empty() {
                            lhs_body.beta_reduce(lhs_var, rhs)
                        } else {
                            alpha_reductions += 1;
                            lhs_body.beta_reduce(lhs_var, &rhs.alpha_reduce(&replacements))
                        }
                    }
                    _ => {
                        let (lhs, left_alpha, left_beta) = self.reduce(lhs.as_ref());
                        let (rhs, right_alpha, right_beta) = self.reduce(rhs.as_ref());

                        alpha_reductions += left_alpha + right_alpha;
                        beta_reductions += left_beta + right_beta;

                        Expr::Apply(Box::new(lhs), Box::new(rhs))
                    }
                },
                Expr::Lambda(var, body) => {
                    let (body, alpha, beta) = self.reduce(body.as_ref());
                    alpha_reductions += alpha;
                    beta_reductions += beta;
                    Expr::Lambda(var.clone(), Box::new(body))
                }
            };

            (expr, alpha_reductions, beta_reductions)
        }
    }

    impl<'a> Reducer<'a> {
        pub fn new(pool: &'a mut VariablePool) -> Self {
            Self { pool }
        }
    }
}

extern crate colored;
extern crate rustyline;

use colored::Colorize;
use expr::*;
use parser::*;
use reducer::*;
use std::collections::HashMap;

struct Interpreter {
    macros: HashMap<BoundVariable, Expr>,
}

impl Interpreter {
    const MAX_REDUCTIONS: u32 = 100;

    fn new() -> Self {
        Self { macros: HashMap::new() }
    }

    fn reduce_full(expr: Expr, limit: u32) -> Result<Expr, Expr> {
        let mut pool = DefaultVariablePool::new();
        let mut reducer = Reducer::new(&mut pool);
        let mut result = expr;

        let mut total_alpha = 0;
        let mut total_beta = 0;

        for i in 1..limit {
            let (reduced, alpha, beta) = reducer.reduce(&result);
            if alpha == 0 && beta == 0 {
                return Ok(reduced);
            }

            total_alpha += alpha;
            total_beta += beta;

            eprintln!(
                "{}",
                format!(
                    "iteration: {}\tα: {}\tβ: {}\ttotal α: {}\ttotal β: {}",
                    i, alpha, beta, total_alpha, total_beta
                ).yellow()
            );
            result = reduced;
        }
        Err(result)
    }

    fn eval(&mut self, what: &Node) {
        match what {
            Node::Reduce(expr) => match Interpreter::reduce_full(expr.macro_replace(&self.macros), Self::MAX_REDUCTIONS) {
                Ok(reduced) => println!("{}", reduced),
                Err(reduced) => {
                    eprintln!("{}", format!("Could not reduce after {} reductions", Self::MAX_REDUCTIONS).yellow());
                    println!("{}", reduced)
                }
            },
            Node::Define(var, expr) => {
                self.macros.insert(var.to_owned(), expr.to_owned());
            }
        }
    }
}

fn main() {
    let mut rl = rustyline::Editor::<()>::new();
    let mut interpreter = Interpreter::new();

    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_ref());
                let mut tokenizer = Tokenizer::new(line.chars()).peekable();

                match parse(&mut tokenizer) {
                    Ok(stmt) => interpreter.eval(&stmt),
                    Err(err) => eprintln!("{}", format!("Could not parse! {:?}", err).red()),
                };
            }
            Err(_) => break,
        }
    }
}
