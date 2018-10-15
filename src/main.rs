#[macro_use]
extern crate log;
extern crate clap;
extern crate pretty_env_logger;
extern crate rustyline;

mod variable {
    use std::fmt;

    #[derive(PartialEq, Eq, Hash, Clone, Debug)]
    pub struct Variable {
        value: String,
        index: usize,
    }

    impl Variable {
        pub fn value(&self) -> &str {
            &self.value
        }

        pub fn index(&self) -> usize {
            self.index
        }

        pub fn new(value: String, index: usize) -> Self {
            Variable { value, index }
        }
    }

    impl fmt::Display for Variable {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            fmt.write_str(&self.value)?;
            if self.index != 0 {
                write!(fmt, "${}", self.index)?
            }
            Ok(())
        }
    }

    pub trait VariablePool {
        fn next_named(&mut self, &str) -> Variable;
        fn next_anon(&mut self) -> Variable;
    }

    pub struct DefaultVariablePool {
        index: usize,
    }

    impl DefaultVariablePool {
        pub fn new() -> Self {
            Self { index: 1 }
        }
    }

    impl VariablePool for DefaultVariablePool {
        fn next_named(&mut self, s: &str) -> Variable {
            let result = Variable::new(s.to_owned(), self.index);
            self.index += 1;
            result
        }
        fn next_anon(&mut self) -> Variable {
            let result = Variable::new("$tmp".to_owned(), self.index);
            self.index += 1;
            result
        }
    }

    pub struct PrettyVariablePool {
        index: usize,
    }

    static PRETTY_NAMES: &'static [char] = &[
        'x', 'y', 'z', 'u', 'v', 'w', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't',
    ];

    impl PrettyVariablePool {
        pub fn new() -> Self {
            Self { index: 0 }
        }
    }

    impl VariablePool for PrettyVariablePool {
        fn next_named(&mut self, _: &str) -> Variable {
            unimplemented!()
        }

        fn next_anon(&mut self) -> Variable {
            let result = Variable::new(
                PRETTY_NAMES[self.index % PRETTY_NAMES.len()].to_string(),
                self.index / PRETTY_NAMES.len(),
            );
            self.index += 1;
            result
        }
    }
}

mod expression {
    use std::collections::{HashMap, HashSet};
    use std::fmt;
    use variable::Variable;

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

    impl fmt::Display for Expression {
        fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
            self.fmt_impl(fmt, true, false)
        }
    }
}

mod parser {
    use expression::*;
    use std::collections::HashSet;
    use std::iter;
    use variable::Variable;

    pub enum AstNode {
        Nothing,
        Define(Variable, Expression),
        SetMaxReductions(u32),
        SetMaxSize(u32),
        SetMaxDepth(u32),
        Reduce(Expression),
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

    pub struct Lexer<T>
    where
        T: Iterator<Item = char>,
    {
        iter: iter::Peekable<T>,
    }

    impl<T: Iterator<Item = char>> Lexer<T> {
        pub fn new(it: T) -> Self {
            Self { iter: it.peekable() }
        }
    }

    impl<T: Iterator<Item = char>> Iterator for Lexer<T> {
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
        RedefinedVariable(Variable),
        UnknownCommand(String),
        ExpectedInteger(String),
        Unterminated,
    }

    pub struct Parser<T: Iterator<Item = Token>> {
        it: iter::Peekable<T>,
        variables: HashSet<Variable>,
    }

    impl<T: Iterator<Item = Token>> Parser<T> {
        pub fn new(it: T) -> Self {
            Self {
                it: it.peekable(),
                variables: HashSet::new(),
            }
        }

        fn get_variable(tok: Option<Token>) -> Result<Variable, ParseError> {
            match tok {
                Some(Token::Identifier(id)) => Ok(Variable::new(id.to_owned(), 0)),
                Some(tok) => Err(ParseError::UnexpectedToken(tok)),
                _ => Err(ParseError::Unterminated),
            }
        }

        fn parse_lambda(&mut self) -> Result<Expression, ParseError> {
            assert_token!(self.it.next(), Token::Lambda)?;
            let variable = Self::get_variable(self.it.next())?;
            if self.variables.contains(&variable) {
                return Err(ParseError::RedefinedVariable(variable));
            }
            assert_token!(self.it.next(), Token::Dot)?;
            self.variables.insert(variable.clone());
            let expression = self.parse_expression(false)?;
            self.variables.remove(&variable);
            Ok(Expression::Lambda(variable, Box::new(expression)))
        }

        fn parse_paren(&mut self) -> Result<Expression, ParseError> {
            assert_token!(self.it.next(), Token::OpenParen)?;
            self.parse_expression(true)
        }

        fn parse_variable_expression(&mut self) -> Result<Expression, ParseError> {
            let variable = Self::get_variable(self.it.next())?;
            Ok(Expression::Variable(variable))
        }

        fn parse_expression(&mut self, parentheses: bool) -> Result<Expression, ParseError> {
            let mut result: Option<Expression> = None;

            loop {
                let subexpression: Result<Expression, ParseError> = match self.it.peek().cloned() {
                    Some(Token::OpenParen) => self.parse_paren(),
                    Some(Token::CloseParen) => break,
                    Some(Token::Lambda) => self.parse_lambda(),
                    Some(Token::Identifier(_)) => self.parse_variable_expression(),
                    _ => break,
                };

                result = match result {
                    Some(expression) => Some(Expression::Apply(Box::new(expression), Box::new(subexpression?))),
                    _ => Some(subexpression?),
                }
            }

            if parentheses {
                assert_token!(self.it.next(), Token::CloseParen)?;
            }

            if let Some(e) = result {
                Ok(e)
            } else {
                Err(ParseError::Unterminated)
            }
        }

        fn parse_define(&mut self) -> Result<AstNode, ParseError> {
            self.it.next();
            let variable = Self::get_variable(self.it.next())?;
            let expression = self.parse_expression(false)?;
            Ok(AstNode::Define(variable, expression))
        }

        fn parse_max_reductions(&mut self) -> Result<AstNode, ParseError> {
            self.it.next();
            let variable = Self::get_variable(self.it.next())?;
            let variable_name = variable.value();
            let limit = variable_name
                .parse::<u32>()
                .map_err(|_| ParseError::ExpectedInteger(variable_name.to_owned()))?;
            Ok(AstNode::SetMaxReductions(limit))
        }

        fn parse_max_size(&mut self) -> Result<AstNode, ParseError> {
            self.it.next();
            let variable = Self::get_variable(self.it.next())?;
            let variable_name = variable.value();
            let limit = variable_name
                .parse::<u32>()
                .map_err(|_| ParseError::ExpectedInteger(variable_name.to_owned()))?;
            Ok(AstNode::SetMaxSize(limit))
        }

        fn parse_max_depth(&mut self) -> Result<AstNode, ParseError> {
            self.it.next();
            let variable = Self::get_variable(self.it.next())?;
            let variable_name = variable.value();
            let limit = variable_name
                .parse::<u32>()
                .map_err(|_| ParseError::ExpectedInteger(variable_name.to_owned()))?;
            Ok(AstNode::SetMaxDepth(limit))
        }

        pub fn parse(&mut self) -> Result<AstNode, ParseError> {
            match self.it.peek().cloned() {
                Some(Token::Command(s)) => match s.as_ref() {
                    "define" => self.parse_define(),
                    "max_reductions" => self.parse_max_reductions(),
                    "max_size" => self.parse_max_size(),
                    "max_depth" => self.parse_max_depth(),
                    s => Err(ParseError::UnknownCommand(s.to_owned())),
                },
                Some(Token::OpenParen) | Some(Token::CloseParen) | Some(Token::Lambda) | Some(Token::Identifier(_)) => {
                    self.parse_expression(false).map(AstNode::Reduce)
                }
                Some(tok) => Err(ParseError::UnexpectedToken(tok)),
                None => Ok(AstNode::Nothing),
            }
        }
    }
}

mod interpreter {
    use expression::Expression;
    use parser::AstNode;
    use variable::{Variable, VariablePool, PrettyVariablePool};

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

        pub fn new(alpha : u32, beta : u32) -> Self {
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
                                ReduceStats::new(1, 1)
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
                            i, overall_stats.alpha(), overall_stats.beta()
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
                AstNode::Nothing => (),
            }
        }
    }
}

fn eval_file(interpreter: &mut interpreter::Interpreter, filename: &str) -> Result<(), std::io::Error> {
    use std::fs::File;
    use std::io::BufRead;
    use std::io::BufReader;
    use std::io::Error;
    use std::io::ErrorKind;
    use parser::{Lexer, Parser};

    let f = File::open(filename)?;
    let file = BufReader::new(&f);
    for line in file.lines() {
        let line = line?.to_owned();
        let mut lexer = Lexer::new(line.chars());
        let mut parser = Parser::new(lexer);

        match parser.parse() {
            Ok(stmt) => interpreter.eval(&stmt),
            Err(err) => return Err(Error::new(ErrorKind::Other, format!("Could not parse! {:?}", err))),
        };
    }

    Ok(())
}

fn main() {
    let matches = clap::App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .about("Simple REPL for untyped lambda calculus")
        .arg(
            clap::Arg::with_name("preamble")
                .short("p")
                .long("preamble")
                .value_name("FILE")
                .help("Preamble for the REPL session")
                .takes_value(true),
        ).get_matches();

    std::env::set_var("RUST_LOG", "info");
    pretty_env_logger::init();

    let mut rl = rustyline::Editor::<()>::new();
    let mut variable_pool = variable::DefaultVariablePool::new();
    let mut interpreter = interpreter::Interpreter::new(&mut variable_pool);

    if let Some(filename) = matches.value_of("preamble") {
        match eval_file(&mut interpreter, filename) {
            Ok(_) => (),
            Err(err) => {
                error!("Error while loading the preamble {:?}", err);
                ::std::process::exit(1);
            }
        };
    }

    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_ref());
                let mut lexer = parser::Lexer::new(line.chars());
                let mut parser = parser::Parser::new(lexer);

                match parser.parse() {
                    Ok(stmt) => interpreter.eval(&stmt),
                    Err(err) => error!("Could not parse! {:?}", err),
                };
            }
            Err(_) => break,
        }
    }
}
