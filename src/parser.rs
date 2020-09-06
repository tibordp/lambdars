use crate::expression::Expression;
use crate::variable::Variable;
use std::collections::HashSet;
use std::error;
use std::fmt;
use std::iter::Peekable;
use std::str::FromStr;

#[derive(Debug)]
pub enum AstNode {
    Nothing,
    Define(Variable, Expression),
    SetMaxReductions(u32),
    SetMaxSize(u32),
    SetMaxDepth(u32),
    Dump,
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
    iter: Peekable<T>,
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
                            'A'..='Z' | 'a'..='z' | '_' | '0'..='9' => iden.push(self.iter.next().unwrap()),
                            _ => break,
                        },
                        None => break,
                    }
                }
                Some(Token::Command(iden))
            }
            Some('A'..='Z') | Some('a'..='z') | Some('_') | Some('0'..='9') => {
                let mut iden = String::default();
                loop {
                    match self.iter.peek().cloned() {
                        Some(ch) => match ch {
                            'A'..='Z' | 'a'..='z' | '_' | '0'..='9' => iden.push(self.iter.next().unwrap()),
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
            Some(tok) => Err(Error::UnexpectedToken(tok)),
            None => Err(Error::Unterminated),
        }
    };
}

#[derive(Debug)]
pub enum Error {
    UnexpectedToken(Token),
    RedefinedVariable(Variable),
    UnknownCommand(String),
    ExpectedInteger(String),
    Unterminated,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::UnexpectedToken(ref token) => write!(f, "Unexpected token {:?}", token),
            Error::RedefinedVariable(ref variable) => write!(f, "Variable {} is redefined in the inner scope", variable),
            Error::Unterminated => write!(f, "Unterminated expression"),
            Error::ExpectedInteger(ref found) => write!(f, "Expected integer, '{}' found", found),
            Error::UnknownCommand(ref found) => write!(f, "Unrecognized command #{}", found),
        }
    }
}

impl error::Error for Error {
    fn cause(&self) -> Option<&dyn error::Error> {
        None
    }
}

pub struct Parser<T: Iterator<Item = Token>> {
    it: Peekable<T>,
    variables: HashSet<Variable>,
}

impl<T: Iterator<Item = Token>> Parser<T> {
    pub fn new(it: T) -> Self {
        Self {
            it: it.peekable(),
            variables: HashSet::new(),
        }
    }

    fn get_variable(tok: Option<Token>) -> Result<Variable, Error> {
        match tok {
            Some(Token::Identifier(id)) => Ok(Variable::new(id, 0)),
            Some(tok) => Err(Error::UnexpectedToken(tok)),
            _ => Err(Error::Unterminated),
        }
    }

    fn parse_lambda(&mut self) -> Result<Expression, Error> {
        assert_token!(self.it.next(), Token::Lambda)?;
        let variable = Self::get_variable(self.it.next())?;
        if self.variables.contains(&variable) {
            return Err(Error::RedefinedVariable(variable));
        }
        assert_token!(self.it.next(), Token::Dot)?;
        self.variables.insert(variable.clone());
        let expression = self.parse_expression(false)?;
        self.variables.remove(&variable);
        Ok(Expression::Lambda(variable, Box::new(expression)))
    }

    fn parse_paren(&mut self) -> Result<Expression, Error> {
        assert_token!(self.it.next(), Token::OpenParen)?;
        self.parse_expression(true)
    }

    fn parse_variable_expression(&mut self) -> Result<Expression, Error> {
        let variable = Self::get_variable(self.it.next())?;
        Ok(Expression::Variable(variable))
    }

    fn parse_expression(&mut self, parentheses: bool) -> Result<Expression, Error> {
        let mut result: Option<Expression> = None;

        loop {
            let subexpression: Result<Expression, Error> = match self.it.peek().cloned() {
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
            Err(Error::Unterminated)
        }
    }

    fn parse_define(&mut self) -> Result<AstNode, Error> {
        self.it.next();
        let variable = Self::get_variable(self.it.next())?;
        let expression = self.parse_expression(false)?;
        Ok(AstNode::Define(variable, expression))
    }

    fn parse_parametrized<U: FromStr>(&mut self) -> Result<U, Error> {
        self.it.next();
        let variable = Self::get_variable(self.it.next())?;
        let variable_name = variable.value();
        variable_name
            .parse::<U>()
            .map_err(|_| Error::ExpectedInteger(variable_name.to_owned()))
    }

    pub fn parse(&mut self) -> Result<AstNode, Error> {
        match self.it.peek().cloned() {
            Some(Token::Command(s)) => match s.as_ref() {
                "define" => self.parse_define(),
                "max_reductions" => self.parse_parametrized().map(AstNode::SetMaxReductions),
                "max_size" => self.parse_parametrized().map(AstNode::SetMaxSize),
                "max_depth" => self.parse_parametrized().map(AstNode::SetMaxDepth),
                "dump" => {
                    self.it.next();
                    Ok(AstNode::Dump)
                }
                s => Err(Error::UnknownCommand(s.to_owned())),
            },
            Some(Token::OpenParen) | Some(Token::CloseParen) | Some(Token::Lambda) | Some(Token::Identifier(_)) => {
                self.parse_expression(false).map(AstNode::Reduce)
            }
            Some(tok) => Err(Error::UnexpectedToken(tok)),
            None => Ok(AstNode::Nothing),
        }
    }
}
