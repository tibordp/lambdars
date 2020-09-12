use crate::expression::Expression;
use crate::variable::Variable;
use std::collections::HashSet;
use std::error;
use std::fmt;
use std::iter::Peekable;
use std::str::FromStr;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OutputMode {
    Default,
    Javascript,
}

impl FromStr for OutputMode {
    type Err = Error;
    fn from_str(input: &str) -> Result<OutputMode, Self::Err> {
        match input {
            "javascript" => Ok(OutputMode::Javascript),
            "default" => Ok(OutputMode::Default),
            _ => Err(Error::Unexpected(input.to_owned())),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum AstNode {
    Nothing,
    Define(Variable, Expression),
    Declare(Variable, Expression),
    SetMaxReductions(u32),
    SetMaxSize(u32),
    SetMaxDepth(u32),
    SetAutoReduce(bool),
    SetOutputMode(OutputMode),
    Dump,
    Clear,
    Expression(Expression),
    Reduce(Expression),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    OpenParen,
    CloseParen,
    Lambda,
    Dot,
    LastOutput,
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
        Self {
            iter: it.peekable(),
        }
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
            Some('@') => {
                self.iter.next();
                Some(Token::LastOutput)
            }
            Some(';') => {
                while let Some(_) = self.iter.next() {}
                None
            }
            Some('#') => {
                let mut iden = String::default();
                self.iter.next();
                while let Some(ch) = self.iter.peek().cloned() {
                    match ch {
                        'A'..='Z' | 'a'..='z' | '_' | '0'..='9' => {
                            iden.push(self.iter.next().unwrap())
                        }
                        _ => break,
                    }
                }
                Some(Token::Command(iden))
            }
            Some('A'..='Z') | Some('a'..='z') | Some('_') | Some('0'..='9') => {
                let mut iden = String::default();
                while let Some(ch) = self.iter.peek().cloned() {
                    match ch {
                        'A'..='Z' | 'a'..='z' | '_' | '0'..='9' => {
                            iden.push(self.iter.next().unwrap())
                        }
                        _ => break,
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

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    UnexpectedToken(Token),
    RedefinedVariable(Variable),
    UnknownCommand(String),
    Unexpected(String),
    Unterminated,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::UnexpectedToken(ref token) => write!(f, "Unexpected token {:?}", token),
            Error::RedefinedVariable(ref variable) => {
                write!(f, "Variable {} is redefined in the inner scope", variable)
            }
            Error::Unterminated => write!(f, "Unterminated expression"),
            Error::Unexpected(ref found) => write!(f, "Unexpected '{}' found", found),
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
        Ok(Expression::Lambda(variable, box expression))
    }

    fn parse_paren(&mut self) -> Result<Expression, Error> {
        assert_token!(self.it.next(), Token::OpenParen)?;
        self.parse_expression(true)
    }

    fn parse_last_output(&mut self) -> Result<Expression, Error> {
        assert_token!(self.it.next(), Token::LastOutput)?;
        Ok(Expression::Variable(Variable::new("@".to_owned(), 0)))
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
                Some(Token::LastOutput) => self.parse_last_output(),
                Some(Token::Identifier(_)) => self.parse_variable_expression(),
                _ => break,
            };

            result = match result {
                Some(expression) => Some(Expression::Apply(box expression, box subexpression?)),
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

    fn parse_reduce(&mut self) -> Result<AstNode, Error> {
        self.it.next();
        let expression = self.parse_expression(false)?;
        Ok(AstNode::Reduce(expression))
    }

    fn parse_define(&mut self) -> Result<AstNode, Error> {
        self.it.next();
        let variable = Self::get_variable(self.it.next())?;
        let expression = self.parse_expression(false)?;
        Ok(AstNode::Define(variable, expression))
    }

    fn parse_declare(&mut self) -> Result<AstNode, Error> {
        self.it.next();
        let variable = Self::get_variable(self.it.next())?;
        let expression = self.parse_expression(false)?;
        Ok(AstNode::Declare(variable, expression))
    }

    fn parse_parametrized<U: FromStr>(&mut self) -> Result<U, Error> {
        self.it.next();
        let variable = Self::get_variable(self.it.next())?;
        let variable_name = variable.value();
        variable_name
            .parse::<U>()
            .map_err(|_| Error::Unexpected(variable_name.to_owned()))
    }

    pub fn parse(&mut self) -> Result<AstNode, Error> {
        match self.it.peek().cloned() {
            Some(Token::Command(s)) => match s.as_ref() {
                "define" => self.parse_define(),
                "declare" => self.parse_declare(),
                "reduce" => self.parse_reduce(),
                "max_reductions" => self.parse_parametrized().map(AstNode::SetMaxReductions),
                "max_size" => self.parse_parametrized().map(AstNode::SetMaxSize),
                "max_depth" => self.parse_parametrized().map(AstNode::SetMaxDepth),
                "auto_reduce" => self.parse_parametrized().map(AstNode::SetAutoReduce),
                "output_mode" => self.parse_parametrized().map(AstNode::SetOutputMode),
                "dump" => {
                    self.it.next();
                    Ok(AstNode::Dump)
                }
                "clear" => {
                    self.it.next();
                    Ok(AstNode::Clear)
                }
                s => Err(Error::UnknownCommand(s.to_owned())),
            },
            Some(Token::OpenParen)
            | Some(Token::CloseParen)
            | Some(Token::Lambda)
            | Some(Token::LastOutput)
            | Some(Token::Identifier(_)) => self.parse_expression(false).map(AstNode::Expression),
            Some(tok) => Err(Error::UnexpectedToken(tok)),
            None => Ok(AstNode::Nothing),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;

    #[test]
    fn parse_lambda_expression() {
        let line = "\\x.\\y.x y";
        let mut parser = Parser::new(Lexer::new(line.chars()));

        assert_matches!(
            parser.parse(),
            Ok(AstNode::Expression(Expression::Lambda(
                _,
                box Expression::Lambda(
                    _,
                    box Expression::Apply(box Expression::Variable(_), box Expression::Variable(_)),
                ),
            )))
        );
    }

    #[test]
    fn parse_lambda_expression_left_associative() {
        let line = "\\x.x x x x";
        let mut parser = Parser::new(Lexer::new(line.chars()));

        assert_matches!(
            parser.parse(),
            Ok(AstNode::Expression(Expression::Lambda(
                _,
                box Expression::Apply(
                    box Expression::Apply(
                        box Expression::Apply(
                            box Expression::Variable(_),
                            box Expression::Variable(_),
                        ),
                        box Expression::Variable(_),
                    ),
                    box Expression::Variable(_),
                ),
            )))
        );
    }

    #[test]
    fn parse_invalid_command() {
        let line = "#invalid";
        let mut parser = Parser::new(Lexer::new(line.chars()));

        assert_matches!(parser.parse(), Err(Error::UnknownCommand(_)));
    }

    #[test]
    fn parse_incomplete_expression() {
        let line = "\\x.";
        let mut parser = Parser::new(Lexer::new(line.chars()));

        assert_matches!(parser.parse(), Err(Error::Unterminated));
    }

    #[test]
    fn parse_comment() {
        let line = "; comment";
        let mut parser = Parser::new(Lexer::new(line.chars()));

        assert_matches!(parser.parse(), Ok(AstNode::Nothing));
    }

    #[test]
    fn parse_dump() {
        let line = "#dump";
        let mut parser = Parser::new(Lexer::new(line.chars()));

        assert_matches!(parser.parse(), Ok(AstNode::Dump));
    }

    #[test]
    fn parse_define() {
        let line = "#define 0 \\x.\\y.y";
        let mut parser = Parser::new(Lexer::new(line.chars()));

        assert_matches!(
            parser.parse(),
            Ok(AstNode::Define(
                _,
                Expression::Lambda(_, box Expression::Lambda(_, box Expression::Variable(_))),
            ))
        );
    }
}
