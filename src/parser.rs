    use std::collections::HashSet;
    use std::iter;
    use expression::Expression;
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