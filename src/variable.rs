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