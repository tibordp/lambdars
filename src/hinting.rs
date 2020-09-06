use regex::Regex;
use std::borrow::Cow::{self, Borrowed, Owned};
use std::cell::RefCell;
use std::collections::HashSet;

use crate::runtime::Runtime;
use rustyline::completion::Completer;
use rustyline::{Context, Result};

#[derive(rustyline_derive::Highlighter, rustyline_derive::Hinter, rustyline_derive::Helper, rustyline_derive::Validator)]
pub struct Helper<'a> {
    pub hints: &'a RefCell<Runtime>,
}

impl<'a> Completer for Helper<'a> {
    type Candidate = String;

    fn complete(&self, line: &str, pos: usize, ctx: &Context) -> Result<(usize, Vec<Self::Candidate>)> {
        let regex = Regex::new(r"[\s()\\.]").expect("Invalid regex");
        let prefix = regex.split(&line[0..pos]).last().unwrap_or("");
        let mut candidates: Vec<_> = self
            .hints
            .borrow()
            .macros
            .iter()
            .map(|(k, _)| format!("{}", k))
            .filter(|k| k.starts_with(prefix))
            .collect();
        candidates.sort();

        Ok((pos - prefix.len(), candidates))
    }
}
