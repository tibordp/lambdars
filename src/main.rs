pub mod expression;
pub mod hinting;
pub mod parser;
pub mod runtime;
pub mod variable;

use log::{error, warn};
use std::convert::From;
use std::error;
use std::fmt;
use std::io;

#[derive(Debug)]
pub enum ReplError {
    Io(io::Error),
    Parse(parser::Error),
    Runtime(runtime::Error),
}

impl fmt::Display for ReplError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ReplError::Io(ref err) => write!(f, "IO error: {}", err),
            ReplError::Parse(ref err) => write!(f, "Parse error: {}", err),
            ReplError::Runtime(ref err) => write!(f, "Runtime error: {}", err),
        }
    }
}

impl error::Error for ReplError {
    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            ReplError::Io(ref err) => Some(err),
            ReplError::Parse(ref err) => Some(err),
            ReplError::Runtime(ref err) => Some(err),
        }
    }
}

impl From<io::Error> for ReplError {
    fn from(err: io::Error) -> Self {
        ReplError::Io(err)
    }
}

impl From<runtime::Error> for ReplError {
    fn from(err: runtime::Error) -> Self {
        ReplError::Runtime(err)
    }
}

impl From<parser::Error> for ReplError {
    fn from(err: parser::Error) -> Self {
        ReplError::Parse(err)
    }
}

fn eval_line(runtime: &mut runtime::Runtime, line: &str) -> Result<(), ReplError> {
    use parser::{Lexer, Parser};

    let mut parser = Parser::new(Lexer::new(line.chars()));
    let ast = &(parser.parse()?);
    if let Some(result) = runtime.eval(ast)? {
        println!("{}", result);
    }

    Ok(())
}

fn history_file(matches: &clap::ArgMatches) -> Option<std::path::PathBuf> {
    use std::path::Path;

    if let Some(filename) = matches.value_of("history_file") {
        return Some(Path::new(filename).to_owned());
    }
    match dirs::home_dir() {
        Some(mut dir) => {
            dir.push(".lambdars_history");
            Some(dir)
        }
        None => None,
    }
}

fn repl(matches: &clap::ArgMatches) -> Result<(), ReplError> {
    use rustyline::error::ReadlineError;
    use std::cell::RefCell;
    use std::fs::File;
    use std::io::{BufRead, BufReader, ErrorKind};

    let variable_pool = Box::new(variable::DefaultVariablePool::new());
    let runtime = RefCell::new(runtime::Runtime::new(variable_pool));

    let mut rl = rustyline::Editor::<hinting::Helper>::new();
    let hinter = hinting::Helper { hints: &runtime };

    rl.set_helper(Some(hinter));
    let history_file = history_file(matches);

    if let Some(history_file) = &history_file {
        match rl.load_history(history_file) {
            Ok(_) => {}
            Err(ReadlineError::Io(err)) if err.kind() == ErrorKind::NotFound => {}
            Err(err) => {
                warn!("Could not load history file ({})", err);
            }
        }
    }

    if let Some(filename) = matches.value_of("preamble") {
        let f = File::open(filename)?;
        let file = BufReader::new(&f);
        for line in file.lines() {
            let line = &(line?);
            eval_line(&mut runtime.borrow_mut(), line)?;
        }
    }

    loop {
        let readline = rl.readline("> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.clone());
                match eval_line(&mut runtime.borrow_mut(), &line) {
                    Err(err) => warn!("{}", err),
                    _ => (),
                };
            }
            Err(ReadlineError::Interrupted) => {}
            Err(_) => break,
        }
    }

    if let Some(history_file) = &history_file {
        if let Err(err) = rl.save_history(history_file) {
            warn!("Could not save history file {}", err)
        }
    }

    Ok(())
}

fn main() {
    std::env::set_var("RUST_LOG", "info");
    pretty_env_logger::init();

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
        )
        .arg(
            clap::Arg::with_name("history_file")
                .long("history-file")
                .value_name("FILE")
                .help("Where to save REPL history")
                .takes_value(true),
        )
        .get_matches();

    match repl(&matches) {
        Ok(()) => {}
        Err(err) => {
            error!("{}", err);
            std::process::exit(1);
        }
    }
}
