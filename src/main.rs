#[macro_use]
extern crate log;
extern crate clap;
extern crate pretty_env_logger;
extern crate rustyline;

mod expression;
mod interpreter;
mod parser;
mod variable;

fn eval_file(interpreter: &mut interpreter::Interpreter, filename: &str) -> Result<(), std::io::Error> {
    use parser::{Lexer, Parser};
    use std::fs::File;
    use std::io::BufRead;
    use std::io::BufReader;
    use std::io::Error;
    use std::io::ErrorKind;

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
