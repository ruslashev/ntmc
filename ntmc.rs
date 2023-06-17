#![allow(clippy::uninlined_format_args)]

use std::fmt;
use std::iter::Peekable;
use std::process::exit;
use std::str::Chars;

fn main() {
    let args = parse_args();
    let contents = std::fs::read_to_string(&args.input).or_exit(format!("open '{}'", args.input));
    let tokens = lex(&contents);

    println!("tokens = {:#?}", tokens);
}

#[derive(Debug)]
struct Args {
    input: String,
    #[allow(unused)]
    output: Option<String>,
}

fn parse_args() -> Args {
    let args = std::env::args().collect::<Vec<String>>();
    let args = args.iter().map(String::as_str).collect::<Vec<&str>>();
    let [_progname, tail @ ..] = args.as_slice() else {
        usage_err("empty args list");
    };

    let mut it = tail;
    let mut input = None;
    let mut output = None;

    loop {
        match it {
            ["-h" | "--help", ..] => usage(0),
            ["-v" | "--version", ..] => version(),
            ["-o" | "--output", filename, rest @ ..] => {
                output = Some((*filename).to_string());
                it = rest;
            }
            [filename, rest @ ..] => {
                match input {
                    None => input = Some((*filename).to_string()),
                    Some(_) => usage_err("multiple input files provided"),
                }
                it = rest;
            }
            _ => break,
        }
    }

    let input = input.unwrap_or_else(|| usage_err("no input filename given"));

    Args { input, output }
}

fn usage_err(msg: &'static str) -> ! {
    println!("Error: {}", msg);
    usage(1);
}

fn usage(ret: i8) -> ! {
    let text = "\
Usage: ntmc [options] <file>
Options:
    -o, --output <file>   Store output in <file>
    -h, --help            Display help
    -v, --version         Display version";

    println!("{}", text);

    exit(ret.into());
}

fn version() -> ! {
    println!("ntmc {}", env!("CARGO_PKG_VERSION"));
    exit(0);
}

trait MaybeError<T, S: AsRef<str>> {
    fn or_exit(self, message: S) -> T;
}

impl<T, S, E> MaybeError<T, S> for Result<T, E>
where
    S: AsRef<str> + fmt::Display,
    E: fmt::Display,
{
    fn or_exit(self, message: S) -> T {
        match self {
            Ok(t) => t,
            Err(e) => {
                eprintln!("Failed to {}: {}", message, e);
                exit(1);
            }
        }
    }
}

#[derive(Debug)]
enum Token {
    Identifier(String),
    MoveRight,
    MoveLeft,
    Accept,
    Reject,
    NewLine,
}

fn lex(source: &str) -> Vec<Token> {
    let mut tokens = vec![];
    let mut it = source.chars().peekable();

    while let Some(c) = it.next() {
        if c == '\n' {
            tokens.push(Token::NewLine);
            continue;
        }

        if c.is_whitespace() {
            continue;
        }

        if c.is_alphanumeric() {
            tokens.push(lex_identifier(c, &mut it));
            continue;
        }

        if c == '<' {
            tokens.push(Token::MoveLeft);
            continue;
        }

        if c == '>' || c == '.' {
            tokens.push(Token::MoveRight);
            continue;
        }

        eprintln!("Unexpected character '{}'", c);
    }

    tokens
}

fn lex_identifier(mut c: char, it: &mut Peekable<Chars<'_>>) -> Token {
    let mut id = String::new();

    loop {
        id.push(c);

        if let Some(p) = it.peek() {
            if !p.is_alphanumeric() {
                break;
            }
        }

        c = match it.next() {
            Some(c) => c,
            None => break,
        }
    }

    match id.as_str() {
        "A" | "Acc" | "Accept" | "H" | "Halt" => Token::Accept,
        "R" | "Rej" | "Reject" => Token::Reject,
        _ => Token::Identifier(id),
    }
}
