#![allow(clippy::uninlined_format_args)]

use std::collections::HashMap;
use std::fmt;
use std::iter;
use std::iter::Peekable;
use std::process::exit;
use std::slice::Iter;
use std::str::Chars;

fn main() {
    let args = parse_args();
    let contents = std::fs::read_to_string(&args.input).or_exit(format!("open '{}'", args.input));
    let tokens = lex(&contents);
    let table = parse(&tokens);

    if args.interactive {
        let accept = interactive_exec(&table, args.argument);
        exit(i32::from(!accept));
    }
}

#[derive(Debug)]
struct Args {
    input: String,
    #[allow(unused)]
    output: Option<String>,
    argument: Option<String>,
    interactive: bool,
}

fn parse_args() -> Args {
    let args = std::env::args().collect::<Vec<String>>();
    let args = args.iter().map(String::as_str).collect::<Vec<&str>>();
    let [_progname, tail @ ..] = args.as_slice() else {
        usage_err("empty args list");
    };

    let mut it = tail;
    let mut output = None;
    let mut input = None;
    let mut argument = None;
    let mut interactive = false;

    loop {
        match it {
            ["-h" | "--help", ..] => usage(0),
            ["-v" | "--version", ..] => version(),
            ["-o" | "--output", filename, rest @ ..] => {
                output = Some((*filename).to_string());
                it = rest;
            }
            ["-a" | "--argument", tape_input, rest @ ..] => {
                argument = Some((*tape_input).to_string());
                it = rest;
            }
            ["-i" | "--interactive", rest @ ..] => {
                interactive = true;
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

    Args {
        input,
        output,
        argument,
        interactive,
    }
}

fn usage_err(msg: &'static str) -> ! {
    eprintln!("Error: {}", msg);
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

#[derive(Debug, PartialEq)]
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

struct Table {
    alphabet: Vec<char>,
    st_actions: Vec<StateActions>,
}

struct StateActions {
    state: State,
    actions: Vec<Action>,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct State(String);

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
struct Symbol(char);

#[derive(Clone)]
struct Action {
    symbol: Symbol,
    movement: Movement,
    state_tr: StateTransition,
}

#[derive(Clone, Copy)]
enum Movement {
    Left,
    Right,
}

#[derive(Clone)]
enum StateTransition {
    Next(String),
    Accept,
    Reject,
}

impl fmt::Display for Table {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for sym in &self.alphabet {
            write!(f, "{} ", sym)?;
        }

        writeln!(f)?;

        for s in &self.st_actions {
            writeln!(f, "{}", s)?;
        }

        Ok(())
    }
}

impl fmt::Display for StateActions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ", self.state.0)?;

        for a in &self.actions {
            write!(f, "{} ", a)?;
        }

        Ok(())
    }
}

impl fmt::Display for Action {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.symbol.0, self.movement, self.state_tr)
    }
}

impl fmt::Display for Movement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            Movement::Left => "<",
            Movement::Right => ">",
        };

        write!(f, "{}", s)
    }
}

impl fmt::Display for StateTransition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            StateTransition::Next(st) => st,
            StateTransition::Accept => "A",
            StateTransition::Reject => "R",
        };

        write!(f, "{}", s)
    }
}

fn parse(tokens: &[Token]) -> Table {
    let mut it = tokens.iter().peekable();
    let mut st_actions = vec![];

    let alphabet = parse_alphabet(&mut it);

    while it.peek().is_some() {
        st_actions.push(parse_line(&mut it, &alphabet));
    }

    Table {
        alphabet,
        st_actions,
    }
}

type TokIter<'a> = Peekable<Iter<'a, Token>>;

fn parse_alphabet(it: &mut TokIter) -> Vec<char> {
    let mut alphabet = vec![];

    loop {
        match it.peek() {
            Some(Token::NewLine) => break,
            None => parsing_err("unexpected end of file"),
            _ => (),
        }

        alphabet.push(parse_symbol(it).0);
    }

    consume_newline(it);

    if alphabet.is_empty() {
        parsing_err("empty alphabet");
    }

    alphabet
}

fn consume_newline(it: &mut TokIter) {
    match next_token(it) {
        Token::NewLine => (),
        t => unexpected_token(t),
    }
}

fn parse_symbol(it: &mut TokIter) -> Symbol {
    match next_token(it) {
        Token::Identifier(id) => {
            if id.len() != 1 {
                parsing_err("alphabet's symbols are 1 character long");
            }
            let s = id.chars().next().unwrap();
            Symbol(s)
        }
        t => unexpected_token(t),
    }
}

fn next_token<'i>(it: &mut TokIter<'i>) -> &'i Token {
    match it.next() {
        Some(t) => t,
        None => parsing_err("unexpected end of file"),
    }
}

fn parsing_err<S>(msg: S) -> !
where
    S: AsRef<str> + fmt::Display,
{
    eprintln!("Parsing error: {}", msg);
    exit(1);
}

fn unexpected_token(t: &Token) -> ! {
    parsing_err(format!("unexpected token {:?}", t));
}

fn parse_line(it: &mut TokIter, alphabet: &[char]) -> StateActions {
    let state = parse_state(it);
    let mut actions = vec![];

    for _ in alphabet {
        actions.push(parse_action(it));
    }

    consume_newline(it);

    StateActions { state, actions }
}

fn parse_state(it: &mut TokIter) -> State {
    match next_token(it) {
        Token::Identifier(id) => State(id.clone()),
        t => unexpected_token(t),
    }
}

fn parse_action(it: &mut TokIter) -> Action {
    let symbol = parse_symbol(it);
    let movement = parse_movement(it);
    let state_tr = parse_state_transition(it);

    Action {
        symbol,
        movement,
        state_tr,
    }
}

fn parse_movement(it: &mut TokIter) -> Movement {
    match next_token(it) {
        Token::MoveRight => Movement::Right,
        Token::MoveLeft => Movement::Left,
        t => unexpected_token(t),
    }
}

fn parse_state_transition(it: &mut TokIter) -> StateTransition {
    match next_token(it) {
        Token::Identifier(id) => StateTransition::Next(id.clone()),
        Token::Accept => StateTransition::Accept,
        Token::Reject => StateTransition::Reject,
        t => unexpected_token(t),
    }
}

struct JumpTable {
    mappings: HashMap<(Symbol, State), Action>,
}

struct Tape {
    positive: Vec<Symbol>,
    negative: Vec<Symbol>,
    head: isize,
    blank: Symbol,
}

impl JumpTable {
    fn from_table(table: &Table) -> Self {
        let mut mappings = HashMap::new();

        for s in &table.st_actions {
            let state = &s.state;

            for (i, action) in s.actions.iter().enumerate() {
                let symbol = Symbol(table.alphabet[i]);

                mappings.insert((symbol, state.clone()), action.clone());
            }
        }

        JumpTable { mappings }
    }

    fn lookup(&self, sym: Symbol, state: State) -> &Action {
        self.mappings.get(&(sym, state)).unwrap()
    }
}

impl Tape {
    fn from_string(blank: Symbol, arg: String) -> Self {
        let positive = arg
            .into_bytes()
            .iter()
            .map(|b| Symbol(*b as char))
            .collect();

        Tape {
            positive,
            negative: Vec::new(),
            head: 0,
            blank,
        }
    }

    fn empty(blank: Symbol) -> Self {
        Tape {
            positive: Vec::new(),
            negative: Vec::new(),
            head: 0,
            blank,
        }
    }

    #[allow(clippy::cast_sign_loss)]
    fn get_symbol(&mut self) -> Symbol {
        let h = self.head;

        if h >= 0 {
            let h = h as usize;

            if h >= self.positive.len() {
                self.extend_tape_positive(h);
            }

            self.positive[h]
        } else {
            let h = (-h - 1) as usize;

            if h >= self.negative.len() {
                self.extend_tape_negative(h);
            }

            self.negative[h]
        }
    }

    fn extend_tape_positive(&mut self, h: usize) {
        let num_items = h + 1 - self.positive.len();
        let items = iter::repeat(self.blank)
            .take(num_items)
            .collect::<Vec<Symbol>>();

        self.positive.extend_from_slice(&items);
    }

    fn extend_tape_negative(&mut self, h: usize) {
        let num_items = h + 1 - self.negative.len();
        let items = iter::repeat(self.blank)
            .take(num_items)
            .collect::<Vec<Symbol>>();

        self.negative.extend_from_slice(&items);
    }

    #[allow(clippy::cast_sign_loss)]
    fn write(&mut self, symbol: Symbol) {
        if self.head >= 0 {
            self.positive[self.head as usize] = symbol;
        } else {
            let h = -self.head - 1;
            self.negative[h as usize] = symbol;
        }
    }

    fn shift(&mut self, movement: Movement) {
        match movement {
            Movement::Left => self.head -= 1,
            Movement::Right => self.head += 1,
        }
    }
}

impl fmt::Display for Tape {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for s in self.negative.iter().rev() {
            write!(f, "{}", s.0)?;
        }

        for s in &self.positive {
            write!(f, "{}", s.0)?;
        }

        Ok(())
    }
}

fn interactive_exec(table: &Table, argument: Option<String>) -> bool {
    let jt = JumpTable::from_table(table);
    let blank = Symbol(table.alphabet[0]);

    let mut tape = if let Some(initial_tape) = argument {
        Tape::from_string(blank, initial_tape)
    } else {
        Tape::empty(blank)
    };

    let mut state = table.st_actions[0].state.clone();

    let accept = loop {
        let symbol = tape.get_symbol();
        let action = jt.lookup(symbol, state);

        tape.write(action.symbol);
        tape.shift(action.movement);

        match &action.state_tr {
            StateTransition::Next(next_st) => state = State(next_st.clone()),
            StateTransition::Accept => {
                println!("Accept");
                break true;
            }
            StateTransition::Reject => {
                println!("Reject");
                break false;
            }
        }
    };

    println!("Tape: {}", tape);

    accept
}
