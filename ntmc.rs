#![allow(clippy::missing_panics_doc)]
#![allow(clippy::missing_safety_doc)]
#![allow(clippy::uninlined_format_args)]

use std::arch::asm;
use std::collections::HashMap;
use std::ffi::{c_int, c_void};
use std::fmt::{self, Display, Formatter};
use std::hash::Hash;
use std::iter::Peekable;
use std::process::exit;
use std::str::Chars;
use std::{iter, ptr, slice};

fn main() {
    let args = parse_args();
    let contents = std::fs::read_to_string(&args.input).or_exit(format!("open '{}'", args.input));
    let tokens = lex(&contents);
    let table = parse(&tokens);

    let accept = if args.interactive {
        interactive_exec(&table, args.argument, args.trace)
    } else {
        jit_compile(&table, args.argument, args.trace)
    };

    exit(i32::from(!accept));
}

#[derive(Debug)]
struct Args {
    input: String,
    #[allow(unused)]
    output: Option<String>,
    argument: Option<String>,
    interactive: bool,
    trace: bool,
}

/// Poor man's argument parser, stolen from [Daily Rust: Slice Patterns][SlicePatterns].
/// Does not support merged short options (`-it` instead of `-i -t`).
///
/// [SlicePatterns]: https://adventures.michaelfbryan.com/posts/daily/slice-patterns/#a-poor-mans-argument-parser
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
    let mut trace = false;

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
            ["-t" | "--trace", rest @ ..] => {
                trace = true;
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
        trace,
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
    -a, --argument <str>  Initial value of tape
    -i, --interactive     Interactive/interpreter mode
    -t, --trace           Trace execution
    -h, --help            Display help
    -v, --version         Display version";

    println!("{}", text);

    exit(ret.into());
}

fn version() -> ! {
    println!("ntmc {}", env!("CARGO_PKG_VERSION"));
    exit(0);
}

macro_rules! die {
    ($( $arg:tt )*) => {
        {
            eprintln!($($arg)*);
            exit(1);
        }
    }
}

trait MaybeError<T, S> {
    fn or_exit(self, message: S) -> T;
}

impl<T, S, E> MaybeError<T, S> for Result<T, E>
where
    S: AsRef<str> + Display,
    E: Display,
{
    fn or_exit(self, message: S) -> T {
        match self {
            Ok(t) => t,
            Err(e) => die!("Failed to {}: {}", message, e),
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

        if c == '#' {
            for c in it.by_ref() {
                if c == '\n' {
                    break;
                }
            }
            tokens.push(Token::NewLine);
            continue;
        }

        if c.is_alphanumeric() {
            tokens.push(lex_identifier(c, &mut it));
            continue;
        }

        let token = match c {
            '<' => Token::MoveLeft,
            '>' => Token::MoveRight,
            '_' => Token::Identifier(' '.to_string()),
            c => Token::Identifier(c.to_string()),
        };

        tokens.push(token);
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

impl Display for Table {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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

impl Display for StateActions {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} ", self.state.0)?;

        for a in &self.actions {
            write!(f, "{} ", a)?;
        }

        Ok(())
    }
}

impl Display for Action {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}{}", self.symbol.0, self.movement, self.state_tr)
    }
}

impl Display for Movement {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = match self {
            Movement::Left => "<",
            Movement::Right => ">",
        };

        write!(f, "{}", s)
    }
}

impl Display for StateTransition {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let s = match self {
            StateTransition::Next(st) => st,
            StateTransition::Accept => "A",
            StateTransition::Reject => "R",
        };

        write!(f, "{}", s)
    }
}

impl From<u8> for Movement {
    fn from(v: u8) -> Self {
        match v {
            0 => Movement::Left,
            1 => Movement::Right,
            x => die!("invalid number representing movement: {:#x}", x),
        }
    }
}

fn parse(tokens: &[Token]) -> Table {
    let mut it = tokens.iter().peekable();
    let mut st_actions = vec![];

    skip_newlines(&mut it);

    let alphabet = parse_alphabet(&mut it);

    while it.peek().is_some() {
        if let Some(Token::NewLine) = it.peek() {
            it.next();
            continue;
        }
        st_actions.push(parse_line(&mut it, &alphabet));
    }

    Table {
        alphabet,
        st_actions,
    }
}

type TokIter<'a> = Peekable<slice::Iter<'a, Token>>;

fn skip_newlines(it: &mut TokIter) {
    while let Some(Token::NewLine) = it.peek() {
        it.next();
    }
}

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
    S: AsRef<str> + Display,
{
    die!("Parsing error: {}", msg);
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

    fn lookup(&self, sym: Symbol, state: &State) -> &Action {
        self.mappings.get(&(sym, state.clone())).unwrap_or_else(|| {
            die!(
                "Error: no actions matched symbol '{}' at state '{}'",
                sym.0,
                state.0
            );
        })
    }
}

impl Tape {
    fn new(blank: Symbol) -> Self {
        Tape {
            positive: Vec::new(),
            negative: Vec::new(),
            head: 0,
            blank,
        }
    }

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

    fn from_argument(argument: Option<String>, blank: Symbol) -> Self {
        if let Some(initial_tape) = argument {
            Self::from_string(blank, initial_tape)
        } else {
            Self::new(blank)
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

impl Display for Tape {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut chars = vec![];

        for s in self.negative.iter().rev() {
            chars.push(s.0);
        }

        for s in &self.positive {
            chars.push(s.0);
        }

        assert!(self.negative.len() < isize::MAX as usize);
        #[allow(clippy::cast_possible_wrap)]
        let tape_idx = self.negative.len() as isize + self.head;

        for (i, c) in chars.iter().enumerate() {
            assert!(i < isize::MAX as usize);
            #[allow(clippy::cast_possible_wrap)]
            let i = i as isize;

            if i == tape_idx {
                let inverse = "\x1b[7m";
                let normal = "\x1b[m";
                write!(f, "{}{}{}", inverse, c, normal)?;
            } else {
                write!(f, "{}", c)?;
            }
        }

        Ok(())
    }
}

fn interactive_exec(table: &Table, argument: Option<String>, trace: bool) -> bool {
    let jt = JumpTable::from_table(table);
    let blank = Symbol(table.alphabet[0]);

    let mut tape = Tape::from_argument(argument, blank);
    let mut state = table.st_actions[0].state.clone();

    let accept = loop {
        if trace {
            println!("tape={}, state={}", tape, state.0);
        }

        let symbol = tape.get_symbol();
        let action = jt.lookup(symbol, &state);

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

extern "C" {
    fn mmap(
        addr: *mut c_void,
        length: usize,
        prot: c_int,
        flags: c_int,
        fd: c_int,
        offset: i64,
    ) -> *mut c_void;
    fn munmap(addr: *mut c_void, length: usize) -> c_int;
    fn mprotect(addr: *mut c_void, len: usize, prot: c_int) -> c_int;
    fn __errno_location() -> *mut c_int;
}

const PROT_READ: c_int = 1;
const PROT_WRITE: c_int = 2;
const PROT_EXEC: c_int = 4;

const MAP_PRIVATE: c_int = 0x2;
const MAP_ANONYMOUS: c_int = 0x20;
const MAP_FAILED: *mut c_void = !0 as *mut c_void;

struct MappedBuffer {
    addr: *mut c_void,
    size: usize,
    write_idx: usize,
}

impl MappedBuffer {
    fn new(pages: usize) -> Self {
        let size = pages * 4096;
        let addr = unsafe {
            mmap(
                ptr::null_mut(),
                size,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS,
                -1,
                0,
            )
        };

        libc_assert(addr != MAP_FAILED, "Mapping failed");

        MappedBuffer {
            addr,
            size,
            write_idx: 0,
        }
    }

    fn write(&mut self, data: &[u8]) {
        let write = self.write_idx..self.write_idx + data.len();

        if write.end > self.size {
            die!("Mapped buffer overflow");
        }

        let slice = unsafe { self.as_slice_mut() };

        slice[write].copy_from_slice(data);

        self.write_idx += data.len();
    }

    unsafe fn as_slice(&self) -> &[u8] {
        std::slice::from_raw_parts(self.addr.cast(), self.size)
    }

    unsafe fn as_slice_mut(&mut self) -> &mut [u8] {
        std::slice::from_raw_parts_mut(self.addr.cast(), self.size)
    }

    fn into_executable(self) -> ExecBuffer {
        let ret = unsafe { mprotect(self.addr, self.size, PROT_READ | PROT_EXEC) };

        libc_assert(ret == 0, "Failed to make buffer executable");

        ExecBuffer { buf: self }
    }

    #[allow(unused)]
    fn hexdump(&self) {
        let full = unsafe { self.as_slice() };
        let slice = &full[0..self.write_idx];

        hexdump(slice, 16, true);
    }
}

fn hexdump(slice: &[u8], cols: usize, print_offsets: bool) {
    for (i, line) in slice.chunks(cols).enumerate() {
        if print_offsets {
            print!("{:04x}: ", i * cols);
        }

        for byte in line {
            print!("{:02x} ", byte);
        }

        println!();
    }
}

impl Drop for MappedBuffer {
    fn drop(&mut self) {
        let ret = unsafe { munmap(self.addr, self.size) };

        libc_assert(ret == 0, "Failed to unmap");
    }
}

struct ExecBuffer {
    buf: MappedBuffer,
}

impl ExecBuffer {
    fn execute(self) -> u64 {
        let code: fn() -> u64 = unsafe { std::mem::transmute(self.buf.addr) };

        code()
    }
}

fn libc_assert(condition: bool, msg: &str) {
    if condition {
        return;
    }

    let errno = unsafe { __errno_location().read() };

    die!("{}: errno = {}", msg, errno);
}

#[rustfmt::skip]
macro_rules! func {
    ($insn:literal $(, $( $opts:tt )+ )*) => {
        unsafe {
            let start: u64;
            let end: u64;

            asm!(
                "lea {}, [rip + 2]",
                "jmp 2f",
                $insn,
                "2:",
                "lea {}, [rip - 7]",

                out(reg) start,
                $( $($opts)+ , )*
                out(reg) end,
            );

            slice::from_raw_parts_mut(start as *mut u8, (end - start) as usize)
        }
    };
}

struct CodeBuffer {
    storage: Vec<u8>,
    write_idx: usize,
}

impl CodeBuffer {
    fn new(len: usize) -> Self {
        let nop = func!("nop")[0];
        let storage = vec![nop; len];

        CodeBuffer {
            storage,
            write_idx: 0,
        }
    }

    fn write(&mut self, data: &[u8]) {
        let range = self.write_idx..self.write_idx + data.len();

        if range.end > self.storage.len() {
            die!("Code buffer overflow");
        }

        self.storage[range].copy_from_slice(data);
        self.write_idx += data.len();
    }

    fn as_slice(&self) -> &[u8] {
        self.storage.as_slice()
    }
}

struct SharedState {
    tape: *mut Tape,
    symbols: *const IdxLut<Symbol>,
}

static mut SHARED_STATE: *mut SharedState = ptr::null_mut();

fn jit_compile(table: &Table, argument: Option<String>, _trace: bool) -> bool {
    let mut b = MappedBuffer::new(8);

    let blank = Symbol(table.alphabet[0]);
    let mut tape = Tape::from_argument(argument, blank);

    let symbols = IdxLut::<Symbol>::from_alphabet(&table.alphabet);

    let mut sh_state = SharedState {
        tape: ptr::addr_of_mut!(tape),
        symbols: ptr::addr_of!(symbols),
    };

    unsafe {
        SHARED_STATE = ptr::addr_of_mut!(sh_state);
    }

    write_jumptable(&mut b);
    write_prologue(&mut b);
    write_table(&mut b, &symbols, table, &tape.get_symbol());
    write_epilogue(&mut b);

    let accept = b.into_executable().execute() != 0;

    if accept {
        println!("Accept");
    } else {
        println!("Reject");
    }

    println!("Tape: {}", tape);

    accept
}

fn write_jumptable(b: &mut MappedBuffer) {
    let funs = [
        tape_write as usize,
        tape_shift as usize,
        get_symbol_offset as usize,
    ];

    let mut cb = CodeBuffer::new(16);

    let jump = func!(
        r#"
        // Move back 7 bytes to start of `lea`, skip 16 bytes of `nop`s and 3 entries of jump table
        // (the 3 needs to be manually updated to reflect `funs` array), into the first bytes of code.
        lea rax, [rip - 7 + 16 + 3 * 8]
        jmp rax
        "#
    );

    cb.write(jump);
    b.write(cb.as_slice());

    for f in funs {
        b.write(&f.to_le_bytes());
    }
}

fn write_prologue(b: &mut MappedBuffer) {
    let prologue = func!(
        r#"
        push rbp
        mov rbp, rsp
        sub rsp, 64

        // Skip 7 bytes of `lea`, 8 bytes of 3 preceding instructions, and get the first entry of
        // jump table
        lea rax, [rip - 7 - 8 - 3 * 8]
        mov rdi, [rax]
        mov [rbp - 8], rdi   // 8: tape_write

        mov rdi, [rax + 8]
        mov [rbp - 16], rdi  // 16: tape_shift

        mov rdi, [rax + 16]
        mov [rbp - 24], rdi  // 24: get_symbol_offset

        xor rdi, rdi
        "#
    );

    b.write(prologue);
}

#[no_mangle]
pub unsafe extern "C" fn tape_write(sym: u8) {
    let state = SHARED_STATE.as_mut().unwrap();
    let tape = state.tape.as_mut().unwrap();

    tape.write(Symbol(sym as char));
}

#[no_mangle]
pub unsafe extern "C" fn tape_shift(movement: u8) {
    let state = SHARED_STATE.as_mut().unwrap();
    let tape = state.tape.as_mut().unwrap();

    tape.shift(movement.into());
}

const CELL_SIZE: usize = 41;

#[no_mangle]
pub unsafe extern "C" fn get_symbol_offset() -> u64 {
    let state = SHARED_STATE.as_mut().unwrap();
    let tape = state.tape.as_mut().unwrap();
    let sym = tape.get_symbol();
    let symbols = state.symbols.as_ref().unwrap();
    let idx = symbols.lookup(&sym);
    let offset = idx * CELL_SIZE;

    offset as u64
}

/// A lookup table that maps strings (states) or letters (symbols) into indices. For example, map
/// states `in`, `ds`, `di` to 0, 1, 2. These indices are later used to calculate offset into a
/// 2-dimensional array of actions.
struct IdxLut<T> {
    indices: HashMap<T, usize>,
}

impl<T: Eq + Hash> IdxLut<T> {
    fn from_alphabet(alphabet: &[char]) -> IdxLut<Symbol> {
        let mut indices = HashMap::new();

        for (i, sym) in alphabet.iter().enumerate() {
            indices.insert(Symbol(*sym), i);
        }

        IdxLut { indices }
    }

    fn from_states(st_actions: &[StateActions]) -> IdxLut<String> {
        let mut indices = HashMap::new();

        for (i, s) in st_actions.iter().enumerate() {
            indices.insert(s.state.0.clone(), i);
        }

        IdxLut { indices }
    }

    fn lookup(&self, k: &T) -> usize {
        *self.indices.get(k).unwrap()
    }
}

/// Main part of JIT code generation: convert a 2D table of actions into a 2D table of code. Each
/// cell in the table has fixed size of [`CELL_SIZE`] bytes, padded with NOPs.
fn write_table(b: &mut MappedBuffer, symbols: &IdxLut<Symbol>, table: &Table, first_arg: &Symbol) {
    let initial_jump_size = 16;

    let table_start = b.addr as usize + b.write_idx + initial_jump_size;
    let alphabet_len = table.alphabet.len();
    let states = IdxLut::<State>::from_states(&table.st_actions);

    // Prior to writing the code table, write a jump to a correct entrypoint: initial state at the
    // first argument of the tape. Since the table is stored sequentially (2D array stored as 1D
    // array), index into it as usual: `y * width + x`.
    let init_st = &table.st_actions[0].state;
    let init_st_idx = states.lookup(&init_st.0);
    let first_arg_idx = symbols.lookup(first_arg);
    let cell_idx = init_st_idx * alphabet_len + first_arg_idx;
    let jump_addr = table_start + cell_idx * CELL_SIZE;

    let mut init_jump_cb = CodeBuffer::new(initial_jump_size);

    write_jump(&mut init_jump_cb, jump_addr);
    b.write(init_jump_cb.as_slice());

    for st in &table.st_actions {
        for action in &st.actions {
            let mut cb = CodeBuffer::new(CELL_SIZE);

            write_tape_write(&mut cb, action.symbol);
            write_tape_shift(&mut cb, action.movement);

            match &action.state_tr {
                StateTransition::Accept => write_halt(&mut cb, true),
                StateTransition::Reject => write_halt(&mut cb, false),
                StateTransition::Next(next_st) => {
                    // Since cells of code correspond to a 2D array, full formula of calculating
                    // address into an item at given indices is thus the following (identical to the
                    // initial jump's calculation):
                    //     table_start + (st_idx * alphabet_len + sym_idx) * cell_size
                    // Expanded:
                    //     table_start + st_idx * alphabet_len * cell_size + sym_idx * cell_size
                    // Here it is evident that every part except `sym_idx` is known prior to running
                    // the code, i.e. statically. Therefore, compile in this part of equation into
                    // instructions and add the remaining addend at runtime.
                    let st_idx = states.lookup(next_st);
                    let static_offset = table_start + st_idx * alphabet_len * CELL_SIZE;

                    write_get_symbol_offset(&mut cb);
                    write_jump_with_offset(&mut cb, static_offset);
                }
            }

            b.write(cb.as_slice());
        }
    }
}

fn write_jump(c: &mut CodeBuffer, addr: usize) {
    let jump = func!(
        r#"
        mov rax, 0xdeadbeefcafebabe
        jmp rax
        "#
    );
    let needle = 0xdead_beef_cafe_babe_u64.to_le_bytes();

    let mut copy = copy_code(jump);

    patch_bytes(&mut copy, &needle, &addr.to_le_bytes());

    c.write(&copy);
}

fn copy_code(code: &mut [u8]) -> Vec<u8> {
    let mut copy = vec![0; code.len()];
    copy.copy_from_slice(code);
    copy
}

fn patch_bytes(haystack: &mut [u8], needle: &[u8], patch: &[u8]) {
    assert!(needle.len() == patch.len());

    let mut idx = None;

    for (i, w) in haystack.windows(needle.len()).enumerate() {
        if w == needle {
            idx = Some(i);
            break;
        }
    }

    let idx = idx.unwrap();

    haystack[idx..idx + patch.len()].copy_from_slice(patch);
}

fn write_tape_write(c: &mut CodeBuffer, sym: Symbol) {
    let write_call = func!(
        r#"
        mov di, 0xfe
        mov rax, [rbp - 8]
        call rax
        "#
    );

    let mut copy = copy_code(write_call);

    patch_bytes(&mut copy, &[0xfe], &[sym.0 as u8]);

    c.write(&copy);
}

fn write_tape_shift(c: &mut CodeBuffer, movement: Movement) {
    let shift_call = func!(
        r#"
        mov di, 0xfe
        mov rax, [rbp - 16]
        call rax
        "#
    );

    let mut copy = copy_code(shift_call);

    patch_bytes(&mut copy, &[0xfe], &[movement as u8]);

    c.write(&copy);
}

fn write_halt(c: &mut CodeBuffer, accept: bool) {
    let code_accept = func!(
        r#"
        mov rax, 1
        leave
        ret
        "#
    );

    let code_reject = func!(
        r#"
        mov rax, 0
        leave
        ret
        "#
    );

    let code = if accept { code_accept } else { code_reject };

    c.write(code);
}

fn write_get_symbol_offset(c: &mut CodeBuffer) {
    let call = func!(
        r#"
        mov rax, [rbp - 24]
        call rax
        "#
    );

    c.write(call);
}

fn write_jump_with_offset(c: &mut CodeBuffer, offset: usize) {
    let add_and_jump = func!(
        r#"
        mov rsi, 0xdeadbeefcafebabe
        add rax, rsi
        jmp rax
        "#
    );
    let needle = 0xdead_beef_cafe_babe_u64.to_le_bytes();

    let mut copy = copy_code(add_and_jump);

    patch_bytes(&mut copy, &needle, &offset.to_le_bytes());

    c.write(&copy);
}

fn write_epilogue(b: &mut MappedBuffer) {
    let epilogue = func!(
        r#"
        leave
        ret
        "#
    );

    b.write(epilogue);
}
