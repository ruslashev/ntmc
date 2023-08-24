Are *you* tired of solving boolean satisfiability problems in exponential time? \**audience boos*\*
Try this brand new Non-deterministic-ish Turing Machine Compiler and solve them in linear time!
(terms and conditions may apply)

FAQ

Q. How?  
A. fork(2)

Q. How is code generation performed?  
A. Code is assembled AOT using Rust's now-stable inline assembly, then patched together
   and rewritten where appropriate, at run time.

   ```rust
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
   ```

   <sup>Do not use this technique in production if you have a family history of heart conditions,
   high blood pressure, or are taking prescription medications without consulting a healthcare
   professional.</sup>

Q. How to run?  
A. Try these:

   ```
   cargo run -- examples/palindrome.ntm -a 1011101 -t
   cargo run -- examples/fork.ntm -a .aaaa.
   cargo run -- examples/cnf_unoptimized.ntm -t -a '. (~0 | 1 | 0) & (0 | 1 | ~0 | 0) & (~1 | 1) .'
   cargo run -- examples/sat.ntm -a '. (a | ~b | c) & (~d | e | ~a) & (b | ~c | d) .'
   ```

Q. Why? Why X, Y?  
A. ...
