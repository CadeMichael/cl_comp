# Project Proposal
## verified WASM compiler
- My project goal (the moon in the analogy of shooting for the moon) idea entails creating a C-like language (CL) with a few features by creating a
compiler that takes the source code of my language and outputs WASM.
    - The features of the language will include: variables, assignments, pointers, while loops, function calls, and pointers.
- To accomplish this task I will be using a proof assistant programming language such as Coq or Lean4.
    - My goal is to use Lean4 as it is more modern and has a good amount of inertia in Academia at this time.
    - It appears to be more performant and designed for larger scale projects, making this project one that could grow and continue after submission and possibly lead to future research.
    - If the support and resources for Lean4 are inadequate I will default to using Coq as it is the standard in PL. The main tasks for the project entail defining the operational semantics for the CL language using the functional capabilities of the proof assistant that I am using. Then I will need to formalize the equivalent JVM instructions, needed for all of the functionality of my language. I will then use the chosen proof assistant to create a compiler from CL to JVM bytecode. Once this is completed I will use the proof capabilities of my chosen language to prove the correctness of my compiler. At the very least I will need to show the bi-simulation of source CL to target JVM bytecode. If I can accomplish all of this I will try adding optimizations to the compiler and proving their soundness. I will start by formalizing each language and defining their operational semantics. I will then create a parser to handle source code CL files. Then I will work on creating a compiler to create runnable bytecode files. I will use CompCert (https://compcert.org/) for inspiration. It is a verified C compiler written in Coq.
# Defining semantics
## start with simple plus language (Pexpr)
- write a `peval`
- assume everything is 32bit
- start with few instructions
### swap
- swap two integers
```
x = x + y
x = x - y
x = x - y
```
## wasm
- write corresponding wasm program
    - will give you a series of programs
    - define `weval` relation how to evaluate simple wasm program
    - write a compilation procedure that compares it down to a wasm program (will have to be a Fixpoint program)
## state
- in wasm state is represented by a FIFO stack and elements cannot be referenced by index
- for instance if the stack is (left is most recently added)
    - `1::2::3::4::nil`
    - and `ibinop add` is called the next value is `3` (1 + 2)
