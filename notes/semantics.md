# Defining semantics

# start with simple plus

- write a `peval`
- assume everything is 32bit
- start with few instructions

## swap

- swap two integers

```
x = x + y
x = x - y
x = x - y
```

# wasm
- write corresponding wasm program
    - will give you a series of programs
    - define `weval` relation how to evaluate simple wasm program
    - write a compilation procedure that compares it down to a wasm program (will have to be a Fixpoint program)

## state

- in wasm state is represented by a LIFO stack and elements cannot be referenced by index
- for instance if the stack is (left is most recently added)
    - `1::2::3::4::nil`
    - and *ibinop add* is called the next value is `3` (1 + 2)
