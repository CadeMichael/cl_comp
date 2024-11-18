# CL Wasm Compiler

- Fall 2024 Course project
    - define **operational semantics** for a simple language called "Cade's Language" ie *CL* and the equivalent semantics for *Wasm*.
    - show **determinism** of the semantics
    - write a **compiler** from CL to Wasm
    - capture **behaviors** of source and target language to show **bi-simulation** of *CL* to *Wasm*

## Links

- [wasm docs syntax](https://webassembly.github.io/spec/core/syntax/instructions.html#syntax-instr-numeric)
- [wasm docs instructions](https://webassembly.github.io/spec/core/valid/instructions.html#valid-constant)
- [WasmCert](https://github.com/WasmCert/WasmCert-Coq)
- [coqdocjs](https://github.com/coq-community/coqdocjs)

## Goals

### Semantics

- define operational semantics for the operations I want to perform, must get **1-3**
    1. *constants*
    2. *integer arithmetic*
    3. *sequence*
    4. assignment
    5. if 
    6. while

- show semantics are *deterministic*

### Compiler

- create the wasm compiler
    1. write a function (it will have to be a *Fixpoint* in coq) that compiles CL to Wasm using the semantics
    2. compare **behaviors** of *source language* and *target language*
    3. show the **behaviors** are equivalent ie *bi-simulation*

## Wasm Semantics

## Cl Semantics
