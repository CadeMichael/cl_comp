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

### old code
```lean
namespace Imp

/-!
# Expr represents expressions
- val is a value (computation is done)
- do represents another operation which is paired with a continuation k
- this allows modular building of our language
-/
inductive Expr (Op : Type) :=
  | Val (n : Nat) -- Identity Function
  | Do (op : Op) (k : Nat → Expr Op) -- Continuation kindof like '>>='

open Expr

inductive Plus :=
  | add (n₁ n₂ : Nat)

open Plus

inductive Minus :=
  | sub (n₁ n₂ : Nat)

open Minus

/-- fold acts as the *visitor* pattern in imperative interpreters -/
def fold_eval {Op} (h : Op → Nat) (t : Expr Op) : Nat :=
  match t with
  | Val n => n
  | Do op k => fold_eval h (k (h op))

def e : Expr Plus := Do (add 3 4) (λ n => Val n)

def hplus : Plus → Nat :=
  λ (add n₁ n₂) => n₁ + n₂ 

def hminus : Minus → Nat :=
  λ (sub n₁ n₂) => n₁ - n₂

def evalp := fold_eval hplus

#eval evalp e

def seq {Op} (e : Expr Op) (k : Nat → Expr Op) : Expr Op :=
  match e with
  | Val n => k n
  | Do op h => Do op (λ n => seq (h n) k)

notation:max x "<-" t1 ";;" t2 => seq t1 (λ x => t2)

def trigger {Op} (op : Op) : Expr Op :=
  Do op (λ x => Val x)

def e₁ : Expr Plus :=
  trigger (add 3 5)

#eval evalp e₁

def e₂ : Expr Plus :=
  x <- trigger (add 1 2);;
  y <- trigger (add 3 4);;
  trigger (add x y)

#eval evalp e₂

def handler_sum {Op₁ Op₂} (h₁ : Op₁ → Nat) (h₂ : Op₂ → Nat)
  : Op₁ ⊕ Op₂ → Nat :=
  λ op => match op with
    | .inl op => h₁ op
    | .inr op => h₂ op

notation:10 h₁ "+'" h₂ => handler_sum h₁ h₂

def eval := fold_eval (hplus +' hminus)

def e₃ : Expr (Plus ⊕ Minus) :=
  x <- trigger (.inr (sub 2 1));;
  y <- trigger (.inr (sub 6 3));;
  trigger (.inl (add x y))

#eval eval e₃

class Subop (Op₁ Op₂ : Type) where
  inject : Op₁ → Op₂

open Subop

instance subop_refl (Op : Type) : Subop Op Op where
  inject := λ x => x -- this is the id function


instance subop_left (Op1 Op2 : Type) : Subop Op1 (Op1 ⊕ Op2) where
  inject := .inl

instance subop_right (Op1 Op2 Op3 : Type) [Subop Op1 Op3]
  : Subop Op1 (Op2 ⊕ Op3) where
  inject := λ e => .inr (inject e)

notation:max "trigger'" e => trigger (inject e)

def e₄ : Expr (Plus ⊕ Minus) :=
  x <- trigger' (sub 7 1);;
  y <- trigger' (add 2 1);;
  trigger' (sub x y)

#eval eval e₄

end Imp
```
```lean
namespace Wasm

open List
open Int

/-
inductive State :=
  | nil : State
  | cons : Int → List Int → State

infix:67 " :: " => State.cons

def State.pop (s : State) : State :=
  match s with
  | State.nil => State.nil
  | h :: t => t
-/

def State : Type := List Int

def State.pop (s : State) : Option (Int × State) :=
  match s with
  | [] => none
  | h :: t => some (h, t) -- (value, state')

def State.push (val : Int) (s : State) : State :=
  val :: s -- state'

-- Prop <--> Bool
-- proposition is that the state is of length ≥ 2 -> iadd
inductive WPlus : Type :=
  | iconst (v : Int) --: State → Int → WPlus
  | iadd : WPlus --State → WPlus
  -- | Wtrap : fail
  -- | ret : (s : State) → Int

/-!
# Notes
- need to figure out how to represent commands and values
- everything is based on `State`
  - is `List Int` the best way of thinking of state
  - how do you define an inductive type that relies on state?
## Wasm Instructions Include
- **ibinop**
  - these aren't binary in the sense that the constructor is passed two arguments
  - constructor is passed a state of at least `len ≥ 2` or at least needs this state
  - in wasm no arguments are passed
- **const**
  - recieves one argument which is the int to be pushed onto the stack

## Representing as inductively defined types
- how can these instructions be defined inductively?
  - maybe something like dependent types
  - `  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt`
- I am not trying to create an interpreter in the concrete sense but define rules
  for reasoning about wasm programs. The actual values returned doesn't matter but
  I need rules to compare to a simple 'Plus' language.

# Figure out what properties you want to prove
- build from the bottom up, don't get lost in the details.
- have a story, related works, proof of concept
- what is the point?
  - if you want to talk about concurrency / non determinism you need small step
  - what is the 'real meaning' of a semantics
    - need to normalize to some common language
  - denotational -> compiler
  - operational -> interpreter
1. say lang A and B are equivalent in some form
  - some simulation relation between them
  - **coq-hammer** ?
-/

-- Fixpoint : Prop 
-- inductive (...) : Prop
def eval (s : State) (c : WPlus): State :=
  match c with
  | WPlus.iconst v => s.push v
  | WPlus.iadd =>  match s.pop with
    | none => []
    | some (n1, s') => match s'.pop with
      | none => []
      | some (n2, s'') => s''.push (n1 + n2)

-- inductive eval : WPlus → State → State → Prop :=
  -- | iconst 

def s : State := []
def s1 : State := eval s (WPlus.iconst 10)
def s2 : State := eval s1 (WPlus.iconst 11)
def s3 : State := eval s2 (WPlus.iconst 5)
def s4 : State := eval s3 (WPlus.iadd)

#eval s1 
#eval s2 
#eval s3 
#eval s4 

end Wasm
```
