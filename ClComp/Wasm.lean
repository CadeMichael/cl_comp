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
