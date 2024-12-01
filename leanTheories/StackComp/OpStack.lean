import StackComp.ScLib

/-!
## Defining variables for the evaluation context
- stack defines the list of values in the programs scopes
-/
def stack := List Int
def empty_stack : List Int := []

/-!
# Defining operations for execution
- **inst** represents instructions, as of right now they can be
  - binary operations
  - pushing constant values onto the stack

## BNF notation and inference rules

- Backus Naur Form to describe the **syntax**
  - defined by `binop` and `inst`
  - to manage state we have a *total map* that holds the integer values associated
    with a string representing a variable
    - we can *load* and *set* values from this map by pushing and popping from the stack

```
        Instr := const Z
          | binop
          | load String
          | set String

        Binop := add
          | minus
          | mult
          | div

```

- transition relations defined with inference rules to describe the **semantics**
  - defined by `ieval` and `seval`

```
s  := stack
st := state
            
                         s = [ x :: y :: sx ]
         --------------------------------------------------------- (binary operation)
          ([x :: y :: sx], st) =[binop op]=> ((op x y) :: sx, st)


                         s = [ x :: sx ]   v : String
          ---------------------------------------------------- (set operation)
             ([x :: sx], st) =[set v]=> ([sx], st[v !-> x])


                          s : stack    st v = x
          ---------------------------------------------------- (load operation)
                   (s, st) =[load v]=> ((x :: s), st)


                                  x : Int
               --------------------------------------------- (Const)
                    (s, st) =[Const x] => ((x :: s), st)
```

## Proving Determinism

- for our stack language we will prove that every sequence of instructions executed
  with the same starting stack and state, will result in the same end stack and end state.
- to accomplish this like with defining the *evaluation relation* we show the determinism
  of one instruction `ieval` and then use this theory to prove that executing a sequence
  of instructions (`List instr`) is also deterministic

-/

namespace StackComp

/-! Define all binary operations -/
inductive binop : Type where
  | B_Add
  | B_Minus
  | B_Mult
  | B_Div

/-! Define all instructions -/
inductive inst : Type where
  | Const (i: Int)
  | Binop (op : binop)
  | Set   (v : String)
  | Load  (v : String)

instance : Repr binop where
  reprPrec
    | .B_Add, _ => "B_Add"
    | .B_Minus, _ => "B_Minus"
    | .B_Mult, _ => "B_Mult"
    | .B_Div, _ => "B_Div"

instance : Repr inst where
  reprPrec
    | .Const i, _ => "(Const " ++ repr i ++ ")"
    | .Binop op, _ => "(Binop " ++ repr op ++ ")"
    | .Set v, _ => "(Set " ++ repr v ++ ")"
    | .Load v, _ => "(Load " ++ repr v ++ ")"

/-! Evaluation function for binary operations -/
def bo_eval (op : binop) (x y : Int) : Int :=
  match op with
  | .B_Add    => x + y
  | .B_Minus  => x - y
  | .B_Mult   => x * y
  | .B_Div    => x / y

/-! Evaluation relation for a single instruction -/
inductive ieval : inst → (stack × state) → (stack × state) → Prop where
  | I_Const: ∀ (n : Int) (s : stack) (st : state),
    ieval (.Const n) (s, st) ((n :: s), st)
  | I_Binop: ∀ (op : binop) (x y : Int) (s : stack) (st : state),
    ieval (.Binop op) ((y :: x :: s), st) (((bo_eval op x y) :: s), st)
  | I_Set: ∀ (v : String) (x : Int) (s : stack) (st : state),
    ieval (.Set v) ((x :: s), st) (s, st[v !-> x])
  | I_Load : ∀ (v : String) (x : Int) (s : stack) (st : state),
    st v = x → ieval (.Load v) (s, st) ((x :: s), st)

/-! Show that the execution of one instruction is deterministic -/
theorem ieval_determ {i s s1 s2 st st1 st2}
  (hl : ieval i (s, st) (s1, st1))
  (hr: ieval i (s, st) (s2, st2)):
  s1 = s2 ∧ st1 = st2 :=
  by
    -- iterate over all possible instructions instruction
    cases hl
    case I_Const n =>
      cases hr
      -- break apart the ∧ and solve both sides
      repeat (any_goals (first | constructor | rfl))
    case I_Binop op x y s' =>
      cases hr
      repeat (any_goals (first | constructor | rfl))
    case I_Set v x =>
      cases hr
      repeat (any_goals (first | constructor | rfl))
    case I_Load v x h =>
      cases hr
      case I_Load x' h' =>
        -- h  : st v = x
        -- h' : st v = x'
        -- ⊢ ((x :: s) = (x' :: s)) ∧ st = st
        rw [←h, h']
        repeat (any_goals (first | constructor | rfl))
      
/-! Evaluation relation for a list of instructions -/
inductive seval : List inst → (stack × state) → (stack × state) → Prop where
  | NilI s:
    seval [] s s
  | ConsI i is s s1 s2 st st1 st2:
    ieval i (s, st) (s1, st1) →
    seval is (s1, st1) (s2, st2) →
    seval (i :: is) (s, st) (s2, st2)

/-! Show that executing a sequence of instructions is deterministic -/
theorem seval_determ {i s s1 s2 st st1 st2}
  (hl : seval i (s, st) (s1, st1))
  (hr : seval i (s, st) (s2, st2)):
  s1 = s2 ∧ st1 = st2 :=
  by
    cases hl
    case NilI =>
      cases hr
      case NilI =>
        exact ⟨rfl, rfl⟩
    case ConsI i is s1' st1' hi hs =>
      cases hr
      case ConsI s'' st1'' hi' hs' =>
        have h1 : s1' = s'' ∧ st1' = st1'' := by
          apply ieval_determ
          exact hi
          exact hi'
        let ⟨h1l, h1r⟩ := h1
        subst h1r
        subst h1l
        apply seval_determ
        exact hs
        exact hs'

/-!
An example of executing a sequence of instructions

```
(module
    (func (export "_start") (result i32)
    ;; load 80 onto the stack
    i32.const 80
    ;; load 10 onto the stack
    i32.const 10
    ;; divide
    i32.div_u
    return
    )
)
```
-/
theorem stack_ex1:
  seval [(.Const 80), (.Const 10), (.Binop .B_Div)] (empty_stack, empty_state) ([8], empty_state) :=
  by
    apply seval.ConsI
    { apply ieval.I_Const }
    apply seval.ConsI
    { apply ieval.I_Const }
    apply seval.ConsI
    { apply ieval.I_Binop }
    have h: (bo_eval .B_Div 80 10) = 8 :=
      by
      unfold bo_eval
      simp
    rw [h]
    apply seval.NilI

end StackComp
