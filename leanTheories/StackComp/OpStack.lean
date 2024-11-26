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

-/

namespace StackComp

inductive binop: Type where
  | B_Add
  | B_Minus
  | B_Mult
  | B_Div

inductive inst : Type where
  | Const (i: Int)
  | Binop (op : binop)
  | Set   (v : String)
  | Load  (v : String)

def bo_eval (op : binop) (x y : Int) : Int :=
  match op with
  | .B_Add    => x + y
  | .B_Minus  => x - y
  | .B_Mult   => x * y
  | .B_Div    => x / y

inductive ieval : inst → (stack × state) → (stack × state) → Prop where
  | I_Const: forall (n : Int) (s : stack) (st : state),
    ieval (.Const n) (s, st) ((n :: s), st)
  | I_Binop: forall (op : binop) (x y : Int) (s : stack) (st : state),
    ieval (.Binop op) ((x :: y :: s), st) (((bo_eval op x y) :: s), st)
  | I_Set: forall (v : String) (x : Int) (s : stack) (st : state),
    ieval (.Set v) ((x :: s), st) (s, st[v !-> x])
  | I_Load : forall (v : String) (x : Int) (s : stack) (st : state),
    st v = x → ieval (.Load v) (s, st) ((x :: s), st)

-- Determinism of a single evaluation step
theorem ieval_determ {i s s1 s2 st st1 st2} (hl : ieval i (s, st) (s1, st1)) (hr: ieval i (s, st) (s2, st2)):
  s1 = s2 ∧ st1 = st2:=
  by
    cases hl
    case I_Const n =>
      cases hr
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
        rw [←h, h']
        repeat (any_goals (first | constructor | rfl))
      
inductive seval : List inst → (stack × state) → (stack × state) → Prop where
  | NilI s:
    seval [] s s
  | ConsI i is s s1 s2 st st1 st2:
    ieval i (s, st) (s1, st1) →
    seval is (s1, st1) (s2, st2) →
    seval (i :: is) (s, st) (s2, st2)

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

theorem stack_ex1:
  seval [(.Const 10), (.Const 80), (.Binop .B_Div)] (empty_stack, empty_state) ([8], empty_state) :=
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
