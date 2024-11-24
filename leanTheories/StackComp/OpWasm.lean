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
```
        Instr := const Z
          | binop

        Binop := add
          | minus
          | mult
          | div

```

- transition relations defined with inference rules to describe the **semantics**
  - defined by `ieval` and `seval`

```
            
                         st = [ x :: y :: sx ]
          ---------------------------------------------------- (binary operation)
             [x :: y :: sx] =[ (binop op) ]=> ([ (op x y) :: sx ])


               --------------------------------------------- (Const)
                      s =[ (Const 10) ] => 10 :: s
```

-/

inductive binop: Type where
  | B_Add
  | B_Minus
  | B_Mult
  | B_Div

inductive inst : Type where
  | Const (i: Int)
  | Binop (op : binop)

def bo_eval (op : binop) (x y : Int) : Int :=
  match op with
  | .B_Add => x + y
  | .B_Minus => x - y
  | .B_Mult => x * y
  | .B_Div => x / y

inductive ieval : inst → stack → stack → Prop where
  | I_Const: forall (n : Int) (s : stack),
    ieval (.Const n) s (n :: s)
  | I_Binop: forall (op : binop) (x y : Int) (s : stack),
    ieval (.Binop op) (x :: y :: s) ((bo_eval op x y) :: s)

-- Determinism of a single evaluation step
theorem ieval_determ {i s s1 s2} (hl : ieval i s s1) (hr: ieval i s s2):
  s1 = s2 :=
  by
    induction hl with
    | I_Const n  s' => cases hr with
      | _ => rfl
    | I_Binop op x y s' => cases hr with
      | _ => rfl

inductive seval : List inst → stack → stack → Prop where
  | NilI s:
    seval [] s s
  | ConsI i is s0 s1 s2:
    ieval i s0 s1 → seval is s1 s2 → seval (i :: is) s0 s2

theorem seval_determ {i s s1 s2} (hl : seval i s s1) (hr : seval i s s2):
  s1 = s2 :=
  by induction hl generalizing s2 with
  | NilI s => cases hr with
    | NilI s => rfl
  | ConsI i'  is' s' s1' s2' heval _hseval ih => cases hr with
    | ConsI i'' is'' s'' s1'' s2'' heval' hseval' =>
      have h1 : s1' = s1'' := by
        apply ieval_determ
        exact heval
        exact heval'
      subst h1
      have h2 : s2' = s2 := ih hseval'
      subst h2
      rfl

theorem stack_ex1:
  seval [(.Const 10), (.Const 80), (.Binop .B_Div)] empty_stack [8] :=
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
