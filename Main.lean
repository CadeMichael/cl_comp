import ClComp

open Imp

/-
# test expression showing the modular trigger'
- `trigger` is a function that extracts the value from the Minus / Plus domain after
an operation has been performed
-/
def e₅ : Expr (Plus ⊕ Minus) :=
  x <- trigger' (Minus.sub 7 1);;
  y <- trigger' (Plus.add 2 1);;
  trigger' (Plus.add x y)

def main : IO Unit :=
  IO.println s!"evaluating e₅ gives:\n=> {eval e₅}"
