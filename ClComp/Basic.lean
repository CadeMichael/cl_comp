namespace Imp

/-
# test expression showing the modular trigger'
- `trigger` is a function that extracts the value from the Minus / Plus domain after
an operation has been performed
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

