From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
(* From Coq Require Import ZArith. *)

(** * Example of ibinop.add in wasm

<<
    (module
        (func (export "_start") (result i32)
        ;; load 10 onto the stack
        i32.const 10
        ;; load 90 onto the stack
        i32.const 90
        i32.const 9
        ;; return the second value (90); the first is discarded
        i32.add
        return
        )
    )
>>

  ** Stack changes during this operation
    - Using E for the evaluation context which is represented by ∊ for empty
      - E₁ = ∊
      - E₂ = [10 :: nil]
      - E₃ = [90 :: 10 :: nil]
      - E₄ = [9 :: 90 :: 10 :: nil]
      - E₅ = [(9 + 90) :: 10 :: nil]

  ** Inference Rules

<< 
        Instr := const nat
          | binop

        Binop := add
          | minus
          | mult

            
                         st = [ x :: y :: sx ]
          ---------------------------------------------------- (binary operation)
             [x :: y :: sx] =[ (binop op) ]=> ([ (op x y) :: sx ])


               --------------------------------------------- (Const)
                      s =[ (Const 10) ] => 10 :: s

>>

 *)
(* Open Scope Z_scope. *)

Definition stack := list nat.
Definition empty_stack: (list nat) := [].

(* Binary operations *)
Inductive binop : Type :=
  | B_Add
  | B_Minus
  | B_Mult
  .

(* Instruction type *)
Inductive inst : Type :=
  | Const (i: nat)
  | Binop (op : binop)
  .

(* Binary Operation eval, simple and deterministic so it can be a Definition *)
Definition bo_eval (op: binop) (x y : nat) : nat :=
  match op with
  | B_Add => x + y
  | B_Minus => x - y
  | B_Mult => x * y
  end.

(* Evaluate a single instruction *)
Inductive ieval : inst -> stack -> stack -> Prop :=
  | I_Const: forall (n : nat) (s : stack),
      ieval (Const n) s (n::s)
  | I_Binop: forall (op : binop) (x y : nat) (s : stack),
      ieval (Binop op) (x :: y :: s) ((bo_eval op x y) :: s)
  .

Theorem ieval_determ : forall i s s1 s2,
  ieval i s s1 -> ieval i s s2 -> s1 = s2.
Proof.
  intros.
  induction H.
  - inversion H0. reflexivity.
  - inversion H0. reflexivity.
Qed.

(* Evaluate a stack of instructions *)
Inductive seval : list inst -> stack -> stack -> Prop :=
  | NilI: forall s, seval [] s s (* No instructions *)
  | ConsI: forall i is s0 s1 s2, (* One or more instructions *)
      ieval i s0 s1 -> seval is s1 s2 -> seval (i :: is) s0 s2
  .

Theorem seval_deterministic:
  forall c s s1 s2,
  (seval c s s1) -> (seval c s s2) -> s1 = s2.
Proof.
  intros.
  generalize dependent s2.
  induction H.
  - intros. inversion H0. reflexivity.
  - intros. inversion H1. subst. 
    assert (s1 = s5).
      {
        apply ieval_determ with (i := i) (s := s0); assumption.
      }
    subst. apply IHseval in H7. assumption.
Qed.

Module StackEvalEx.

Example const_ex1:
  ieval (Const 10) empty_stack [10].
Proof.
  apply I_Const.
Qed.

Example binop_ex1:
  ieval (Binop B_Add) [3;4] [7].
Proof.
  apply I_Binop.
Qed.

Example stack_ex1:
  seval [(Const 10); (Const 8); (Binop B_Mult)] empty_stack [80].
Proof.
  eapply ConsI.
  - apply I_Const.
  - eapply ConsI.
    + apply I_Const.
    + eapply ConsI.
      * apply I_Binop.
      * apply NilI.
Qed.
  
End StackEvalEx.

(* Close Scope Z_scope. *)
