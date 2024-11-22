From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import ZArith.

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
        Instr := const Z
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

(* Use ℤ instead of ℕ *)
Open Scope Z_scope.

(**
  ** Definitions of langauge
    - const
    - binary operations
 *)

(* Stack for the language *)
Definition stack := list Z.
Definition empty_stack: (list Z) := [].

(* Binary operations *)
Inductive binop : Type :=
  | B_Add
  | B_Minus
  | B_Mult
  | B_Div
  .

(* Instruction type *)
Inductive inst : Type :=
  | Const (i: Z)
  | Binop (op : binop)
  .

(** 
  ** Definitions of evaluation relations
    - evaluating a signle instruction
    - evaluating a list of instructions
 *)

(* Binary Operation eval, simple and deterministic so it can be a Definition *)
Definition bo_eval (op: binop) (x y : Z) : Z :=
  match op with
  | B_Add => x + y
  | B_Minus => x - y
  | B_Mult => x * y
  | B_Div => x / y
  end.

(* Evaluate a single instruction *)
Inductive ieval : inst -> stack -> stack -> Prop :=
  | I_Const: forall (n : Z) (s : stack),
      ieval (Const n) s (n::s)
  | I_Binop: forall (op : binop) (x y : Z) (s : stack),
      ieval (Binop op) (x :: y :: s) ((bo_eval op x y) :: s)
  .

(* Evaluate a stack of instructions *)
Inductive seval : list inst -> stack -> stack -> Prop :=
  | NilI: forall s, seval [] s s (* No instructions *)
  | ConsI: forall i is s0 s1 s2, (* One or more instructions *)
      ieval i s0 s1 -> seval is s1 s2 -> seval (i :: is) s0 s2
  .

(** 
  ** Proofs of determinism for one instruction and a list of instructions
    - shows that for the execution of the same commands starting with the
      same initial state, will result in the same ending state
 *)

(* Show determinism for the execution of one instruction *)
Theorem ieval_determ : forall i s s1 s2,
  ieval i s s1 -> ieval i s s2 -> s1 = s2.
Proof.
  intros.
  induction H.
  - (* Const *)
    inversion H0. reflexivity.
  - (* Binop *)
    inversion H0. reflexivity.
Qed.

(* The same starting state and commands must result in the same end state *)
Theorem seval_determ:
  forall c s s1 s2,
  (seval c s s1) -> (seval c s s2) -> s1 = s2.
Proof.
  intros.
  generalize dependent s2.
  (* H : seval c s s1 *)
  induction H.
  - (* No instructions c = [] *)
    intros.
    inversion H0. (* H0 : seval [] s s2 *)
    reflexivity.
  - (* List of instructions c = (i :: is) *)
    intros.
    (* IHseval : ∀ s3, seval (i :: is) s0 s3 -> s2 = s3 *)
    inversion H1. (* H1 : seval (i :: is) s0 s3 *)
    subst. 
    assert (s1 = s5).
      (* H  : ieval i s0 s1 *)
      (* H4 : ieval i s0 s5 *)
      {
        apply ieval_determ with (i := i) (s := s0); assumption.
      }
    subst.
    (* IHseval : ∀ s3, seval is s5 s3 -> s2 = s3 *)
    (* H7 : seval is s5 s3 *)
    apply IHseval in H7.
    assumption.
Qed.

(** ** Examples of computations in the stack language *)
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
  seval [(Const 10); (Const 80); (Binop B_Div)] empty_stack [8].
Proof.
  eapply ConsI.
  - apply I_Const.
  - eapply ConsI.
    + apply I_Const.
    + (* stack = [80; 10] *)
      eapply ConsI.
      * apply I_Binop.
      * apply NilI.
Qed.

Example stack_ex2:
  seval [(Binop B_Minus)] [10; 7] [3].
Proof.
  eapply ConsI.
  - apply I_Binop. 
  - apply NilI.
Qed.
  
End StackEvalEx.

Close Scope Z_scope.
