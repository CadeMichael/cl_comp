import StackComp.OpSimp
import StackComp.OpStack
import StackComp.ScLib

namespace StackComp

/-!
Checking imports are working
-- #check inst
-- #check aexp
-- #check binop
-- #check List
-/

def comp_aexp (a : aexp) : (List inst) :=
  match a with
  | .ANum i       => [.Const i]
  | .AId v        => [.Load v]
  | .APlus a1 a2  => (comp_aexp a1) ++ (comp_aexp a2) ++ [(.Binop .B_Add)]
  | .AMinus a1 a2 => (comp_aexp a1) ++ (comp_aexp a2) ++ [(.Binop .B_Minus)]
  | .AMult a1 a2  => (comp_aexp a1) ++ (comp_aexp a2) ++ [(.Binop .B_Mult)]
  | .ADiv a1 a2   => (comp_aexp a1) ++ (comp_aexp a2) ++ [(.Binop .B_Div)]

def comp_com (c : com) : (List inst) := 
  match c with
  | .CAsgn x a  => (comp_aexp a) ++ [.Set x]
  | .CSeq c1 c2 => (comp_com c1) ++ (comp_com c2)

/-! Testing compilation -/
-- #eval comp_aexp (.APlus (.ANum 10) (.AId "x"))
#eval comp_aexp (.ADiv (.ANum 9) (.ANum 3))
#eval aeval empty_state (.ADiv (.ANum 9) (.ANum 3))
-- (.ADiv 80 10)
-- ==> .ADiv a1 a2
-- ==> [const 10, const 80, binop b_div]
-- ==> [const a2, const a1, binop b_div]
-- #eval comp_com (.CAsgn "x" (.APlus (.ANum 10) (.ANum 3)))

theorem seval_append {is1 is2 s1 st1 s2 st2 s3 st3} :
  seval is1 (s1, st1) (s2, st2) →
  seval is2 (s2, st2) (s3, st3) →
  seval (is1 ++ is2) (s1, st1) (s3, st3) :=
  by
    intros h1 h2
    cases h1
    case NilI =>
        exact h2
    case ConsI i is s1' st1' hi hs =>
        apply seval.ConsI
        exact hi
        apply seval_append
        exact hs
        apply h2

/-! Proving stages of compilation correct -/
theorem comp_aexp_cert {a st i}:
  aeval st a = i →
  seval (comp_aexp a) (s, st) (i::s, st) :=
  by
    induction a generalizing i s with
    | ANum i' =>
      intro h
      rw [aeval] at h
      rw [comp_aexp]
      rw [h]
      apply seval.ConsI
      apply ieval.I_Const
      apply seval.NilI
    | AId x =>
      intro h
      rw [aeval] at h
      rw[comp_aexp]
      apply seval.ConsI
      apply ieval.I_Load
      rw [h]
      apply seval.NilI
    | APlus a1 a2 ha1 ha2 =>
      intro h
      rw [aeval] at h
      rw [comp_aexp]
      let i1 := aeval st a1
      let i2 := aeval st a2
      have h1 : aeval st a1 = i1 := rfl
      have h2 : aeval st a2 = i2 := rfl
      rw [h1, h2] at h
      have eval_a2 : seval (comp_aexp a1) (s, st) (i1 :: s, st) := ha1 h1
      have eval_a1 : seval (comp_aexp a2) (i1 :: s, st) (i2 :: i1 :: s, st) := by 
        apply ha2
        apply h2
      have eval_a1_a2 : seval (comp_aexp a1 ++ comp_aexp a2) (s, st) (i2 :: i1 :: s, st) := by
        apply seval_append
        exact eval_a2
        apply eval_a1
      apply seval_append
      exact eval_a1_a2
      apply seval.ConsI
      apply ieval.I_Binop
      rw [←h]
      rw [bo_eval]
      simp
      apply seval.NilI
    | AMinus a1 a2 ha1 ha2 =>
      intro h
      rw [aeval] at h
      rw [comp_aexp]
      let i1 := aeval st a1
      let i2 := aeval st a2
      have h1 : aeval st a1 = i1 := rfl
      have h2 : aeval st a2 = i2 := rfl
      rw [h1, h2] at h
      have eval_a2 : seval (comp_aexp a1) (s, st) (i1 :: s, st) := ha1 h1
      have eval_a1 : seval (comp_aexp a2) (i1 :: s, st) (i2 :: i1 :: s, st) := by 
        apply ha2
        apply h2
      have eval_a1_a2 : seval (comp_aexp a1 ++ comp_aexp a2) (s, st) (i2 :: i1 :: s, st) := by
        apply seval_append
        exact eval_a2
        apply eval_a1
      apply seval_append
      exact eval_a1_a2
      apply seval.ConsI
      apply ieval.I_Binop
      rw [←h]
      rw [bo_eval]
      simp
      apply seval.NilI
    | AMult a1 a2 ha1 ha2 =>
      intro h
      rw [aeval] at h
      rw [comp_aexp]
      let i1 := aeval st a1
      let i2 := aeval st a2
      have h1 : aeval st a1 = i1 := rfl
      have h2 : aeval st a2 = i2 := rfl
      rw [h1, h2] at h
      have eval_a2 : seval (comp_aexp a1) (s, st) (i1 :: s, st) := ha1 h1
      have eval_a1 : seval (comp_aexp a2) (i1 :: s, st) (i2 :: i1 :: s, st) := by 
        apply ha2
        apply h2
      have eval_a1_a2 : seval (comp_aexp a1 ++ comp_aexp a2) (s, st) (i2 :: i1 :: s, st) := by
        apply seval_append
        exact eval_a2
        apply eval_a1
      apply seval_append
      exact eval_a1_a2
      apply seval.ConsI
      apply ieval.I_Binop
      rw [←h]
      rw [bo_eval]
      simp
      apply seval.NilI
    | ADiv a1 a2 ha1 ha2 =>
      intro h
      rw [aeval] at h
      rw [comp_aexp]
      let i1 := aeval st a1
      let i2 := aeval st a2
      have h1 : aeval st a1 = i1 := rfl
      have h2 : aeval st a2 = i2 := rfl
      rw [h1, h2] at h
      have eval_a2 : seval (comp_aexp a1) (s, st) (i1 :: s, st) := ha1 h1
      have eval_a1 : seval (comp_aexp a2) (i1 :: s, st) (i2 :: i1 :: s, st) := by 
        apply ha2
        apply h2
      have eval_a1_a2 : seval (comp_aexp a1 ++ comp_aexp a2) (s, st) (i2 :: i1 :: s, st) := by
        apply seval_append
        exact eval_a2
        apply eval_a1
      apply seval_append
      exact eval_a1_a2
      apply seval.ConsI
      apply ieval.I_Binop
      rw [←h]
      rw [bo_eval]
      simp
      apply seval.NilI

theorem comp_state_cert {c s st st1 st2}
  (hl : ceval c st st1)
  (hr : seval (comp_com c) (empty_stack, st) (s, st2)):
  st1 = st2 :=
  by
    sorry

end StackComp
