def stack := List Int
def empty_stack : List Int := []

inductive binop: Type :=
  | B_Add
  | B_Minus
  | B_Mult
  | B_Div

inductive inst : Type :=
  | Const (i: Int)
  | Binop (op : binop)

def bo_eval (op : binop) (x y : Int) : Int :=
  match op with
  | .B_Add => x + y
  | .B_Minus => x - y
  | .B_Mult => x * y
  | .B_Div => x / y

inductive ieval : inst → stack → stack → Prop := 
  | I_Const: forall (n : Int) (s : stack),
    ieval (.Const n) s (n :: s)
  | I_Binop: forall (op : binop) (x y : Int) (s : stack),
    ieval (.Binop op) (x :: y :: s) ((bo_eval op x y) :: s)

theorem ieval_determ {i s s1 s2} (hl : ieval i s s1) (hr: ieval i s s2):
  s1 = s2 :=
  by
    induction hl with
    | I_Const n  s' => cases hr with
      | _ => rfl
    | I_Binop op x y s' => cases hr with
      | _ => rfl

  
