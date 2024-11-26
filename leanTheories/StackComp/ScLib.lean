namespace StackComp

def state : Type :=
  String → Int

def empty_state : state := λ _ => 0

def state.update (x : String) (v : Int) (s : state) : state :=
  λ x' => if x' = x then v else s x'

macro s:term "[" x:term "!->" v:term "]" : term =>
  `(state.update $x $v $s)

#print empty_state

def state_ex := empty_state["x" !-> 10]["y" !-> 5]

#eval (state_ex "x")

end StackComp
