namespace StackComp

/-! 
# State
- for both SIMP and Stack state is defined as a function from a string to an int
  - in essence this is a **total map**
  - we map strings to integer values
- we explicitly define `state` and `empty_state`
- we create custom notation for updating the *state map*
  - `∀ (st : state) (v : String) (x : Int), st[v !-> x]`
-/

/-! Define state -/
def state : Type :=
  String → Int

/-! Define emtpy state -/
def empty_state : state := λ _ => 0

/-! Provide a mechanism to update state -/
def state.update (x : String) (v : Int) (s : state) : state :=
  λ x' => if x' = x then v else s x'

/-! Create custom notation for updating state -/
macro s:term "[" x:term "!->" v:term "]" : term =>
  `(state.update $x $v $s)

#print empty_state

def state_ex := empty_state["x" !-> 10]["y" !-> 5]

#eval (state_ex "x")

end StackComp
