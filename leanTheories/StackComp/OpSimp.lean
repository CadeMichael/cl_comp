import StackComp.ScLib

/-!
# Simple Language
- This will be the language that compiles to the simple stack language
- it will at the very least have integer arithmetic and assignment

## Syntax via BNF for arithmetic

```
aexp := i
  | i + i
  | i - i
  | i * i
  | i / i
```

## Semantics via Transition Relationships for arithmetic

```

            ------------------------- (ANum)
                  ANum i ==> i


                     st x = v
            ------------------------- (AId)
                   AId x ==> v
                  

                    a1 ==> i1
                    a2 ==> i2
            ------------------------- (APlus)
              APlus a1 a2 ==> i1 + i2 


                    a1 ==> i1
                    a2 ==> i2
            ------------------------- (APlus)
              APlus a1 a2 ==> i1 + i2 


                    a1 ==> i1
                    a2 ==> i2
            -------------------------- (AMinus)
             AMinus a1 a2 ==> i1 - i2 


                    a1 ==> i1
                    a2 ==> i2
            ------------------------- (AMult)
              AMult a1 a2 ==> i1 * i2 


                    a1 ==> i1
                    a2 ==> i2
            ------------------------- (ADiv)
              ADiv a1 a2 ==> i1 / i2 
```

## level of embedding
- with lean we don't have to define our simple arithmetic syntax and evaluation
  - we can use a **shallow** embedding, this means that we pass the burden of these
    operations to the top level language or the language being used to define Simp
  - or we can use **deep** embedding where we specify the way arithmetic should be
    handled. For the most detailed specifications of Simp I believe that deep fits this purpose better

## State
- State is represented as a function from a `String` to an `Integer`
- it can be updated by creating a new function that returns a new int for a new string input
-/

namespace StackComp

/-! aexp holds the types of expressions that interact with ints -/
inductive aexp : Type where
  | ANum   (i : Int)
  | AId    (x : String)
  | APlus  (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult  (a1 a2 : aexp)
  | ADiv   (a1 a2 : aexp)

/-!
# Defining how arithmetic is evaluated with a Relation
- this can be easier to extend with new operations but especially in lean is much more
  stubborn. by this I mean we can't simplify an expression down to an ending state of i3
  if `i3 = i1 op i2` we must write `i1 op i2`.
- this added flexibilility in this case is not needed and only adds some complexity
- I am showing it as a case study and possible second route for defining Simp
-/
inductive aevalR: aexp → state → Int → Prop :=
  | E_ANum  (i : Int) (st : state): aevalR (.ANum i) st i
  | E_AId   (x : String) (st : state): aevalR (.AId x) st (st x)
  | E_APlus (a1 a2 : aexp) (st : state):
    (aevalR a1 st i1) →
    (aevalR a2 st i2) →
    aevalR (.APlus a1 a2) st (i1 + i2)
  | E_AMinus (a1 a2 : aexp) (st : state):
    (aevalR a1 st i1) →
    (aevalR a2 st i2) →
    aevalR (.AMinus a1 a2) st (i1 - i2)
  | E_AMult (a1 a2 : aexp) (st : state):
    (aevalR a1 st i1) →
    (aevalR a2 st i2) →
    aevalR (.AMult a1 a2) st (i1 * i2)
  | E_ADiv (a1 a2 : aexp) (st : state):
    (aevalR a1 st i1) →
    (aevalR a2 st i2) →
    aevalR (.ADiv a1 a2) st (i1 / i2)

theorem aevalR_ex1:
  aevalR (aexp.AMult (aexp.ANum 10) (aexp.ANum 5)) empty_state (10 * 5) :=
  by
    apply aevalR.E_AMult
    { apply aevalR.E_ANum }
    { apply aevalR.E_ANum }

/-! 
# Defining how arithmetic is evaluated with a function
- the benefits of this is we have determinism by virtue of aevel being a function
- we have a cleaner syntax for showing examples of evaluation
-/
def aeval (st : state) (a : aexp) : Int :=
  match a with
  | .ANum i       => i
  | .AId x        => st x
  | .APlus a1 a2  => (aeval st a1) + (aeval st a2)
  | .AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | .AMult a1 a2  => (aeval st a1) * (aeval st a2)
  | .ADiv a1 a2   => (aeval st a1) / (aeval st a2)

/-!
## Examples of evaluation
- simple arithmetic
- getting values from state
-/
#eval aeval empty_state (.APlus (.ANum 5) (.ANum 5))
#eval aeval (empty_state["x" !-> 11]) (.AMult (.AId "x") (.ANum 5))

/-! 
# Defining rules for big step evaluation of SIMP
- to define evaluation we will use an *inductive* definition to describe how different
  commands `com` are evaluated.

## BNF for SIMP

- we have two types of primitive commands
  - assignment, denoted with `:=`
  - sequencing, denoted with `;`

```
com := x := a
  | c ; c
```

## Semantics of SIMP

```
                   aeval st a = n
            ---------------------------- (C_Asgn)
             st =[x := a]=> st[x !-> n]


                   st =[c1]=> st'
                  st' =[c1]=> st''
            ------------------------- (C_Seq)
                st =[c1 ; c2]=> st''
```
-/

/-! Defining the semantics of SIMP -/
inductive com : Type where
  | CAsgn (x : String) (a : aexp)
  | CSeq  (c1 c2 : com)

/-! Defining the Semantics of SIMP -/
inductive ceval : com → state → state → Prop where
  | C_Asgn : ∀ st a i x,
    aeval st a = i → ceval (.CAsgn x a) st (st[x !-> i])
  | C_Seq : ∀ c1 c2 st st' st'',
    ceval c1 st st' → ceval c2 st' st'' →
    ceval (.CSeq c1 c2) st st''

/-! Proving that evaluation of SIMP is determinism -/
theorem ceval_determ {c st st1 st2}
  (hl : ceval c st st1)
  (hr : ceval c st st2):
  st1 = st2 :=
  by induction hl generalizing st2 with
  | C_Asgn st' a i x ha =>
    cases hr
    case C_Asgn i' ha' =>
      have hi: i = i' := by
        rw [←ha, ←ha']
      subst hi
      rfl
  | C_Seq c1 c2 st' st1' st2' _ec1 _ec2 hc hc' =>
    cases hr 
    case C_Seq st'' hc1 hc1' =>
      have h1 : st1' = st'' := by
        apply hc
        exact hc1
      apply hc'
      rw [h1]
      exact hc1'

end StackComp
