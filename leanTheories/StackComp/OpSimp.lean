import StackComp.ScLib
/-!
# Simple Language
- This will be the language that compiles to the simple stack language
- it will at the very least have integer arithmetic

## Syntax via BNF

```
aexp := i
  | i + i
  | i - i
  | i * i
  | i / i
```

## Semantics via Transition Relationships

```

            ------------------------- (ANum)
                  ANum i ==> i
                  

                    e1 ==> i1
                    e2 ==> i2
            ------------------------- (APlus)
              APlus e1 e2 ==> i1 + i2 


                    e1 ==> i1
                    e2 ==> i2
            ------------------------- (APlus)
              APlus e1 e2 ==> i1 + i2 


                    e1 ==> i1
                    e2 ==> i2
            -------------------------- (AMinus)
             AMinus e1 e2 ==> i1 - i2 


                    e1 ==> i1
                    e2 ==> i2
            ------------------------- (AMult)
              AMult e1 e2 ==> i1 * i2 


                    e1 ==> i1
                    e2 ==> i2
            ------------------------- (ADiv)
              ADiv e1 e2 ==> i1 / i2 
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

inductive aexp: Type where
  | ANum (i : Int)
  | AId (x : String)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp)

-- def aeval ()

/-!
# Defining how arithmetic is evaluated with a Relation
- this can be easier to extend with new operations but especially in lean is much more
  stubborn. by this I mean we can't simplify an expression down to an ending state of i3
  if `i3 = i1 op i2` we must write `i1 op i2`.
- this added flexibilility in this case is not needed and only adds some complexity
- I am showing it as a case study and possible second route for defining Simp
-/
inductive aevalR: aexp -> Int -> Prop :=
  | E_ANum (i : Int) : aevalR (.ANum i) i
  | E_APlus (e1 e2 : aexp) :
    (aevalR e1 i1) →
    (aevalR e2 i2) →
    aevalR (.APlus e1 e2) (i1 + i2)
  | E_AMinus (e1 e2 : aexp) :
    (aevalR e1 i1) →
    (aevalR e2 i2) →
    aevalR (.AMinus e1 e2) (i1 - i2)
  | E_AMult (e1 e2 : aexp) :
    (aevalR e1 i1) →
    (aevalR e2 i2) →
    aevalR (.AMult e1 e2) (i1 * i2)
  | E_ADiv (e1 e2 : aexp) :
    (aevalR e1 i1) →
    (aevalR e2 i2) →
    aevalR (.ADiv e1 e2) (i1 / i2)

theorem aevalR_ex1:
  aevalR (aexp.AMult (aexp.ANum 10) (aexp.ANum 5)) (10 * 5) :=
  by
    apply aevalR.E_AMult
    { apply aevalR.E_ANum }
    { apply aevalR.E_ANum }

end StackComp
