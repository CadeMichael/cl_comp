(**
  * Example of ibinop.add in wasm

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
            -------------------------------- (const)
              C ⊢ i32.const c: [] -> [i32]

            ---------------------------------------- (binary operation)
              C ⊢ i32.binop c: [i32 i32] -> [i32]

>>

 *)

Module OpWasm.

Definition c := 10.
Check 1.

End OpWasm.
