# CL Wasm Compiler

- Fall 2024 Course project
    - define **operational semantics** for a simple language called "Cade's Language" ie *CL* and the equivalent semantics for *Wasm*.
    - show **determinism** of the semantics
    - write a **compiler** from CL to Wasm
    - capture **behaviors** of source and target language to show **bi-simulation** of *CL* to *Wasm*

## Links

- [wasm docs syntax](https://webassembly.github.io/spec/core/syntax/instructions.html#syntax-instr-numeric)
- [wasm docs instructions](https://webassembly.github.io/spec/core/valid/instructions.html#valid-constant)
- [WasmCert](https://github.com/WasmCert/WasmCert-Coq)
- [coqdocjs](https://github.com/coq-community/coqdocjs)

## Goals

### Semantics

- define operational semantics for the operations I want to perform, must get **1-3**
    1. *constants*
    2. *integer arithmetic*
    3. *sequence*
    4. assignment
    5. if 
    6. while

- show semantics are *deterministic*

### Compiler

- create the wasm compiler
    1. write a function (it will have to be a *Fixpoint* in coq) that compiles CL to Wasm using the semantics
    2. compare **behaviors** of *source language* and *target language*
    3. show the **behaviors** are equivalent ie *bi-simulation*

## Wasm Semantics

### WasmCert-Coq Notes

- contexts.v:19 _eval context type class_
```coq
(* 19 *)
(* Typeclass for a Wasm evaluation context.
   ctx_frame_mask and ctx_frame_cond are auxiliary functions for defining
   the ctx_reduce relation, which instructs on how reductions of instructions
   within the hole could affect the configuration on the outer context (well, in
   principle they shouldn't do so in a normal language, but the frame reduction
   rule necessitates such a practice here).
*)
Class eval_ctx (ctx_t: Type): Type :=
  {
    ctx_fill: list administrative_instruction -> ctx_t -> list administrative_instruction;
    ctx_frame_mask: ctx_t -> frame -> frame;
    ctx_frame_cond: ctx_t -> frame -> frame -> Prop;
    ctx_reduce: forall (ctx: ctx_t) hs s f es hs' s' f' es',
      ctx_frame_cond ctx f f' ->
      reduce hs s (ctx_frame_mask ctx f) es hs' s' (ctx_frame_mask ctx f') es' ->
      reduce hs s f (ctx_fill es ctx) hs' s' f' (ctx_fill es' ctx);
  }.

(* 826 *)
Record t_context : Set := {
  tc_types : list function_type;
  tc_funcs : list function_type;
  tc_tables : list table_type;
  tc_mems : list memory_type;
  tc_globals : list global_type;
  tc_elems : list reference_type;
  tc_datas : list ok;
  tc_locals : list value_type;
  tc_labels : list result_type;
  tc_return : option result_type;
  tc_refs : list funcidx;
}.
```

- datatypes.v:1066 _administrative instructions_
```coq
Inductive administrative_instruction : Type := (* e *)
| AI_basic : basic_instruction -> administrative_instruction
| AI_trap
| AI_ref : funcaddr -> administrative_instruction
| AI_ref_extern: externaddr -> administrative_instruction
| AI_invoke : funcaddr -> administrative_instruction
| AI_label : nat -> list administrative_instruction -> list administrative_instruction -> administrative_instruction
| AI_frame : nat -> frame -> list administrative_instruction -> administrative_instruction
.
```

- datatypes.v:104 _number types & values_ (values:637)
```coq
Inductive number_type : Set := 
  | T_i32
  | T_i64
  | T_f32
  | T_f64
  .

Inductive value : Type :=
| VAL_num: value_num -> value
| VAL_vec: value_vec -> value
| VAL_ref: value_ref -> value
.
```

- datatypes.v:348 _unary and binary operations_
```coq
Inductive sx : Set :=
  | SX_S
  | SX_U
  .

Inductive unop_i : Set :=
  | UOI_clz
  | UOI_ctz
  | UOI_popcnt
  .

Inductive unop_f : Set :=
  | UOF_abs
  | UOF_neg
  | UOF_sqrt
  | UOF_ceil
  | UOF_floor
  | UOF_trunc
  | UOF_nearest
  .

Inductive unop : Set :=
  | Unop_i : unop_i -> unop
  | Unop_f : unop_f -> unop
  | Unop_extend : N -> unop
  .

Inductive binop_i : Set :=
  | BOI_add
  | BOI_sub
  | BOI_mul
  | BOI_div : sx -> binop_i
  | BOI_rem : sx -> binop_i
  | BOI_and
  | BOI_or
  | BOI_xor
  | BOI_shl
  | BOI_shr : sx -> binop_i
  | BOI_rotl
  | BOI_rotr
  .

Inductive binop_f : Set :=
  | BOF_add
  | BOF_sub
  | BOF_mul
  | BOF_div
  | BOF_min
  | BOF_max
  | BOF_copysign
  .

Inductive binop : Set :=
  | Binop_i : binop_i -> binop
  | Binop_f : binop_f -> binop
  .
```

- datatypes.v:518 _basic instructions_
```coq
Inductive basic_instruction : Type := (* be *)
(** std-doc:
Numeric instructions provide basic operations over numeric values of specific type. These operations closely match respective operations available in hardware.
 **)
  | BI_const_num : value_num -> basic_instruction
  | BI_unop : number_type -> unop -> basic_instruction
  | BI_binop : number_type -> binop -> basic_instruction
  | BI_testop : number_type -> testop -> basic_instruction
  | BI_relop : number_type -> relop -> basic_instruction
  | BI_cvtop : number_type -> cvtop -> number_type -> option sx -> basic_instruction
(** std-doc: (not implemented yet)
Vector instructions (also known as SIMD instructions, single data multiple value) provide basic operations over values of vector type.
Vector instructions can be grouped into several subcategories:

Constants: return a static constant.
Unary Operations: consume one v128 operand and produce one v128 result.
Binary Operations: consume two v128 operands and produce one v128 result.
Ternary Operations: consume three v128 operands and produce one v128 result.
Tests: consume one v128 operand and produce a Boolean integer result.
Shifts: consume a v128 operand and a i32 operand, producing one v128 result.
Splats: consume a value of numeric type and produce a v128 result of a specified shape.
Extract lanes: consume a v128 operand and return the numeric value in a given lane.
Replace lanes: consume a v128 operand and a numeric value for a given lane, and produce a v128 result.
**)

(* Definition expr := list basic_instruction. *)
```

- opsem.v:17 _reduce simple & reduce_
```coq
(* 17 *)
Inductive reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=

(** unop **)
  | rs_unop : forall v op t,
    reduce_simple [::$VN v; AI_basic (BI_unop t op)] [::$VN (@app_unop op v)]
                   
(** binop **)
  | rs_binop_success : forall v1 v2 v op t,
    app_binop op v1 v2 = Some v ->
    reduce_simple [::$VN v1; $VN v2; AI_basic (BI_binop t op)] [::$VN v]
  | rs_binop_failure : forall v1 v2 op t,
    app_binop op v1 v2 = None ->
    reduce_simple [::$VN v1; $VN v2; AI_basic (BI_binop t op)] [::AI_trap]

(* 173 *)
Inductive reduce : host_state -> store_record -> frame -> list administrative_instruction ->
                   host_state -> store_record -> frame -> list administrative_instruction -> Prop :=
  | r_simple :
      forall e e' s f hs,
        reduce_simple e e' ->
        reduce hs s f e hs s f e'
```

- operations.v:337 _unary operations and their applications_
```coq
Definition app_unop_i (e : Wasm_int.type) (iop : unop_i) : Wasm_int.sort e -> Wasm_int.sort e :=
  let: Wasm_int.Pack u (Wasm_int.Class eqmx intmx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' in
  match iop with
  | UOI_ctz => Wasm_int.int_ctz intmx
  | UOI_clz => Wasm_int.int_clz intmx
  | UOI_popcnt => Wasm_int.int_popcnt intmx
  end.

Definition app_unop_f (e : Wasm_float.type) (fop : unop_f) : Wasm_float.sort e -> Wasm_float.sort e :=
  let: Wasm_float.Pack u (Wasm_float.Class eqmx mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' in
  match fop with
  | UOF_neg => Wasm_float.float_neg mx
  | UOF_abs => Wasm_float.float_abs mx
  | UOF_ceil => Wasm_float.float_ceil mx
  | UOF_floor => Wasm_float.float_floor mx
  | UOF_trunc => Wasm_float.float_trunc mx
  | UOF_nearest => Wasm_float.float_nearest mx
  | UOF_sqrt => Wasm_float.float_sqrt mx
  end.

(* TODO: implement new extendN_s numerics *)
Definition app_unop_extend (n: N) (v: value_num) :=
  v.

Definition app_unop (op: unop) (v: value_num) :=
  match op with
  | Unop_i iop =>
    match v with
    | VAL_int32 c => VAL_int32 (@app_unop_i i32t iop c)
    | VAL_int64 c => VAL_int64 (@app_unop_i i64t iop c)
    | _ => v
    end
  | Unop_f fop =>
    match v with
    | VAL_float32 c => VAL_float32 (@app_unop_f f32t fop c)
    | VAL_float64 c => VAL_float64 (@app_unop_f f64t fop c)
    | _ => v
    end
  | Unop_extend n => app_unop_extend n v
  end.
```

- operations.v:380 _apply integer binary operations_
```coq
Definition app_binop_i (e : Wasm_int.type) (iop : binop_i)
    : Wasm_int.sort e -> Wasm_int.sort e -> option (Wasm_int.sort e) :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' -> option (Wasm_int.sort e') in
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match iop with
  | BOI_add => add_some (Wasm_int.int_add mx)
  | BOI_sub => add_some (Wasm_int.int_sub mx)
  | BOI_mul => add_some (Wasm_int.int_mul mx)
  | BOI_div SX_U => Wasm_int.int_div_u mx
  | BOI_div SX_S => Wasm_int.int_div_s mx
  | BOI_rem SX_U => Wasm_int.int_rem_u mx
  | BOI_rem SX_S => Wasm_int.int_rem_s mx
  | BOI_and => add_some (Wasm_int.int_and mx)
  | BOI_or => add_some (Wasm_int.int_or mx)
  | BOI_xor => add_some (Wasm_int.int_xor mx)
  | BOI_shl => add_some (Wasm_int.int_shl mx)
  | BOI_shr SX_U => add_some (Wasm_int.int_shr_u mx)
  | BOI_shr SX_S => add_some (Wasm_int.int_shr_s mx)
  | BOI_rotl => add_some (Wasm_int.int_rotl mx)
  | BOI_rotr => add_some (Wasm_int.int_rotr mx)
  end.
```

## Cl Semantics

### old code
```lean
namespace Imp

/-!
# Expr represents expressions
- val is a value (computation is done)
- do represents another operation which is paired with a continuation k
- this allows modular building of our language
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

/-- fold acts as the *visitor* pattern in imperative interpreters -/
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
```
```lean
namespace Wasm

open List
open Int

/-
inductive State :=
  | nil : State
  | cons : Int → List Int → State

infix:67 " :: " => State.cons

def State.pop (s : State) : State :=
  match s with
  | State.nil => State.nil
  | h :: t => t
-/

def State : Type := List Int

def State.pop (s : State) : Option (Int × State) :=
  match s with
  | [] => none
  | h :: t => some (h, t) -- (value, state')

def State.push (val : Int) (s : State) : State :=
  val :: s -- state'

-- Prop <--> Bool
-- proposition is that the state is of length ≥ 2 -> iadd
inductive WPlus : Type :=
  | iconst (v : Int) --: State → Int → WPlus
  | iadd : WPlus --State → WPlus
  -- | Wtrap : fail
  -- | ret : (s : State) → Int

/-!
# Notes
- need to figure out how to represent commands and values
- everything is based on `State`
  - is `List Int` the best way of thinking of state
  - how do you define an inductive type that relies on state?
## Wasm Instructions Include
- **ibinop**
  - these aren't binary in the sense that the constructor is passed two arguments
  - constructor is passed a state of at least `len ≥ 2` or at least needs this state
  - in wasm no arguments are passed
- **const**
  - recieves one argument which is the int to be pushed onto the stack

## Representing as inductively defined types
- how can these instructions be defined inductively?
  - maybe something like dependent types
  - `  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt`
- I am not trying to create an interpreter in the concrete sense but define rules
  for reasoning about wasm programs. The actual values returned doesn't matter but
  I need rules to compare to a simple 'Plus' language.

# Figure out what properties you want to prove
- build from the bottom up, don't get lost in the details.
- have a story, related works, proof of concept
- what is the point?
  - if you want to talk about concurrency / non determinism you need small step
  - what is the 'real meaning' of a semantics
    - need to normalize to some common language
  - denotational -> compiler
  - operational -> interpreter
1. say lang A and B are equivalent in some form
  - some simulation relation between them
  - **coq-hammer** ?
-/

-- Fixpoint : Prop 
-- inductive (...) : Prop
def eval (s : State) (c : WPlus): State :=
  match c with
  | WPlus.iconst v => s.push v
  | WPlus.iadd =>  match s.pop with
    | none => []
    | some (n1, s') => match s'.pop with
      | none => []
      | some (n2, s'') => s''.push (n1 + n2)

-- inductive eval : WPlus → State → State → Prop :=
  -- | iconst 

def s : State := []
def s1 : State := eval s (WPlus.iconst 10)
def s2 : State := eval s1 (WPlus.iconst 11)
def s3 : State := eval s2 (WPlus.iconst 5)
def s4 : State := eval s3 (WPlus.iadd)

#eval s1 
#eval s2 
#eval s3 
#eval s4 

end Wasm
```
