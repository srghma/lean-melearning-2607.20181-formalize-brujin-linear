module

public import RequestProject.Sec2SimplyTyped.Syntax

@[expose] public section

set_option autoImplicit false

/-!
# Toy types: the simple types of the paper over three leaves

The grammar of types of the toy language is the grammar of the paper,
`ty ::= a | (ty → ty)` (`LinearDB.Ty`), read as *linear* function types `σ ⊸ τ`, and
instantiated at three leaves (`Base`: `nat`, `bool`, `string`).

```
Base ::= nat | bool | string
LTy  ::= atom Base | arr LTy LTy          -- `arr σ τ` is the linear arrow `σ ⊸ τ`
```

What cannot be written:

* a product, a sum, a unit, a recursive type: there are none, only leaves and arrows;
* a leaf other than the three of `Base`.

Every type is, uniquely, a *spine* `σ₁ ⊸ … ⊸ σₙ ⊸ b` of argument types ending in a leaf
(`Ty.args`, `Ty.result`, `Ty.ofSpine_args_result`).  Renaming the leaves (`Ty.map`) is a
functor (`Ty.map_id`, `Ty.map_map`).
-/

namespace LinearDB

namespace Toy

/-! ## Leaves -/

/-- The leaves of the toy language. -/
inductive Base : Type where
  | nat
  | bool
  | string
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- The Lean type a leaf denotes. -/
def Base.denote : Base → Type
  | .nat => ℕ
  | .bool => Bool
  | .string => String

/-! ## Types -/

/-- The types of the toy language: the paper's simple types over `Base`. -/
abbrev LTy : Type := Ty Base

namespace LTy

/-- `Nat`. -/
abbrev nat : LTy := .atom .nat
/-- `Bool`. -/
abbrev bool : LTy := .atom .bool
/-- `String`. -/
abbrev string : LTy := .atom .string
/-- The linear function type `σ ⊸ τ`. -/
abbrev fn (σ τ : LTy) : LTy := .arr σ τ

/-- What a type denotes: a leaf its Lean type, `σ ⊸ τ` the Lean functions (linearity is a
    property of the terms, not of the values). -/
def den : LTy → Type
  | .atom b => b.denote
  | .arr σ τ => den σ → den τ

end LTy

end Toy

/-! ## Spines and renaming (for any set of leaves) -/

namespace Ty

variable {A B D : Type*}

/-- The argument types of a type: `σ₁ ⊸ … ⊸ σₙ ⊸ b` has arguments `[σ₁, …, σₙ]`. -/
def args : Ty A → List (Ty A)
  | .atom _ => []
  | .arr σ τ => σ :: args τ

/-- The leaf a type ends in: `σ₁ ⊸ … ⊸ σₙ ⊸ b` ends in `b`. -/
def result : Ty A → A
  | .atom a => a
  | .arr _ τ => result τ

/-- The type `σ₁ ⊸ … ⊸ σₙ ⊸ b` from its spine. -/
def ofSpine : List (Ty A) → A → Ty A
  | [], a => .atom a
  | σ :: σs, a => .arr σ (ofSpine σs a)

/-- Every type is the spine of its arguments and its leaf. -/
@[simp] theorem ofSpine_args_result (t : Ty A) : ofSpine t.args t.result = t := by
  induction t with
  | atom a => rfl
  | arr σ τ _ ih => simp [args, result, ofSpine, ih]

/-- The spine of a type determines it. -/
@[simp] theorem args_ofSpine (σs : List (Ty A)) (a : A) : (ofSpine σs a).args = σs := by
  induction σs with
  | nil => rfl
  | cons σ σs ih => simp [args, ofSpine, ih]

@[simp] theorem result_ofSpine (σs : List (Ty A)) (a : A) : (ofSpine σs a).result = a := by
  induction σs with
  | nil => rfl
  | cons σ σs ih => simp [result, ofSpine, ih]

/-- Rename the leaves of a type. -/
def map (f : A → B) : Ty A → Ty B
  | .atom a => .atom (f a)
  | .arr σ τ => .arr (map f σ) (map f τ)

/-- Renaming by the identity is the identity. -/
@[simp] theorem map_id (t : Ty A) : t.map (fun a => a) = t := by
  induction t with
  | atom a => rfl
  | arr σ τ ih₁ ih₂ => simp [map, ih₁, ih₂]

/-- Renaming twice is renaming by the composite. -/
@[simp] theorem map_map (f : A → B) (g : B → D) (t : Ty A) :
    (t.map f).map g = t.map (fun a => g (f a)) := by
  induction t with
  | atom a => rfl
  | arr σ τ ih₁ ih₂ => simp [map, ih₁, ih₂]

end Ty

end LinearDB

end
