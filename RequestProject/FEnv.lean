module

public import RequestProject.Syntax

/-!
# Typing environments and fragmentary environments (Sections 2 and 3 of the paper)

**Convention.** The paper writes environments left to right and numbers their components from
right to left, so that `Γ(0)` is the rightmost component and `Γ, α` extends `Γ` on the right.
We represent an environment as a Lean `List` whose *head is component `0`*. Hence
* the paper's `Γ(i)` is `Γ[i]` (or `Γ[i]?`);
* the paper's `Γ, α` is `α :: Γ`;
* the paper's `Γ₁, ω, Γ₂` is `Γ₂ ++ ω :: Γ₁` (and `Γ₁, Θ, Γ₂` is `Γ₂ ++ Θ ++ Γ₁`).

Quasi-types are `Option (Ty A)`, where `none` plays the role of the placeholder `⊥`.
The partial operations of addition and subtraction are modelled as functions returning an
`Option`, the value `none` meaning "undefined".
-/

@[expose] public section

namespace LinearDB

variable {A : Type*}

/-- Typing environments: finite sequences of simple types (head = component `0`). -/
abbrev Env (A : Type*) := List (Ty A)

/-- Quasi-types `qty = ty ∪ {⊥}`; `none` is `⊥`. -/
abbrev QTy (A : Type*) := Option (Ty A)

/-- Fragmentary environments: finite sequences of quasi-types (head = component `0`). -/
abbrev FEnv (A : Type*) := List (QTy A)

namespace QTy

/-- Partial addition of quasi-types: the smallest partial operation with
`⊥ + ω = ω` and `ω + ⊥ = ω`. (`none` = undefined.) -/
def add : QTy A → QTy A → Option (QTy A)
  | none, w => some w
  | w, none => some w
  | some _, some _ => none

/-- Partial subtraction of quasi-types: the smallest partial operation with
`ω - ⊥ = ω` and `ω - ω = ⊥`. (`none` = undefined.) -/
def sub [DecidableEq A] : QTy A → QTy A → Option (QTy A)
  | w, none => some w
  | none, some _ => none
  | some a, some b => if a = b then some none else none

/-- The flat partial order on quasi-types: `ψ ⊑ ω` iff `ψ = ⊥` or `ψ = ω`. -/
def le (ψ ω : QTy A) : Prop := ψ = none ∨ ψ = ω

end QTy

namespace FEnv

/-- Componentwise lifting of a partial binary operation on quasi-types to fragmentary
environments: defined iff both environments have the same length and the operation is defined
at every component. -/
def zipOp (f : QTy A → QTy A → Option (QTy A)) : FEnv A → FEnv A → Option (FEnv A)
  | [], [] => some []
  | a :: Γ, b :: Δ =>
    match f a b, zipOp f Γ Δ with
    | some c, some Θ => some (c :: Θ)
    | _, _ => none
  | _, _ => none

/-- Partial addition of fragmentary environments (componentwise). -/
def add (Γ Δ : FEnv A) : Option (FEnv A) := zipOp QTy.add Γ Δ

/-- Partial subtraction of fragmentary environments (componentwise). -/
def sub [DecidableEq A] (Γ Δ : FEnv A) : Option (FEnv A) := zipOp QTy.sub Γ Δ

/-- The order on fragmentary environments: `Γ ⊑ Δ` iff `|Γ| = |Δ|` and `Γ(i) ⊑ Δ(i)` for all
`i`. -/
def le (Γ Δ : FEnv A) : Prop := List.Forall₂ QTy.le Γ Δ

/-- Two fragmentary environments are *disjoint* (`Γ ⋈ Δ`) iff `Γ + Δ` is defined. -/
def Disjoint (Γ Δ : FEnv A) : Prop := (add Γ Δ).isSome

/-- The minimal fragmentary environment `⊥, …, ⊥` of length `n`. -/
def minenv (n : ℕ) : FEnv A := List.replicate n none

/-- Every typing environment is a fragmentary environment. -/
def ofEnv (Γ : Env A) : FEnv A := Γ.map some

end FEnv

end LinearDB
