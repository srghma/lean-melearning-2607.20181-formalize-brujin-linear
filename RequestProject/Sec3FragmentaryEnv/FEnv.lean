module

public import RequestProject.Sec2SimplyTyped.Typing

/-!
# Fragmentary environments (Section 3 of the paper)

Typing environments `Env` are defined in `Sec2SimplyTyped/Typing.lean`.

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

/-- Zips two lists with a partial operation `f`.
    Succeeds iff both lists have the exact same length and `f` succeeds at every element. -/
def List.zipWithExactM {m : Type u → Type u} [Monad m] [Alternative m]
    {α β γ : Type u} (f : α → β → m γ) : List α → List β → m (List γ)
  | [], [] => pure []
  | a :: as, b :: bs => do
    let c ← f a b
    let cs ← List.zipWithExactM f as bs
    pure (c :: cs)
  | _, _ => failure

namespace LinearDB

variable {A : Type*}

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

/-- Partial addition of fragmentary environments (componentwise). -/
def add (Γ Δ : FEnv A) : Option (FEnv A) := List.zipWithExactM QTy.add Γ Δ

/-- Partial subtraction of fragmentary environments (componentwise). -/
def sub [DecidableEq A] (Γ Δ : FEnv A) : Option (FEnv A) := List.zipWithExactM QTy.sub Γ Δ

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
