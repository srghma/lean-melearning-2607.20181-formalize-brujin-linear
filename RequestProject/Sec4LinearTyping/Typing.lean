module

public import RequestProject.Sec3FragmentaryEnv.FEnv

/-!
# The typing system for the linear λ-calculus (Section 4 of the paper)

* `LLTyped τ Γ t α Δ` — `⊢_ll {Γ} t : α {Δ}`, the main typing system of the paper (Figure 4);
* `Compatible` and `Minimal` environments.

Here `τ : C → Ty A` assigns a type to each constant. Recall that environments are lists whose
head is component `0` (so the paper's `Γ, α` is `α :: Γ`).
-/

@[expose] public section

namespace LinearDB

open Term

variable {A C : Type*}

/-- The typing system for the linear λ-calculus (Figure 4): `LLTyped τ Γ t α Δ` stands for the
Hodas–Miller style judgement `{Γ} t : α {Δ}`. -/
inductive LLTyped (τ : C → Ty A) : FEnv A → Term C → Ty A → FEnv A → Prop
  | const (Γ : FEnv A) (c : C) : LLTyped τ Γ (.const c) (τ c) Γ
  | var (Γ : FEnv A) (α : Ty A) : LLTyped τ (some α :: Γ) (.var 0) α (none :: Γ)
  | weak₁ {Γ Δ : FEnv A} {i : ℕ} {α : Ty A} (β : Ty A) :
      LLTyped τ Γ (.var i) α Δ → LLTyped τ (some β :: Γ) (.var (i + 1)) α (some β :: Δ)
  | weak₂ {Γ Δ : FEnv A} {i : ℕ} {α : Ty A} :
      LLTyped τ Γ (.var i) α Δ → LLTyped τ (none :: Γ) (.var (i + 1)) α (none :: Δ)
  -- | weak {Γ Δ : FEnv A} {i : ℕ} {α : Ty A} (ω : QTy A) :
  --     LLTyped τ Γ (.var i) α Δ → LLTyped τ (ω :: Γ) (.var (i + 1)) α (ω :: Δ)
  | app {Γ Δ Θ : FEnv A} {t u : Term C} {α β : Ty A} :
      LLTyped τ Γ t (.arr α β) Δ → LLTyped τ Δ u α Θ → LLTyped τ Γ (.app t u) β Θ
  | abs {Γ Δ : FEnv A} {t : Term C} {α β : Ty A} :
      LLTyped τ (some α :: Γ) t β (none :: Δ) → LLTyped τ Γ (.lam t) (.arr α β) Δ

/-- A fragmentary environment `Γ` is *compatible* with a term `t` iff for every `i ∈ fv t`,
`i < |Γ|` and `Γ(i) ≠ ⊥`. -/
def Compatible (Γ : FEnv A) (t : Term C) : Prop :=
  ∀ i ∈ t.fv, ∃ β : Ty A, Γ[i]? = some (some β)

/-- An environment `Γ` is *minimal* with respect to `t`.

The paper's definition reads: `(|Γ| - 1) ∈ fv t` and `i < |Γ|` for all `i ∈ fv t`.
Taken literally this is never satisfied by the empty environment (there is no index `-1`),
which would make the paper's characterization of linear terms fail for closed terms
such as `λ 0`. We therefore only require `(|Γ| - 1) ∈ fv t` when `Γ` is nonempty. -/
def Minimal (Γ : Env A) (t : Term C) : Prop :=
  (∀ n, Γ.length = n + 1 → n ∈ t.fv) ∧ ∀ i ∈ t.fv, i < Γ.length

end LinearDB
