module

public import RequestProject.Sec3FragmentaryEnv.FEnv

/-!
# The typing system with fragmentary environments (Section 3 of the paper)

`FLLTyped τ Γ t α` — `⊢_fll Γ ⊢ t : α`, fragmentary environments with a disjointness proviso
(Figure 3).
-/

@[expose] public section

namespace LinearDB

open Term

variable {A C : Type*}

/-- The typing system with fragmentary environments (Figure 3). The proviso `Γ ⋈ Δ` of
rule (app) is expressed by the requirement that `Γ + Δ` be defined (and equal to `Θ`). -/
inductive FLLTyped (τ : C → Ty A) : FEnv A → Term C → Ty A → Prop
  | const (n : ℕ) (c : C) : FLLTyped τ (FEnv.minenv n) (.const c) (τ c)
  | var (n : ℕ) (α : Ty A) : FLLTyped τ (some α :: FEnv.minenv n) (.var 0) α
  | weak {Γ : FEnv A} {i : ℕ} {α : Ty A} :
      FLLTyped τ Γ (.var i) α → FLLTyped τ (none :: Γ) (.var (i + 1)) α
  | app {Γ Δ Θ : FEnv A} {t u : Term C} {α β : Ty A} :
      FLLTyped τ Γ t (.arr α β) → FLLTyped τ Δ u α → FEnv.add Γ Δ = some Θ →
      FLLTyped τ Θ (.app t u) β
  | abs {Γ : FEnv A} {t : Term C} {α β : Ty A} :
      FLLTyped τ (some α :: Γ) t β → FLLTyped τ Γ (.lam t) (.arr α β)

end LinearDB
