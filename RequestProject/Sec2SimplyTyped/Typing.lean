module

public import RequestProject.Sec2SimplyTyped.Syntax

/-!
# The simply typed λ-calculus in de Bruijn notation (Section 2 of the paper)

* `Env A` — typing environments;
* `STTyped τ Γ t α` — `⊢_st Γ ⊢ t : α`, the typing system of Figure 2.

Here `τ : C → Ty A` assigns a type to each constant.

**Convention.** The paper writes environments left to right and numbers their components from
right to left, so that `Γ(0)` is the rightmost component and `Γ, α` extends `Γ` on the right.
We represent an environment as a Lean `List` whose *head is component `0`*. Hence the paper's
`Γ(i)` is `Γ[i]`, and the paper's `Γ, α` is `α :: Γ`.
-/

@[expose] public section

namespace LinearDB

open Term

variable {A C : Type*}

/-- Typing environments: finite sequences of simple types (head = component `0`). -/
abbrev Env (A : Type*) := List (Ty A)

/-- The simply typed λ-calculus in de Bruijn notation (Figure 2). -/
inductive STTyped (τ : C → Ty A) : Env A → Term C → Ty A → Prop
  | const (Γ : Env A) (c : C) : STTyped τ Γ (.const c) (τ c)
  | var (Γ : Env A) (α : Ty A) : STTyped τ (α :: Γ) (.var 0) α
  | weak {Γ : Env A} {i : ℕ} {α : Ty A} (β : Ty A) :
      STTyped τ Γ (.var i) α → STTyped τ (β :: Γ) (.var (i + 1)) α
  | app {Γ : Env A} {t u : Term C} {α β : Ty A} :
      STTyped τ Γ t (.arr α β) → STTyped τ Γ u α → STTyped τ Γ (.app t u) β
  | abs {Γ : Env A} {t : Term C} {α β : Ty A} :
      STTyped τ (α :: Γ) t β → STTyped τ Γ (.lam t) (.arr α β)

end LinearDB
