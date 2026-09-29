module

public import Mathlib

/-!
# Syntax of the λ-calculus in de Bruijn notation (Sections 2 and 5 of the paper)

* simple types `Ty A` over a set `A` of atomic types;
* λ-terms `Term C` in de Bruijn notation over a set `C` of constants (Definition 1);
* the number of free occurrences `occ i t` of an index, the free variables `fv t`;
* linear and quasi-linear λ-terms (Definition of linearity, conditions i–iii);
* lifting, substitution and β-contraction / β-reduction (Section 5).
-/

@[expose] public section

namespace LinearDB

/-- Simple types over a set `A` of atomic types: `ty ::= a | (ty → ty)`. -/
inductive Ty (A : Type*) where
  | atom : A → Ty A
  | arr : Ty A → Ty A → Ty A
  deriving DecidableEq

/-- λ-terms in de Bruijn notation over a set `C` of constants:
`lt ::= c | i | (lt lt) | (λ lt)` (Definition 1). -/
inductive Term (C : Type*) where
  | const : C → Term C
  | var : ℕ → Term C
  | app : Term C → Term C → Term C
  | lam : Term C → Term C
  deriving DecidableEq

namespace Term

variable {C : Type*}

/-- `occ i t`: the number of free occurrences of the index `i` in `t`. -/
def occ : ℕ → Term C → ℕ
  | _, const _ => 0
  | i, var j => if i = j then 1 else 0
  | i, app t₁ t₂ => occ i t₁ + occ i t₂
  | i, lam t₁ => occ (i + 1) t₁

/-- The set of free variables of a term: the indices with a nonzero number of occurrences. -/
def fv (t : Term C) : Set ℕ := {i | occ i t ≠ 0}

/-- The (reflexive) subterm relation: `IsSubterm s t` means that `s` is a subterm of `t`. -/
inductive IsSubterm : Term C → Term C → Prop
  | refl (t : Term C) : IsSubterm t t
  | appL {s t₁ : Term C} (t₂ : Term C) : IsSubterm s t₁ → IsSubterm s (app t₁ t₂)
  | appR {s t₂ : Term C} (t₁ : Term C) : IsSubterm s t₂ → IsSubterm s (app t₁ t₂)
  | lam {s t : Term C} : IsSubterm s t → IsSubterm s (lam t)

/-- A λ-term is *quasi-linear* if it satisfies conditions (i) and (ii) of the definition of
linearity:
(i) every subterm of the form `(λ u)` satisfies `occ 0 u = 1`;
(ii) every free variable `i` of `t` satisfies `occ i t = 1`. -/
def QuasiLinear (t : Term C) : Prop :=
  (∀ u, IsSubterm (lam u) t → occ 0 u = 1) ∧ (∀ i ∈ fv t, occ i t = 1)

/-- A λ-term is *linear* if it is quasi-linear and moreover
(iii) whenever `i ∈ fv t` and `j < i`, then `j ∈ fv t`. -/
def Linear (t : Term C) : Prop :=
  QuasiLinear t ∧ ∀ i j : ℕ, i ∈ fv t → j < i → j ∈ fv t

/-- Lifting `↑ᵏᵢ(t)`: add `k` to every index of `t` that is `≥ i` (where `i` counts the
enclosing λ's). Written `lift t k i`. -/
def lift : Term C → ℕ → ℕ → Term C
  | const c, _, _ => const c
  | var j, k, i => if j < i then var j else var (j + k)
  | app t₁ t₂, k, i => app (lift t₁ k i) (lift t₂ k i)
  | lam t₁, k, i => lam (lift t₁ k (i + 1))

/-- Substitution `t[i := u]` of the index `i` by the term `u` in `t`. Written `subst t i u`. -/
def subst : Term C → ℕ → Term C → Term C
  | const c, _, _ => const c
  | var j, i, u => if j < i then var j else if j = i then lift u i 0 else var (j - 1)
  | app t₁ t₂, i, u => app (subst t₁ i u) (subst t₂ i u)
  | lam t₁, i, u => lam (subst t₁ (i + 1) u)

/-- β-contraction `t →β u` (Definition of β-contraction). -/
inductive Beta : Term C → Term C → Prop
  | beta (t u : Term C) : Beta (app (lam t) u) (subst t 0 u)
  | appL {t u : Term C} (v : Term C) : Beta t u → Beta (app t v) (app u v)
  | appR {t u : Term C} (v : Term C) : Beta t u → Beta (app v t) (app v u)
  | lam {t u : Term C} : Beta t u → Beta (lam t) (lam u)

/-- β-reduction: the reflexive, transitive closure of β-contraction. -/
def BetaRed : Term C → Term C → Prop := Relation.ReflTransGen Beta

end Term

end LinearDB
