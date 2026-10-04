module

public import Mathlib

/-!
# Syntax of the λ-calculus in de Bruijn notation (Section 2 of the paper)

* simple types `Ty A` over a set `A` of atomic types;
* λ-terms `Term C` in de Bruijn notation over a set `C` of constants (Definition 1);
* the number of free occurrences `occ i t` of an index, the free variables `fv t`;
* linear and quasi-linear λ-terms (Definition of linearity, conditions i–iii), with some
  elementary facts about subterms of quasi-linear terms.

Lifting, substitution and β-reduction (Section 5) are in `Sec5BetaReduction/Beta.lean`.
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

end Term

/-! ### Subterms of quasi-linear terms -/

namespace Term

variable {C : Type*}

lemma occ_var (i j : ℕ) : occ i (var j : Term C) = if i = j then 1 else 0 := rfl

lemma not_isSubterm_lam_var {u : Term C} {j : ℕ} : ¬ IsSubterm (lam u) (var j) := by
  intro h; cases h

lemma not_isSubterm_lam_const {u : Term C} {c : C} : ¬ IsSubterm (lam u) (const c) := by
  intro h; cases h

lemma QuasiLinear.app_left {t u : Term C} (h : QuasiLinear (app t u)) : QuasiLinear t := by
  refine ⟨fun v hv => h.1 v (IsSubterm.appL _ hv), fun i hi => ?_⟩
  have := h.2 i (by simp only [fv, Set.mem_setOf_eq, occ] at hi ⊢; omega)
  simp only [fv, Set.mem_setOf_eq, occ] at hi this; omega

lemma QuasiLinear.app_right {t u : Term C} (h : QuasiLinear (app t u)) : QuasiLinear u := by
  refine ⟨fun v hv => h.1 v (IsSubterm.appR _ hv), fun i hi => ?_⟩
  have := h.2 i (by simp only [fv, Set.mem_setOf_eq, occ] at hi ⊢; omega)
  simp only [fv, Set.mem_setOf_eq, occ] at hi this; omega

lemma QuasiLinear.occ_zero_of_lam {t : Term C} (h : QuasiLinear (lam t)) : occ 0 t = 1 :=
  h.1 t (IsSubterm.refl _)

lemma QuasiLinear.of_lam {t : Term C} (h : QuasiLinear (lam t)) : QuasiLinear t := by
  refine ⟨fun v hv => h.1 v (IsSubterm.lam hv), fun i hi => ?_⟩
  rcases i with _ | i
  · exact h.occ_zero_of_lam
  · exact h.2 i hi

lemma quasiLinear_var (j : ℕ) : QuasiLinear (var j : Term C) := by
  refine ⟨fun u hu => absurd hu not_isSubterm_lam_var, fun i hi => ?_⟩
  simp only [fv, Set.mem_setOf_eq, occ] at hi ⊢
  split_ifs at hi ⊢ <;> simp_all

end Term

end LinearDB
