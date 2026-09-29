module

public import RequestProject.Typing
public import RequestProject.FEnvLemmas

/-!
# Properties of the typing system for the linear λ-calculus (Section 4 of the paper)

* `LLTyped.le`            — Lemma `subeq`;
* `LLTyped.occ_spec`      — Lemma `quasi-linearity-aux`;
* `LLTyped.quasiLinear`   — Proposition `quasi-linearity`;
* `LLTyped.toST`          — Proposition `ll2st`;
* `STTyped.toLL`          — Proposition `st2ll`;
* `llTyped_minenv_iff`    — characterization of the linear simply-typed λ-terms;
* `LLTyped.add_env`, `LLTyped.sub_env` — Lemma `envarith`.
-/

@[expose] public section

namespace LinearDB

open Term

variable {A C : Type*}

/-! ### Basic facts about `⊑` -/

namespace QTy

lemma le_refl (a : QTy A) : le a a := Or.inr rfl

lemma le_trans {a b c : QTy A} (h₁ : le a b) (h₂ : le b c) : le a c := by
  rcases h₁ with rfl | rfl
  · exact Or.inl rfl
  · exact h₂

end QTy

namespace FEnv

lemma le_refl (Γ : FEnv A) : le Γ Γ := List.forall₂_same.2 fun a _ => QTy.le_refl a

lemma le_trans {Γ Δ Θ : FEnv A} (h₁ : le Γ Δ) (h₂ : le Δ Θ) : le Γ Θ := by
  unfold le at *
  induction h₁ generalizing Θ with
  | nil => cases h₂; exact List.Forall₂.nil
  | cons hab _ ih =>
    cases h₂ with
    | cons hbc h => exact List.Forall₂.cons (QTy.le_trans hab hbc) (ih h)

@[simp] lemma le_cons_cons {a b : QTy A} {Γ Δ : FEnv A} :
    le (a :: Γ) (b :: Δ) ↔ QTy.le a b ∧ le Γ Δ := List.forall₂_cons

lemma le_length {Γ Δ : FEnv A} (h : le Γ Δ) : Γ.length = Δ.length := List.Forall₂.length_eq h

lemma le_nil_left {Δ : FEnv A} : le [] Δ ↔ Δ = [] := List.forall₂_nil_left_iff

lemma le_nil_right {Γ : FEnv A} : le Γ [] ↔ Γ = [] := List.forall₂_nil_right_iff

lemma le_cons_left {a : QTy A} {Γ Δ : FEnv A} (h : le (a :: Γ) Δ) :
    ∃ b Δ', Δ = b :: Δ' ∧ QTy.le a b ∧ le Γ Δ' := by
  cases Δ with
  | nil => exact absurd (le_length h) (by simp)
  | cons b Δ' => exact ⟨b, Δ', rfl, (le_cons_cons.1 h).1, (le_cons_cons.1 h).2⟩

lemma le_cons_right {b : QTy A} {Γ Δ : FEnv A} (h : le Γ (b :: Δ)) :
    ∃ a Γ', Γ = a :: Γ' ∧ QTy.le a b ∧ le Γ' Δ := by
  cases Γ with
  | nil => exact absurd (le_length h) (by simp)
  | cons a Γ' => exact ⟨a, Γ', rfl, (le_cons_cons.1 h).1, (le_cons_cons.1 h).2⟩

@[simp] lemma ofEnv_nil : ofEnv ([] : Env A) = [] := rfl

@[simp] lemma ofEnv_cons (α : Ty A) (Γ : Env A) : ofEnv (α :: Γ) = some α :: ofEnv Γ := rfl

@[simp] lemma length_ofEnv (Γ : Env A) : (ofEnv Γ).length = Γ.length := List.length_map _

@[simp] lemma length_minenv (n : ℕ) : (minenv n : FEnv A).length = n := List.length_replicate

lemma add_cons_cons_eq_some {a b : QTy A} {Γ Δ Θ : FEnv A} :
    add (a :: Γ) (b :: Δ) = some Θ ↔
      ∃ c Θ', QTy.add a b = some c ∧ add Γ Δ = some Θ' ∧ Θ = c :: Θ' :=
  zipOp_cons_cons_eq_some _

lemma sub_cons_cons_eq_some [DecidableEq A] {a b : QTy A} {Γ Δ Θ : FEnv A} :
    sub (a :: Γ) (b :: Δ) = some Θ ↔
      ∃ c Θ', QTy.sub a b = some c ∧ sub Γ Δ = some Θ' ∧ Θ = c :: Θ' :=
  zipOp_cons_cons_eq_some _

@[simp] lemma add_cons_cons_some_iff {a b c : QTy A} {Γ Δ Θ : FEnv A} :
    add (a :: Γ) (b :: Δ) = some (c :: Θ) ↔ QTy.add a b = some c ∧ add Γ Δ = some Θ := by
  rw [add_cons_cons_eq_some]; simp

@[simp] lemma sub_cons_cons_some_iff [DecidableEq A] {a b c : QTy A} {Γ Δ Θ : FEnv A} :
    sub (a :: Γ) (b :: Δ) = some (c :: Θ) ↔ QTy.sub a b = some c ∧ sub Γ Δ = some Θ := by
  rw [sub_cons_cons_eq_some]; simp

end FEnv

/-! ### Subterms of quasi-linear terms -/

namespace Term

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

/-! ### Lemma `subeq` -/

/-- Lemma `subeq`: if `⊢_ll {Γ} t : α {Δ}` then `Δ ⊑ Γ`. -/
theorem LLTyped.le {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) : FEnv.le Δ Γ := by
  induction h with
  | const Γ c => exact FEnv.le_refl Γ
  | var Γ α => exact FEnv.le_cons_cons.2 ⟨Or.inl rfl, FEnv.le_refl Γ⟩
  | weak₁ β _ ih => exact FEnv.le_cons_cons.2 ⟨QTy.le_refl _, ih⟩
  | weak₂ _ ih => exact FEnv.le_cons_cons.2 ⟨QTy.le_refl _, ih⟩
  | app _ _ ih₁ ih₂ => exact FEnv.le_trans ih₂ ih₁
  | abs _ ih => exact (FEnv.le_cons_cons.1 ih).2

theorem LLTyped.length_eq {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) : Δ.length = Γ.length := FEnv.le_length h.le

/-! ### Lemma `quasi-linearity-aux` -/

/-- Uniform version of Lemma `quasi-linearity-aux`, valid for every index `i`
(for `i ≥ |Γ|` both lookups are undefined and `i` does not occur in `t`). -/
theorem LLTyped.occ_cases {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) (i : ℕ) :
    (Γ[i]? = Δ[i]? ∧ occ i t = 0) ∨
      ((∃ β, Γ[i]? = some (some β)) ∧ Δ[i]? = some none ∧ occ i t = 1) := by
  induction h generalizing i with
  | const Γ c => left; simp [occ]
  | var Γ α =>
    rcases i with _ | i
    · right; simp [occ]
    · left; simp [occ]
  | weak₁ β _ ih =>
    rcases i with _ | i
    · left; simp [occ]
    · simpa [occ] using ih i
  | weak₂ _ ih =>
    rcases i with _ | i
    · left; simp [occ]
    · simpa [occ] using ih i
  | app _ _ ih₁ ih₂ =>
    simp only [occ]
    rcases ih₁ i with ⟨h1, h2⟩ | ⟨⟨β, h1⟩, h2, h3⟩ <;>
      rcases ih₂ i with ⟨h4, h5⟩ | ⟨⟨β', h4⟩, h5, h6⟩
    · left; exact ⟨h1.trans h4, by omega⟩
    · right; exact ⟨⟨β', h1.trans h4⟩, h5, by omega⟩
    · right; exact ⟨⟨β, h1⟩, h4 ▸ h2, by omega⟩
    · rw [h2] at h4; simp at h4
  | abs _ ih => simpa [occ] using ih (i + 1)

/-- Lemma `quasi-linearity-aux`: if `⊢_ll {Γ} t : α {Δ}`, then for every index `i`,
if `Γ(i) ∈ ty` and `Δ(i) = ⊥` then `occ(i, t) = 1`; otherwise `Γ(i) = Δ(i)` and
`occ(i, t) = 0`. (The paper restricts to `0 ≤ i < |Γ|`; the statement holds for every `i`,
lookups beyond the length being undefined on both sides.) -/
theorem LLTyped.occ_spec {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) (i : ℕ) :
    ((∃ β, Γ[i]? = some (some β)) ∧ Δ[i]? = some none → occ i t = 1) ∧
      (¬ ((∃ β, Γ[i]? = some (some β)) ∧ Δ[i]? = some none) →
        Γ[i]? = Δ[i]? ∧ occ i t = 0) := by
  rcases h.occ_cases i with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · refine ⟨fun ⟨⟨β, hβ⟩, hΔ⟩ => ?_, fun _ => ⟨h1, h2⟩⟩
    rw [hβ, hΔ] at h1; simp at h1
  · exact ⟨fun _ => h3, fun hn => absurd ⟨h1, h2⟩ hn⟩

/-- Every free variable of an `ll`-typed term is declared (with a proper type) in the input
environment. -/
theorem LLTyped.compatible {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) : Compatible Γ t := by
  intro i hi
  rcases h.occ_cases i with ⟨-, h2⟩ | ⟨h1, -, -⟩
  · exact absurd h2 hi
  · exact h1

/-! ### Proposition `quasi-linearity` -/

/-- Proposition `quasi-linearity`: every `ll`-typable term is quasi-linear. -/
theorem LLTyped.quasiLinear {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) : QuasiLinear t := by
  refine ⟨?_, fun i hi => ?_⟩
  · intro v hv
    induction h generalizing v with
    | const _ _ => exact absurd hv not_isSubterm_lam_const
    | var _ _ => exact absurd hv not_isSubterm_lam_var
    | weak₁ _ _ _ => exact absurd hv not_isSubterm_lam_var
    | weak₂ _ _ => exact absurd hv not_isSubterm_lam_var
    | app _ _ ih₁ ih₂ =>
      cases hv with
      | appL _ hv => exact ih₁ _ hv
      | appR _ hv => exact ih₂ _ hv
    | abs h ih =>
      cases hv with
      | refl =>
        rcases h.occ_cases 0 with ⟨h1, -⟩ | ⟨-, -, h3⟩
        · simp at h1
        · exact h3
      | lam hv => exact ih _ hv
  · rcases h.occ_cases i with ⟨-, h2⟩ | ⟨-, -, h3⟩
    · exact absurd h2 hi
    · exact h3

/-! ### Proposition `ll2st` -/

/-- The generalized statement used to prove Proposition `ll2st`: for every environment `Θ`
such that `Γ ⊑ Θ`, `⊢_st Θ ⊢ t : α`. -/
theorem LLTyped.toST_of_le {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) : ∀ Θ : Env A, FEnv.le Γ (FEnv.ofEnv Θ) → STTyped τ Θ t α := by
  induction h with
  | const Γ c => intro Θ _; exact STTyped.const Θ c
  | var Γ α =>
    intro Θ hΘ
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.le_nil_right] at hΘ
    · simp only [FEnv.ofEnv_cons, FEnv.le_cons_cons, QTy.le] at hΘ
      obtain ⟨h1 | h1, -⟩ := hΘ
      · simp at h1
      · cases h1; exact STTyped.var _ _
  | weak₁ β _ ih =>
    intro Θ hΘ
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.le_nil_right] at hΘ
    · simp only [FEnv.ofEnv_cons, FEnv.le_cons_cons] at hΘ
      exact STTyped.weak θ (ih Θ hΘ.2)
  | weak₂ _ ih =>
    intro Θ hΘ
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.le_nil_right] at hΘ
    · simp only [FEnv.ofEnv_cons, FEnv.le_cons_cons] at hΘ
      exact STTyped.weak θ (ih Θ hΘ.2)
  | app h₁ _ ih₁ ih₂ =>
    intro Θ hΘ
    exact STTyped.app (ih₁ Θ hΘ) (ih₂ Θ (FEnv.le_trans h₁.le hΘ))
  | @abs Γ Δ t α β _ ih =>
    intro Θ hΘ
    exact STTyped.abs (ih (α :: Θ) (by simpa using ⟨QTy.le_refl _, hΘ⟩))

/-- Proposition `ll2st`: if `⊢_ll {Γ} t : α {Δ}`, then there exists an environment `Θ` such
that `Γ ⊑ Θ` and `⊢_st Θ ⊢ t : α`. -/
theorem LLTyped.toST {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) : ∃ Θ : Env A, FEnv.le Γ (FEnv.ofEnv Θ) ∧ STTyped τ Θ t α := by
  refine ⟨Γ.map (fun a => a.getD α), ?_, h.toST_of_le _ ?_⟩ <;>
  · clear h
    induction Γ with
    | nil => exact List.Forall₂.nil
    | cons a Γ ih =>
      refine List.Forall₂.cons ?_ ih
      rcases a with _ | a
      · exact Or.inl rfl
      · exact Or.inr rfl

/-! ### Proposition `st2ll` -/

/-- Free variables of a simply-typed term are declared in the environment. -/
theorem STTyped.fv_lt {τ : C → Ty A} {Γ : Env A} {t : Term C} {α : Ty A}
    (h : STTyped τ Γ t α) : ∀ i ∈ t.fv, i < Γ.length := by
  induction h with
  | const => intro i hi; simp [fv, occ] at hi
  | var =>
    intro i hi
    simp only [fv, Set.mem_setOf_eq, occ] at hi
    split_ifs at hi with h
    · simp [h]
    · simp at hi
  | weak β _ ih =>
    intro i hi
    rcases i with _ | i
    · simp [fv, occ] at hi
    · have := ih i (by simpa [fv, occ] using hi)
      simp; omega
  | @app _ t u _ _ _ _ ih₁ ih₂ =>
    intro i hi
    simp only [fv, Set.mem_setOf_eq, occ] at hi
    by_cases h : occ i t = 0
    · exact ih₂ i (by simp [fv]; omega)
    · exact ih₁ i h
  | abs _ ih =>
    intro i hi
    have := ih (i + 1) hi
    simp at this; omega

/-- The generalized statement used to prove Proposition `st2ll`: for every fragmentary
environment `Θ` compatible with `t` such that `Θ ⊑ Γ`, there exists `Δ` such that
`⊢_ll {Θ} t : α {Δ}`. -/
theorem STTyped.toLL_of_le {τ : C → Ty A} {Γ : Env A} {t : Term C} {α : Ty A}
    (h : STTyped τ Γ t α) (hq : QuasiLinear t) :
    ∀ Θ : FEnv A, Compatible Θ t → FEnv.le Θ (FEnv.ofEnv Γ) → ∃ Δ, LLTyped τ Θ t α Δ := by
  induction h with
  | const Γ c => intro Θ _ _; exact ⟨Θ, LLTyped.const Θ c⟩
  | var Γ α =>
    intro Θ hc hΘ
    obtain ⟨β, hβ⟩ := hc 0 (by simp [fv, occ])
    obtain ⟨b, Θ', rfl, hb, -⟩ := FEnv.le_cons_right hΘ
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hβ
    subst hβ
    rcases hb with hb | hb
    · simp at hb
    · cases hb; exact ⟨_, LLTyped.var Θ' _⟩
  | @weak Γ i α β _ ih =>
    intro Θ hc hΘ
    obtain ⟨θ, Θ', rfl, -, hΘ'⟩ := FEnv.le_cons_right hΘ
    have hc' : Compatible Θ' (Term.var i : Term C) := by
      intro j hj
      have hj' : j = i := by
        simp only [fv, Set.mem_setOf_eq, occ] at hj; split_ifs at hj with h <;> simp_all
      subst hj'
      simpa using hc (j + 1) (by simp [fv, occ])
    obtain ⟨Δ, hΔ⟩ := ih (quasiLinear_var i) Θ' hc' hΘ'
    rcases θ with _ | θ
    · exact ⟨_, LLTyped.weak₂ hΔ⟩
    · exact ⟨_, LLTyped.weak₁ θ hΔ⟩
  | @app Γ t u α β h₁ h₂ ih₁ ih₂ =>
    intro Θ hc hΘ
    have hc₁ : Compatible Θ t := fun i hi =>
      hc i (by simp only [fv, Set.mem_setOf_eq, occ] at hi ⊢; omega)
    obtain ⟨Λ, hΛ⟩ := ih₁ hq.app_left Θ hc₁ hΘ
    have hc₂ : Compatible Λ u := by
      intro i hi
      have hi' : i ∈ (Term.app t u).fv := by simp only [fv, Set.mem_setOf_eq, occ] at hi ⊢; omega
      have h1 := hq.2 i hi'
      simp only [fv, Set.mem_setOf_eq, occ] at hi h1
      rcases hΛ.occ_cases i with ⟨e, -⟩ | ⟨-, -, e⟩
      · rw [← e]; exact hc i hi'
      · omega
    exact (ih₂ hq.app_right Λ hc₂ (FEnv.le_trans hΛ.le hΘ)).imp fun Δ hΔ => LLTyped.app hΛ hΔ
  | @abs Γ t α β _ ih =>
    intro Θ hc hΘ
    have hc' : Compatible (some α :: Θ) t := by
      rintro (_ | i) hi
      · exact ⟨α, rfl⟩
      · simpa using hc i hi
    obtain ⟨Δ', hΔ'⟩ := ih hq.of_lam (some α :: Θ) hc' (by simpa using ⟨QTy.le_refl _, hΘ⟩)
    obtain ⟨d, Δ, rfl, -, -⟩ := FEnv.le_cons_right hΔ'.le
    rcases hΔ'.occ_cases 0 with ⟨-, h2⟩ | ⟨-, h2, -⟩
    · rw [hq.occ_zero_of_lam] at h2; simp at h2
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at h2
      subst h2
      exact ⟨Δ, LLTyped.abs hΔ'⟩

/-- Proposition `st2ll`: if `⊢_st Γ ⊢ t : α` and `t` is quasi-linear, then there exists a
fragmentary environment `Δ` such that `⊢_ll {Γ} t : α {Δ}`. -/
theorem STTyped.toLL {τ : C → Ty A} {Γ : Env A} {t : Term C} {α : Ty A}
    (h : STTyped τ Γ t α) (hq : QuasiLinear t) : ∃ Δ, LLTyped τ (FEnv.ofEnv Γ) t α Δ := by
  refine h.toLL_of_le hq _ (fun i hi => ?_) (FEnv.le_refl _)
  have := h.fv_lt i hi
  exact ⟨Γ[i], by simp [FEnv.ofEnv, this]⟩

/-! ### Characterization of the linear simply-typed λ-terms -/

/-- `⊢_ll {Γ} t : α {⊥…⊥}` if and only if `t` is a linear λ-term, `Γ` is minimal with respect
to `t`, and `⊢_st Γ ⊢ t : α`. (Minimality is taken in the corrected sense of `Minimal`.) -/
theorem llTyped_minenv_iff {τ : C → Ty A} {Γ : Env A} {t : Term C} {α : Ty A} :
    LLTyped τ (FEnv.ofEnv Γ) t α (FEnv.minenv Γ.length) ↔
      Linear t ∧ Minimal Γ t ∧ STTyped τ Γ t α := by
  have key : ∀ Δ : FEnv A, LLTyped τ (FEnv.ofEnv Γ) t α Δ →
      (∀ i, i ∈ t.fv ↔ i < Γ.length) → Δ = FEnv.minenv Γ.length := by
    intro Δ hΔ hfv
    apply List.ext_getElem?
    intro i
    rcases hΔ.occ_cases i with ⟨h1, h2⟩ | ⟨-, h2, -⟩
    · by_cases hi : i < Γ.length
      · exact absurd h2 ((hfv i).2 hi)
      · rw [← h1, List.getElem?_eq_none (by simp; omega),
          List.getElem?_eq_none (by simp; omega)]
    · rw [h2]
      have : i < Δ.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at h2; simp at h2
      rw [hΔ.length_eq] at this
      simp only [FEnv.length_ofEnv] at this
      simp [FEnv.minenv, this]
  constructor
  · intro h
    have hfv : ∀ i, i ∈ t.fv ↔ i < Γ.length := by
      intro i
      rcases h.occ_cases i with ⟨h1, h2⟩ | ⟨⟨β, h1⟩, -, h3⟩
      · constructor
        · intro hi; exact absurd h2 hi
        · intro hi; simp [FEnv.ofEnv, FEnv.minenv, hi] at h1
      · have : i < Γ.length := by
          by_contra hc; rw [List.getElem?_eq_none (by simp; omega)] at h1; simp at h1
        simp only [fv, Set.mem_setOf_eq, h3]; simpa using this
    refine ⟨⟨h.quasiLinear, fun i j hi hj => (hfv j).2 (by have := (hfv i).1 hi; omega)⟩,
      ⟨fun n hn => (hfv n).2 (by omega), fun i hi => (hfv i).1 hi⟩,
      h.toST_of_le Γ (FEnv.le_refl _)⟩
  · rintro ⟨hlin, ⟨hmin₁, hmin₂⟩, hst⟩
    obtain ⟨Δ, hΔ⟩ := hst.toLL hlin.1
    have hfv : ∀ i, i ∈ t.fv ↔ i < Γ.length := by
      intro i
      refine ⟨hmin₂ i, fun hi => ?_⟩
      obtain ⟨n, hn⟩ : ∃ n, Γ.length = n + 1 := ⟨Γ.length - 1, by omega⟩
      rcases Nat.lt_or_ge i n with h | h
      · exact hlin.2 n i (hmin₁ n hn) h
      · rw [show i = n by omega]; exact hmin₁ n hn
    rw [← key Δ hΔ hfv]; exact hΔ

/-! ### Lemma `envarith` -/

/-- Lemma `envarith` (a): if `⊢_ll {Γ} t : α {Δ}` and `Γ + Θ` is defined, then `Δ + Θ` is
defined and `⊢_ll {Γ + Θ} t : α {Δ + Θ}`. -/
theorem LLTyped.add_env {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) {Θ Γ' : FEnv A} (hΓ' : FEnv.add Γ Θ = some Γ') :
    ∃ Δ', FEnv.add Δ Θ = some Δ' ∧ LLTyped τ Γ' t α Δ' := by
  induction h generalizing Θ Γ' with
  | const Γ c => exact ⟨Γ', hΓ', LLTyped.const _ c⟩
  | var Γ α =>
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.add] at hΓ'
    obtain ⟨c, G, hc, hG, rfl⟩ := FEnv.add_cons_cons_eq_some.1 hΓ'
    rcases θ with _ | θ <;> simp [QTy.add] at hc
    subst hc
    exact ⟨none :: G, by simp [hG, QTy.add], LLTyped.var G α⟩
  | weak₁ β _ ih =>
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.add] at hΓ'
    obtain ⟨c, G, hc, hG, rfl⟩ := FEnv.add_cons_cons_eq_some.1 hΓ'
    rcases θ with _ | θ <;> simp [QTy.add] at hc
    subst hc
    obtain ⟨D, hD, hD'⟩ := ih hG
    exact ⟨some β :: D, by simp [hD, QTy.add], LLTyped.weak₁ β hD'⟩
  | weak₂ _ ih =>
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.add] at hΓ'
    obtain ⟨c, G, hc, hG, rfl⟩ := FEnv.add_cons_cons_eq_some.1 hΓ'
    simp [QTy.add] at hc
    subst hc
    obtain ⟨D, hD, hD'⟩ := ih hG
    rcases θ with _ | θ
    · exact ⟨none :: D, by simp [hD, QTy.add], LLTyped.weak₂ hD'⟩
    · exact ⟨some θ :: D, by simp [hD, QTy.add], LLTyped.weak₁ θ hD'⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨D, hD, hD'⟩ := ih₁ hΓ'
    obtain ⟨E, hE, hE'⟩ := ih₂ hD
    exact ⟨E, hE, LLTyped.app hD' hE'⟩
  | @abs Γ Δ t α β _ ih =>
    obtain ⟨D, hD, hD'⟩ := ih (Θ := none :: Θ) (Γ' := some α :: Γ') (by simp [hΓ', QTy.add])
    obtain ⟨d, D₀, hd, hD₀, hDeq⟩ := FEnv.add_cons_cons_eq_some.1 hD
    subst hDeq
    simp [QTy.add] at hd
    subst hd
    exact ⟨D₀, hD₀, LLTyped.abs hD'⟩

/-- Lemma `envarith` (b): if `⊢_ll {Γ} t : α {Δ}` and `Δ - Θ` is defined, then `Γ - Θ` is
defined and `⊢_ll {Γ - Θ} t : α {Δ - Θ}`. -/
theorem LLTyped.sub_env [DecidableEq A] {τ : C → Ty A} {Γ Δ : FEnv A} {t : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) {Θ Δ' : FEnv A} (hΔ' : FEnv.sub Δ Θ = some Δ') :
    ∃ Γ', FEnv.sub Γ Θ = some Γ' ∧ LLTyped τ Γ' t α Δ' := by
  induction h generalizing Θ Δ' with
  | const Γ c => exact ⟨Δ', hΔ', LLTyped.const _ c⟩
  | var Γ α =>
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.sub] at hΔ'
    obtain ⟨c, G, hc, hG, rfl⟩ := FEnv.sub_cons_cons_eq_some.1 hΔ'
    rcases θ with _ | θ <;> simp [QTy.sub] at hc
    subst hc
    exact ⟨some α :: G, by simp [hG, QTy.sub], LLTyped.var G α⟩
  | weak₁ β _ ih =>
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.sub] at hΔ'
    obtain ⟨c, G, hc, hG, rfl⟩ := FEnv.sub_cons_cons_eq_some.1 hΔ'
    obtain ⟨D, hD, hD'⟩ := ih hG
    rcases θ with _ | θ
    · simp [QTy.sub] at hc
      subst hc
      exact ⟨some β :: D, by simp [hD, QTy.sub], LLTyped.weak₁ β hD'⟩
    · simp only [QTy.sub] at hc
      split_ifs at hc with hβ
      · simp at hc
        subst hc hβ
        exact ⟨none :: D, by simp [hD, QTy.sub], LLTyped.weak₂ hD'⟩
  | weak₂ _ ih =>
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.sub] at hΔ'
    obtain ⟨c, G, hc, hG, rfl⟩ := FEnv.sub_cons_cons_eq_some.1 hΔ'
    rcases θ with _ | θ <;> simp [QTy.sub] at hc
    subst hc
    obtain ⟨D, hD, hD'⟩ := ih hG
    exact ⟨none :: D, by simp [hD, QTy.sub], LLTyped.weak₂ hD'⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨D, hD, hD'⟩ := ih₂ hΔ'
    obtain ⟨E, hE, hE'⟩ := ih₁ hD
    exact ⟨E, hE, LLTyped.app hE' hD'⟩
  | @abs Γ Δ t α β _ ih =>
    obtain ⟨G, hG, hG'⟩ := ih (Θ := none :: Θ) (Δ' := none :: Δ') (by simp [hΔ', QTy.sub])
    obtain ⟨g, G₀, hg, hG₀, hGeq⟩ := FEnv.sub_cons_cons_eq_some.1 hG
    subst hGeq
    simp [QTy.sub] at hg
    subst hg
    exact ⟨G₀, hG₀, LLTyped.abs hG'⟩

end LinearDB
