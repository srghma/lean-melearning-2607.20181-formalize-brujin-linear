module

public import RequestProject.Inversion

/-!
# Subject reduction (Section 6 of the paper)

* `LLTyped.subst_of_not_occ` — Lemma `l3` (substitution for a variable that does not occur);
* `LLTyped.lift_env`         — Lemma `philippe` (lifting);
* `LLTyped.subst_lemma`      — Lemma `sr` (the substitution lemma);
* `LLTyped.subject_reduction` — the subject reduction property for β-contraction;
* `LLTyped.subject_reduction_star` — its extension to β-reduction.
-/

@[expose] public section

namespace LinearDB

open Term

variable {A C : Type*} {τ : C → Ty A}

private lemma exists_split_at {α : Type*} {l : List α} {i : ℕ} (h : i < l.length) :
    ∃ l₂ x l₁, l = l₂ ++ x :: l₁ ∧ l₂.length = i := by
  refine ⟨l.take i, l[i], l.drop (i + 1), ?_, by simp; omega⟩
  rw [List.getElem_cons_drop, List.take_append_drop]

private lemma le_append_cons_inv {A₂ A₁ B₂ B₁ : FEnv A} {a b : QTy A}
    (h : FEnv.le (A₂ ++ a :: A₁) (B₂ ++ b :: B₁)) (hl : A₂.length = B₂.length) :
    QTy.le a b ∧ FEnv.le A₁ B₁ := by
  induction A₂ generalizing B₂ with
  | nil =>
    rcases B₂ with _ | ⟨b', B₂⟩
    · exact FEnv.le_cons_cons.1 h
    · simp at hl
  | cons a' A₂ ih =>
    rcases B₂ with _ | ⟨b', B₂⟩
    · simp at hl
    · exact ih (FEnv.le_cons_cons.1 h).2 (by simpa using hl)

/-- Lemma `l3`: if `|Γ₂| = |Δ₂| = i` and `⊢_ll {Γ₁, ω, Γ₂} t : α {Δ₁, ω, Δ₂}`, then
`⊢_ll {Γ₁, Γ₂} t[i := u] : α {Δ₁, Δ₂}`. -/
theorem LLTyped.subst_of_not_occ {ω : QTy A} {u : Term C} :
    ∀ {t : Term C} {Γ₁ Γ₂ Δ₁ Δ₂ : FEnv A} {α : Ty A} {i : ℕ},
      Γ₂.length = i → Δ₂.length = i →
      LLTyped τ (Γ₂ ++ ω :: Γ₁) t α (Δ₂ ++ ω :: Δ₁) →
      LLTyped τ (Γ₂ ++ Γ₁) (t.subst i u) α (Δ₂ ++ Δ₁) := by
  intro t
  induction t with
  | const c =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ α i hΓ hΔ h
    obtain ⟨rfl, he⟩ := h.const_inv
    obtain ⟨rfl, he'⟩ := List.append_inj he (by omega)
    cases he'
    exact LLTyped.const _ c
  | var j =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ α i hΓ hΔ h
    obtain ⟨h1, h2, h3⟩ := LLTyped.var_iff.1 h
    rcases lt_trichotomy j i with hj | rfl | hj
    · have hs : (Term.var j : Term C).subst i u = .var j := by simp [subst, hj]
      rw [hs]
      refine LLTyped.var_iff.2 ⟨?_, ?_, fun m hm => ?_⟩
      · rwa [getElem?_app_lt hΓ hj] at h1 ⊢
      · rwa [getElem?_app_lt hΔ hj] at h2 ⊢
      · rcases lt_or_ge m i with hmi | hmi
        · have := h3 m hm
          rwa [getElem?_app_lt hΓ hmi, getElem?_app_lt hΔ hmi] at this ⊢
        · have := h3 (m + 1) (by omega)
          rwa [getElem?_mid_succ hΓ hmi, getElem?_mid_succ hΔ hmi, ← getElem?_app_ge hΓ hmi,
            ← getElem?_app_ge hΔ hmi] at this
    · rw [getElem?_mid_eq hΓ] at h1
      rw [getElem?_mid_eq hΔ] at h2
      rw [h1] at h2; simp at h2
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hs : (Term.var (j + 1) : Term C).subst i u = .var j := by
        simp only [subst]; rw [if_neg (by omega), if_neg (by omega)]; rfl
      rw [hs]
      refine LLTyped.var_iff.2 ⟨?_, ?_, fun m hm => ?_⟩
      · rwa [getElem?_mid_succ hΓ (by omega), ← getElem?_app_ge hΓ (by omega)] at h1
      · rwa [getElem?_mid_succ hΔ (by omega), ← getElem?_app_ge hΔ (by omega)] at h2
      · rcases lt_or_ge m i with hmi | hmi
        · have := h3 m (by omega)
          rwa [getElem?_app_lt hΓ hmi, getElem?_app_lt hΔ hmi] at this ⊢
        · have := h3 (m + 1) (by omega)
          rwa [getElem?_mid_succ hΓ hmi, getElem?_mid_succ hΔ hmi, ← getElem?_app_ge hΓ hmi,
            ← getElem?_app_ge hΔ hmi] at this
  | app t₁ t₂ ih₁ ih₂ =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ α i hΓ hΔ h
    obtain ⟨γ, Ξ, h₁, h₂⟩ := h.app_inv
    obtain ⟨Ξ₂, Ξ₁, rfl, hΞ, -, -⟩ := FEnv.le_split_mid h₂.le h₁.le (by omega)
    exact LLTyped.app (ih₁ hΓ (by omega) h₁) (ih₂ (by omega) hΔ h₂)
  | lam t ih =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ α i hΓ hΔ h
    obtain ⟨α₁, α₂, rfl, h'⟩ := h.lam_inv
    exact LLTyped.abs (ih (Γ₂ := some α₁ :: Γ₂) (Δ₂ := none :: Δ₂)
      (by simp [hΓ]) (by simp [hΔ]) h')

/-- Lemma `philippe` (lifting): if `|Γ₂| = |Δ₂| = i` and `⊢_ll {Γ₁, Γ₂} t : α {Δ₁, Δ₂}`, then
`⊢_ll {Γ₁, Θ, Γ₂} ↑^{|Θ|}_i(t) : α {Δ₁, Θ, Δ₂}`. -/
theorem LLTyped.lift_env {Θ : FEnv A} :
    ∀ {t : Term C} {Γ₁ Γ₂ Δ₁ Δ₂ : FEnv A} {α : Ty A} {i : ℕ},
      Γ₂.length = i → Δ₂.length = i →
      LLTyped τ (Γ₂ ++ Γ₁) t α (Δ₂ ++ Δ₁) →
      LLTyped τ (Γ₂ ++ (Θ ++ Γ₁)) (t.lift Θ.length i) α (Δ₂ ++ (Θ ++ Δ₁)) := by
  intro t
  induction t with
  | const c =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ α i hΓ hΔ h
    obtain ⟨rfl, he⟩ := h.const_inv
    obtain ⟨rfl, rfl⟩ := List.append_inj he (by omega)
    exact LLTyped.const _ c
  | var j =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ α i hΓ hΔ h
    obtain ⟨h1, h2, h3⟩ := LLTyped.var_iff.1 h
    -- lookups in the environment extended by `Θ` at position `i`
    have key : ∀ (L₂ L₁ : FEnv A), L₂.length = i → ∀ m, i + Θ.length ≤ m →
        (L₂ ++ (Θ ++ L₁))[m]? = (L₂ ++ L₁)[m - Θ.length]? := by
      intro L₂ L₁ hL m hm
      rw [getElem?_app_ge hL (by omega), getElem?_app_ge hL (by omega),
        getElem?_app_ge rfl (by omega), show m - i - Θ.length = m - Θ.length - i by omega]
    have mid : ∀ (L₂ L₁ : FEnv A), L₂.length = i → ∀ m, i ≤ m → m < i + Θ.length →
        (L₂ ++ (Θ ++ L₁))[m]? = Θ[m - i]? := by
      intro L₂ L₁ hL m hm hm'
      rw [getElem?_app_ge hL hm, getElem?_app_lt rfl (by omega)]
    by_cases hj : j < i
    · have hs : (Term.var j : Term C).lift Θ.length i = .var j := by simp [lift, hj]
      rw [hs]
      refine LLTyped.var_iff.2 ⟨?_, ?_, fun m hm => ?_⟩
      · rwa [getElem?_app_lt hΓ hj] at h1 ⊢
      · rwa [getElem?_app_lt hΔ hj] at h2 ⊢
      · rcases lt_or_ge m i with hmi | hmi
        · have := h3 m hm
          rwa [getElem?_app_lt hΓ hmi, getElem?_app_lt hΔ hmi] at this ⊢
        · rcases lt_or_ge m (i + Θ.length) with hmk | hmk
          · rw [mid _ _ hΓ m hmi hmk, mid _ _ hΔ m hmi hmk]
          · rw [key _ _ hΓ m hmk, key _ _ hΔ m hmk]
            exact h3 _ (by omega)
    · have hs : (Term.var j : Term C).lift Θ.length i = .var (j + Θ.length) := by
        simp [lift, hj]
      rw [hs]
      refine LLTyped.var_iff.2 ⟨?_, ?_, fun m hm => ?_⟩
      · rw [key _ _ hΓ _ (by omega), Nat.add_sub_cancel]; exact h1
      · rw [key _ _ hΔ _ (by omega), Nat.add_sub_cancel]; exact h2
      · rcases lt_or_ge m i with hmi | hmi
        · have := h3 m (by omega)
          rwa [getElem?_app_lt hΓ hmi, getElem?_app_lt hΔ hmi] at this ⊢
        · rcases lt_or_ge m (i + Θ.length) with hmk | hmk
          · rw [mid _ _ hΓ m hmi hmk, mid _ _ hΔ m hmi hmk]
          · rw [key _ _ hΓ m hmk, key _ _ hΔ m hmk]
            exact h3 _ (by omega)
  | app t₁ t₂ ih₁ ih₂ =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ α i hΓ hΔ h
    obtain ⟨γ, Ξ, h₁, h₂⟩ := h.app_inv
    have hlen : i ≤ Ξ.length := by have := h₁.length_eq; simp at this; omega
    rw [← List.take_append_drop i Ξ] at h₁ h₂
    have ht : (Ξ.take i).length = i := by simp; omega
    exact LLTyped.app (ih₁ hΓ ht h₁) (ih₂ ht hΔ h₂)
  | lam t ih =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ α i hΓ hΔ h
    obtain ⟨α₁, α₂, rfl, h'⟩ := h.lam_inv
    exact LLTyped.abs (ih (Γ₂ := some α₁ :: Γ₂) (Δ₂ := none :: Δ₂)
      (by simp [hΓ]) (by simp [hΔ]) h')

/-- Lemma `sr` (the substitution lemma): if `|Γ₂| = |Δ₂| = i`,
`⊢_ll {Γ₁, β, Γ₂} t : α {Δ₁, ⊥, Δ₂}` and `⊢_ll {Δ₁} u : β {Θ}`, then
`⊢_ll {Γ₁, Γ₂} t[i := u] : α {Θ, Δ₂}`. -/
theorem LLTyped.subst_lemma {u : Term C} {β : Ty A} :
    ∀ {t : Term C} {Γ₁ Γ₂ Δ₁ Δ₂ Θ : FEnv A} {α : Ty A} {i : ℕ},
      Γ₂.length = i → Δ₂.length = i →
      LLTyped τ (Γ₂ ++ some β :: Γ₁) t α (Δ₂ ++ none :: Δ₁) →
      LLTyped τ Δ₁ u β Θ →
      LLTyped τ (Γ₂ ++ Γ₁) (t.subst i u) α (Δ₂ ++ Θ) := by
  classical
  intro t
  induction t with
  | const c =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ Θ α i hΓ hΔ h _
    obtain ⟨-, he⟩ := h.const_inv
    obtain ⟨-, he'⟩ := List.append_inj he (by omega)
    simp at he'
  | var j =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ Θ α i hΓ hΔ h hu
    obtain ⟨h1, h2, h3⟩ := LLTyped.var_iff.1 h
    have hji : j = i := by
      by_contra hne
      have := h3 i (Ne.symm hne)
      rw [getElem?_mid_eq hΓ, getElem?_mid_eq hΔ] at this
      simp at this
    subst hji
    rw [getElem?_mid_eq hΓ] at h1
    simp only [Option.some.injEq] at h1
    subst h1
    have e₂ : Γ₂ = Δ₂ := by
      apply List.ext_getElem?
      intro m
      rcases lt_or_ge m j with hm | hm
      · have := h3 m (by omega)
        rwa [getElem?_app_lt hΓ hm, getElem?_app_lt hΔ hm] at this
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    have e₁ : Γ₁ = Δ₁ := by
      apply List.ext_getElem?
      intro m
      have := h3 (j + m + 1) (by omega)
      rwa [getElem?_mid_succ hΓ (by omega), getElem?_mid_succ hΔ (by omega),
        show j + m - j = m by omega] at this
    subst e₂ e₁
    have hs : (Term.var j : Term C).subst j u = u.lift j 0 := by simp [subst]
    rw [hs, ← hΓ]
    exact LLTyped.lift_env (Θ := Γ₂) (Γ₂ := []) (Δ₂ := []) rfl rfl hu
  | app t₁ t₂ ih₁ ih₂ =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ Θ α i hΓ hΔ h hu
    obtain ⟨γ, Ξ, h₁, h₂⟩ := h.app_inv
    have hlen : i < Ξ.length := by have := h₁.length_eq; simp at this; omega
    obtain ⟨Ξ₂, ξ, Ξ₁, rfl, hΞ⟩ := exists_split_at hlen
    obtain ⟨hξ, -⟩ := le_append_cons_inv h₁.le (by omega)
    obtain ⟨-, hle₁⟩ := le_append_cons_inv h₂.le (by omega)
    rcases hξ with rfl | rfl
    · -- the index `i` occurs in `t₁`
      obtain ⟨X, hX⟩ := FEnv.sub_isSome_of_le' hle₁
      obtain ⟨L, hL⟩ := FEnv.add_sub_isSome hle₁ hX
      have hLe : L = Ξ₁ := FEnv.simpleEq_b hX hL
      subst hLe
      obtain ⟨Θ', hΘ', hu'⟩ := hu.add_env hL
      have p₁ := ih₁ hΓ hΞ h₁ hu'
      have p₂ := LLTyped.subst_of_not_occ (u := u) hΞ hΔ h₂
      obtain ⟨Y, hY⟩ := FEnv.sub_isSome_of_le' hu.le
      obtain ⟨R, hR⟩ := FEnv.sub_sub_isSome hu.le hY
      have hRe : R = Θ := FEnv.simpleEq_c hY hR
      subst hRe
      have hsub : FEnv.sub (Δ₂ ++ Δ₁) (FEnv.minenv i ++ Y) = some (Δ₂ ++ R) := by
        have := FEnv.sub_minenv Δ₂
        rw [hΔ] at this
        exact FEnv.zipOp_append this hR
      obtain ⟨G, hG, p₂'⟩ := p₂.sub_env hsub
      obtain ⟨G₂, G₁, rfl, hG₂, hG₁⟩ := FEnv.zipOp_append_inv hG (by simp [hΞ])
      have hG₂' := FEnv.sub_minenv Ξ₂
      rw [hΞ] at hG₂'
      have : G₂ = Ξ₂ := Option.some.inj (hG₂.symm.trans hG₂')
      subst this
      have : Θ' = G₁ := FEnv.simpleEq_a hX hΘ' hY hG₁
      subst this
      exact LLTyped.app p₁ p₂'
    · -- the index `i` occurs in `t₂`
      exact LLTyped.app (LLTyped.subst_of_not_occ hΓ hΞ h₁) (ih₂ hΞ hΔ h₂ hu)
  | lam t ih =>
    intro Γ₁ Γ₂ Δ₁ Δ₂ Θ α i hΓ hΔ h hu
    obtain ⟨α₁, α₂, rfl, h'⟩ := h.lam_inv
    exact LLTyped.abs (ih (Γ₂ := some α₁ :: Γ₂) (Δ₂ := none :: Δ₂)
      (by simp [hΓ]) (by simp [hΔ]) h' hu)

/-- **Subject reduction**: if `⊢_ll {Γ} t : α {Δ}` and `t →β u`, then `⊢_ll {Γ} u : α {Δ}`. -/
theorem LLTyped.subject_reduction {Γ Δ : FEnv A} {t u : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) (hb : Beta t u) : LLTyped τ Γ u α Δ := by
  induction hb generalizing Γ Δ α with
  | beta t u =>
    obtain ⟨β, Θ, h₁, h₂⟩ := h.app_inv
    obtain ⟨β', α', he, h₁'⟩ := h₁.lam_inv
    cases he
    exact LLTyped.subst_lemma (Γ₂ := []) (Δ₂ := []) rfl rfl h₁' h₂
  | appL v _ ih =>
    obtain ⟨β, Θ, h₁, h₂⟩ := h.app_inv
    exact LLTyped.app (ih h₁) h₂
  | appR v _ ih =>
    obtain ⟨β, Θ, h₁, h₂⟩ := h.app_inv
    exact LLTyped.app h₁ (ih h₂)
  | lam _ ih =>
    obtain ⟨a, b, rfl, h₁⟩ := h.lam_inv
    exact LLTyped.abs (ih h₁)

/-- Subject reduction for β-reduction (the reflexive, transitive closure of β-contraction). -/
theorem LLTyped.subject_reduction_star {Γ Δ : FEnv A} {t u : Term C} {α : Ty A}
    (h : LLTyped τ Γ t α Δ) (hb : BetaRed t u) : LLTyped τ Γ u α Δ := by
  induction hb with
  | refl => exact h
  | tail _ hb ih => exact ih.subject_reduction hb

end LinearDB
