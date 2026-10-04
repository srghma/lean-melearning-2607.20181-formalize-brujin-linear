module

public import RequestProject.Sec4LinearTyping.LL
public import RequestProject.Sec5BetaReduction.Beta

/-!
# Inversion lemmas for the `ll` typing system and auxiliary facts on environments

These technical results are used in the proof of subject reduction.
-/

@[expose] public section

namespace LinearDB

open Term

variable {A C : Type*} {τ : C → Ty A}

/-! ### Inversion lemmas -/

theorem LLTyped.const_inv {Γ Δ : FEnv A} {c : C} {α : Ty A}
    (h : LLTyped τ Γ (.const c) α Δ) : α = τ c ∧ Δ = Γ := by
  cases h; exact ⟨rfl, rfl⟩

theorem LLTyped.app_inv {Γ Θ : FEnv A} {t u : Term C} {β : Ty A}
    (h : LLTyped τ Γ (.app t u) β Θ) :
    ∃ α Δ, LLTyped τ Γ t (.arr α β) Δ ∧ LLTyped τ Δ u α Θ := by
  cases h with
  | app h₁ h₂ => exact ⟨_, _, h₁, h₂⟩

theorem LLTyped.lam_inv {Γ Δ : FEnv A} {t : Term C} {γ : Ty A}
    (h : LLTyped τ Γ (.lam t) γ Δ) :
    ∃ α β, γ = .arr α β ∧ LLTyped τ (some α :: Γ) t β (none :: Δ) := by
  cases h with
  | abs h => exact ⟨_, _, rfl, h⟩

/-- Pointwise description of the judgements `{Γ} j : α {Δ}` for an index `j`:
`Γ(j) = α`, `Δ(j) = ⊥`, and `Γ` and `Δ` agree everywhere else. -/
def VarSpec (Γ : FEnv A) (j : ℕ) (α : Ty A) (Δ : FEnv A) : Prop :=
  Γ[j]? = some (some α) ∧ Δ[j]? = some none ∧ ∀ m, m ≠ j → Γ[m]? = Δ[m]?

theorem LLTyped.var_iff {Γ Δ : FEnv A} {j : ℕ} {α : Ty A} :
    LLTyped τ Γ (.var j) α Δ ↔ VarSpec Γ j α Δ := by
  constructor
  · intro h
    generalize ht : (Term.var j : Term C) = t at h
    induction h generalizing j with
    | const => cases ht
    | var Γ α =>
      cases ht
      refine ⟨rfl, rfl, fun m hm => ?_⟩
      rcases m with _ | m
      · omega
      · rfl
    | weak₁ β _ ih =>
      cases ht
      obtain ⟨h1, h2, h3⟩ := ih rfl
      refine ⟨h1, h2, fun m hm => ?_⟩
      rcases m with _ | m
      · rfl
      · simpa using h3 m (by omega)
    | weak₂ _ ih =>
      cases ht
      obtain ⟨h1, h2, h3⟩ := ih rfl
      refine ⟨h1, h2, fun m hm => ?_⟩
      rcases m with _ | m
      · rfl
      · simpa using h3 m (by omega)
    | app => cases ht
    | abs => cases ht
  · rintro ⟨h1, h2, h3⟩
    induction j generalizing Γ Δ with
    | zero =>
      rcases Γ with _ | ⟨g, Γ⟩
      · simp at h1
      rcases Δ with _ | ⟨d, Δ⟩
      · simp at h2
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2
      subst h1 h2
      have : Γ = Δ := List.ext_getElem? fun m => by simpa using h3 (m + 1) (by omega)
      subst this
      exact LLTyped.var Γ α
    | succ j ih =>
      rcases Γ with _ | ⟨g, Γ⟩
      · simp at h1
      rcases Δ with _ | ⟨d, Δ⟩
      · simp at h2
      simp only [List.getElem?_cons_succ] at h1 h2
      have hgd : g = d := by simpa using h3 0 (by omega)
      subst hgd
      have := ih h1 h2 (fun m hm => by simpa using h3 (m + 1) (by omega))
      rcases g with _ | g
      · exact LLTyped.weak₂ this
      · exact LLTyped.weak₁ g this

/-! ### Index arithmetic in concatenated environments -/

section Index

variable {α : Type*} {l₁ l₂ l₃ : List α} {x : α} {i m : ℕ}

lemma getElem?_app_lt (h : l₁.length = i) (hm : m < i) : (l₁ ++ l₂)[m]? = l₁[m]? :=
  List.getElem?_append_left (by omega)

lemma getElem?_app_ge (h : l₁.length = i) (hm : i ≤ m) : (l₁ ++ l₂)[m]? = l₂[m - i]? := by
  rw [List.getElem?_append_right (by omega), h]

lemma getElem?_mid_eq (h : l₁.length = i) : (l₁ ++ x :: l₂)[i]? = some x := by
  rw [getElem?_app_ge h le_rfl]; simp

lemma getElem?_mid_succ (h : l₁.length = i) (hm : i ≤ m) :
    (l₁ ++ x :: l₂)[m + 1]? = l₂[m - i]? := by
  rw [getElem?_app_ge h (by omega), show m + 1 - i = (m - i) + 1 by omega,
    List.getElem?_cons_succ]

end Index

/-! ### Splitting environments -/

lemma FEnv.le_split_mid {ω : QTy A} {Γ₁ Γ₂ Δ₁ Δ₂ Ξ : FEnv A}
    (hΔ : FEnv.le (Δ₂ ++ ω :: Δ₁) Ξ) (hΓ : FEnv.le Ξ (Γ₂ ++ ω :: Γ₁))
    (hl : Γ₂.length = Δ₂.length) :
    ∃ Ξ₂ Ξ₁, Ξ = Ξ₂ ++ ω :: Ξ₁ ∧ Ξ₂.length = Γ₂.length ∧
      FEnv.le Δ₁ Ξ₁ ∧ FEnv.le Ξ₁ Γ₁ := by
  induction Γ₂ generalizing Δ₂ Ξ with
  | nil =>
    rcases Δ₂ with _ | ⟨d, Δ₂⟩
    · obtain ⟨ξ, Ξ₁, rfl, h1, h2⟩ := FEnv.le_cons_left hΔ
      obtain ⟨h3, h4⟩ := FEnv.le_cons_cons.1 hΓ
      have : ξ = ω := by
        rcases h1 with rfl | rfl <;> rcases h3 with h3 | h3 <;> first | rfl | exact h3
      subst this
      exact ⟨[], Ξ₁, rfl, rfl, h2, h4⟩
    · simp at hl
  | cons g Γ₂ ih =>
    rcases Δ₂ with _ | ⟨d, Δ₂⟩
    · simp at hl
    · obtain ⟨ξ, Ξ', rfl, -, h2⟩ := FEnv.le_cons_left hΔ
      obtain ⟨-, h4⟩ := FEnv.le_cons_cons.1 hΓ
      obtain ⟨Ξ₂, Ξ₁, rfl, h5, h6, h7⟩ := ih h2 h4 (by simpa using hl)
      exact ⟨ξ :: Ξ₂, Ξ₁, rfl, by simp [h5], h6, h7⟩

lemma FEnv.List.zipWithExactM_append {f : QTy A → QTy A → Option (QTy A)} {A₁ A₂ B₁ B₂ X Y : FEnv A}
    (h₁ : List.zipWithExactM f A₁ B₁ = some X) (h₂ : List.zipWithExactM f A₂ B₂ = some Y) :
    List.zipWithExactM f (A₁ ++ A₂) (B₁ ++ B₂) = some (X ++ Y) := by
  induction A₁ generalizing B₁ X with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (FEnv.List.zipWithExactM_nil_left_eq_some f).1 h₁
    simpa using h₂
  | cons a A₁ ih =>
    rcases B₁ with _ | ⟨b, B₁⟩
    · simp at h₁
    obtain ⟨c, X', hc, hX', rfl⟩ := (FEnv.List.zipWithExactM_cons_cons_eq_some f).1 h₁
    rw [List.cons_append, List.cons_append, FEnv.List.zipWithExactM_cons_cons_eq_some]
    exact ⟨c, X' ++ Y, hc, ih hX', rfl⟩

lemma FEnv.List.zipWithExactM_append_inv {f : QTy A → QTy A → Option (QTy A)} {A₁ A₂ B₁ B₂ W : FEnv A}
    (h : List.zipWithExactM f (A₁ ++ A₂) (B₁ ++ B₂) = some W) (hl : A₁.length = B₁.length) :
    ∃ X Y, W = X ++ Y ∧ List.zipWithExactM f A₁ B₁ = some X ∧ List.zipWithExactM f A₂ B₂ = some Y := by
  induction A₁ generalizing B₁ W with
  | nil =>
    rcases B₁ with _ | ⟨b, B₁⟩
    · exact ⟨[], W, rfl, rfl, by simpa using h⟩
    · simp at hl
  | cons a A₁ ih =>
    rcases B₁ with _ | ⟨b, B₁⟩
    · simp at hl
    rw [List.cons_append, List.cons_append, FEnv.List.zipWithExactM_cons_cons_eq_some] at h
    obtain ⟨c, W', hc, hW', rfl⟩ := h
    obtain ⟨X, Y, rfl, hX, hY⟩ := ih hW' (by simpa using hl)
    exact ⟨c :: X, Y, rfl, by simp [List.zipWithExactM, hc, hX], hY⟩

/-! ### Definedness facts -/

lemma FEnv.sub_isSome_of_le' [DecidableEq A] {Δ Ξ : FEnv A} (h : FEnv.le Δ Ξ) :
    ∃ X, FEnv.sub Ξ Δ = some X := by
  unfold FEnv.le at h
  induction h with
  | nil => exact ⟨[], rfl⟩
  | @cons d x Δ Ξ hdx _ ih =>
    obtain ⟨X, hX⟩ := ih
    rcases hdx with rfl | rfl
    · exact ⟨x :: X, by simp [hX, QTy.sub]⟩
    · rcases d with _ | d
      · exact ⟨none :: X, by simp [hX, QTy.sub]⟩
      · exact ⟨none :: X, by simp [hX, QTy.sub]⟩

lemma FEnv.add_sub_isSome [DecidableEq A] {Δ Ξ X : FEnv A} (h : FEnv.le Δ Ξ)
    (hX : FEnv.sub Ξ Δ = some X) : ∃ L, FEnv.add Δ X = some L := by
  unfold FEnv.le at h
  induction h generalizing X with
  | nil => rw [show X = [] by simpa [FEnv.sub] using hX.symm]; exact ⟨[], rfl⟩
  | @cons d x Δ Ξ hdx _ ih =>
    obtain ⟨c, X', hc, hX', rfl⟩ := FEnv.sub_cons_cons_eq_some.1 hX
    obtain ⟨L, hL⟩ := ih hX'
    rcases hdx with rfl | rfl
    · exact ⟨c :: L, by simp [hL, QTy.add]⟩
    · rcases d with _ | d
      · exact ⟨c :: L, by simp [hL, QTy.add]⟩
      · simp [QTy.sub] at hc
        subst hc
        exact ⟨some d :: L, by simp [hL, QTy.add]⟩

lemma FEnv.sub_sub_isSome [DecidableEq A] {Θ Δ Y : FEnv A} (h : FEnv.le Θ Δ)
    (hY : FEnv.sub Δ Θ = some Y) : ∃ R, FEnv.sub Δ Y = some R := by
  unfold FEnv.le at h
  induction h generalizing Y with
  | nil => rw [show Y = [] by simpa [FEnv.sub] using hY.symm]; exact ⟨[], rfl⟩
  | @cons θ d Θ Δ hθd _ ih =>
    obtain ⟨c, Y', hc, hY', rfl⟩ := FEnv.sub_cons_cons_eq_some.1 hY
    obtain ⟨R, hR⟩ := ih hY'
    rcases hθd with rfl | rfl
    · simp [QTy.sub] at hc
      subst hc
      rcases d with _ | d
      · exact ⟨none :: R, by simp [hR, QTy.sub]⟩
      · exact ⟨none :: R, by simp [hR, QTy.sub]⟩
    · rcases θ with _ | θ
      · simp [QTy.sub] at hc
        subst hc
        exact ⟨none :: R, by simp [hR, QTy.sub]⟩
      · simp [QTy.sub] at hc
        subst hc
        exact ⟨some θ :: R, by simp [hR, QTy.sub]⟩

lemma FEnv.sub_minenv [DecidableEq A] (Γ : FEnv A) :
    FEnv.sub Γ (FEnv.minenv Γ.length) = some Γ := by
  induction Γ with
  | nil => rfl
  | cons g Γ ih =>
    change FEnv.sub (g :: Γ) (none :: FEnv.minenv Γ.length) = some (g :: Γ)
    rw [FEnv.sub_cons_cons_some_iff]
    exact ⟨by cases g <;> rfl, ih⟩

end LinearDB
