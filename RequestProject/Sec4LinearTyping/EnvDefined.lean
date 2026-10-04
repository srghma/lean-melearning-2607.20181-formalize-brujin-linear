module

public import RequestProject.Sec3FragmentaryEnv.FEnvLemmas

/-!
# Lemma `envdefined` (end of Section 4 of the paper)
-/

@[expose] public section

namespace LinearDB.FEnv

variable {A : Type*}

/-- Lemma `envdefined` (a): if `Δ ⊑ Γ` and `Γ + Θ` is defined, then `Δ + Θ` is defined. -/
theorem add_isSome_of_le {Γ Δ Θ : FEnv A} (h : le Δ Γ) (hΓ : (add Γ Θ).isSome) :
    (add Δ Θ).isSome := by
  unfold le at h
  induction h generalizing Θ with
  | nil => exact hΓ
  | @cons d g Δ Γ hdg _ ih =>
    cases Θ with
    | nil => simp [add] at hΓ
    | cons θ Θ =>
      obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1 hΓ
      obtain ⟨c, X', hc, hX', rfl⟩ := (List.zipWithExactM_cons_cons_eq_some _).1 hX
      obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 (ih (Θ := Θ) (by simp [add, hX']))
      rcases hdg with rfl | rfl
      · simp [add, List.zipWithExactM, QTy.add, show List.zipWithExactM QTy.add Δ Θ = some Y from hY]
      · simp [add, List.zipWithExactM, hc, show List.zipWithExactM QTy.add Δ Θ = some Y from hY]

/-- Lemma `envdefined` (b): if `Δ ⊑ Γ` and `Θ - Γ` is defined, then `Θ - Δ` is defined. -/
theorem sub_isSome_of_le [DecidableEq A] {Γ Δ Θ : FEnv A} (h : le Δ Γ)
    (hΓ : (sub Θ Γ).isSome) : (sub Θ Δ).isSome := by
  unfold le at h
  induction h generalizing Θ with
  | nil => exact hΓ
  | @cons d g Δ Γ hdg _ ih =>
    cases Θ with
    | nil => simp [sub] at hΓ
    | cons θ Θ =>
      obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1 hΓ
      obtain ⟨c, X', hc, hX', rfl⟩ := (List.zipWithExactM_cons_cons_eq_some _).1 hX
      obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 (ih (Θ := Θ) (by simp [sub, hX']))
      rcases hdg with rfl | rfl
      · cases θ <;> simp [sub, List.zipWithExactM, QTy.sub, show List.zipWithExactM QTy.sub Θ Δ = some Y from hY]
      · simp [sub, List.zipWithExactM, hc, show List.zipWithExactM QTy.sub Θ Δ = some Y from hY]

end LinearDB.FEnv
