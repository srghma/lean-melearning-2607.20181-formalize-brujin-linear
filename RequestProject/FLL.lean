module

public import RequestProject.LL

/-!
# The typing system with fragmentary environments (Section 3 of the paper)

* `FLLTyped.occ_spec` — the lemma relating `⊢_fll` judgements and numbers of occurrences;
* `STTyped.toFLL`     — Proposition `fst2fll`;
* `FLLTyped.toST`     — Proposition `fll2fst`.
-/

@[expose] public section

namespace LinearDB

open Term

variable {A C : Type*} {τ : C → Ty A}

/-! ### Auxiliary facts about the addition of fragmentary environments -/

namespace FEnv

lemma add_getElem? {Γ Δ Θ : FEnv A} (h : add Γ Δ = some Θ) (i : ℕ) :
    (Γ[i]? = some none ∧ Θ[i]? = Δ[i]?) ∨ (Δ[i]? = some none ∧ Θ[i]? = Γ[i]?) ∨
      (Γ[i]? = none ∧ Δ[i]? = none ∧ Θ[i]? = none) := by
  induction Γ generalizing Δ Θ i with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (zipOp_nil_left_eq_some _).1 h
    simp
  | cons a Γ ih =>
    rcases Δ with _ | ⟨b, Δ⟩
    · simp [add] at h
    obtain ⟨c, Θ', hc, hΘ', rfl⟩ := add_cons_cons_eq_some.1 h
    rcases i with _ | i
    · rcases a with _ | a <;> rcases b with _ | b <;> simp [QTy.add] at hc <;> subst hc <;> simp
    · simpa using ih hΘ' i

lemma le_of_add {Γ Δ Θ X : FEnv A} (hΓ : le Γ X) (hΔ : le Δ X) (h : add Γ Δ = some Θ) :
    le Θ X := by
  unfold le at hΓ
  induction hΓ generalizing Δ Θ with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (zipOp_nil_left_eq_some _).1 h
    exact List.Forall₂.nil
  | @cons a x Γ X hax _ ih =>
    obtain ⟨b, Δ', rfl, hb, hΔ'⟩ := le_cons_right hΔ
    obtain ⟨c, Θ', hc, hΘ', rfl⟩ := add_cons_cons_eq_some.1 h
    refine le_cons_cons.2 ⟨?_, ih hΔ' hΘ'⟩
    rcases a with _ | a <;> rcases b with _ | b <;> simp [QTy.add] at hc <;> subst hc <;> assumption

lemma le_add_left {Γ Δ Θ : FEnv A} (h : add Γ Δ = some Θ) : le Γ Θ := by
  induction Γ generalizing Δ Θ with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (zipOp_nil_left_eq_some _).1 h
    exact List.Forall₂.nil
  | cons a Γ ih =>
    rcases Δ with _ | ⟨b, Δ⟩
    · simp [add] at h
    obtain ⟨c, Θ', hc, hΘ', rfl⟩ := add_cons_cons_eq_some.1 h
    refine le_cons_cons.2 ⟨?_, ih hΘ'⟩
    rcases a with _ | a <;> rcases b with _ | b <;> simp [QTy.add] at hc <;> subst hc <;>
      first | exact Or.inl rfl | exact Or.inr rfl

lemma le_add_right {Γ Δ Θ : FEnv A} (h : add Γ Δ = some Θ) : le Δ Θ := by
  induction Γ generalizing Δ Θ with
  | nil =>
    obtain ⟨rfl, rfl⟩ := (zipOp_nil_left_eq_some _).1 h
    exact List.Forall₂.nil
  | cons a Γ ih =>
    rcases Δ with _ | ⟨b, Δ⟩
    · simp [add] at h
    obtain ⟨c, Θ', hc, hΘ', rfl⟩ := add_cons_cons_eq_some.1 h
    refine le_cons_cons.2 ⟨?_, ih hΘ'⟩
    rcases a with _ | a <;> rcases b with _ | b <;> simp [QTy.add] at hc <;> subst hc <;>
      first | exact Or.inl rfl | exact Or.inr rfl

lemma add_exists {Γ Δ : FEnv A} (hl : Γ.length = Δ.length)
    (h : ∀ (i : ℕ) (a b : Ty A), Γ[i]? = some (some a) → Δ[i]? = some (some b) → False) :
    ∃ Θ, add Γ Δ = some Θ := by
  induction Γ generalizing Δ with
  | nil =>
    rcases Δ with _ | ⟨b, Δ⟩
    · exact ⟨[], rfl⟩
    · simp at hl
  | cons a Γ ih =>
    rcases Δ with _ | ⟨b, Δ⟩
    · simp at hl
    obtain ⟨Θ, hΘ⟩ := ih (by simpa using hl) (fun i a b h1 h2 => h (i + 1) a b h1 h2)
    rcases a with _ | a
    · exact ⟨b :: Θ, by simp [hΘ, QTy.add]⟩
    rcases b with _ | b
    · exact ⟨some a :: Θ, by simp [hΘ, QTy.add]⟩
    · exact (h 0 a b rfl rfl).elim

lemma minenv_le {X : FEnv A} : le (minenv X.length) X := by
  induction X with
  | nil => exact List.Forall₂.nil
  | cons x X ih => exact le_cons_cons.2 ⟨Or.inl rfl, ih⟩

@[simp] lemma getElem?_minenv_eq_some {n i : ℕ} {a : QTy A} :
    (minenv n : FEnv A)[i]? = some a ↔ i < n ∧ a = none := by
  simp [minenv, List.getElem?_replicate, eq_comm]

end FEnv

/-! ### The occurrence lemma -/

/-- Uniform version of the occurrence lemma of Section 3, valid for every index `i`. -/
theorem FLLTyped.occ_cases {Γ : FEnv A} {t : Term C} {α : Ty A}
    (h : FLLTyped τ Γ t α) (i : ℕ) :
    ((∃ β, Γ[i]? = some (some β)) ∧ occ i t = 1) ∨
      (¬ (∃ β, Γ[i]? = some (some β)) ∧ occ i t = 0) := by
  induction h generalizing i with
  | const n c => right; simp [occ]
  | var n α =>
    rcases i with _ | i
    · left; simp [occ]
    · right; simp [occ]
  | weak _ ih =>
    rcases i with _ | i
    · right; simp [occ]
    · simpa [occ] using ih i
  | app _ _ hadd ih₁ ih₂ =>
    simp only [occ]
    rcases FEnv.add_getElem? hadd i with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2, e3⟩
    · rw [e2]
      rcases ih₁ i with ⟨⟨β, h1⟩, -⟩ | ⟨-, h1⟩
      · rw [e1] at h1; simp at h1
      · rcases ih₂ i with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · left; exact ⟨h2, by omega⟩
        · right; exact ⟨h2, by omega⟩
    · rw [e2]
      rcases ih₂ i with ⟨⟨β, h1⟩, -⟩ | ⟨-, h1⟩
      · rw [e1] at h1; simp at h1
      · rcases ih₁ i with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · left; exact ⟨h2, by omega⟩
        · right; exact ⟨h2, by omega⟩
    · right
      rcases ih₁ i with ⟨⟨β, h1⟩, -⟩ | ⟨-, h1⟩
      · rw [e1] at h1; simp at h1
      rcases ih₂ i with ⟨⟨β, h2⟩, -⟩ | ⟨-, h2⟩
      · rw [e2] at h2; simp at h2
      exact ⟨by simp [e3], by omega⟩
  | abs _ ih => simpa [occ] using ih (i + 1)

/-- Lemma of Section 3: if `⊢_fll Γ ⊢ t : α`, then for every `0 ≤ i < |Γ|`, if `Γ(i) ∈ ty`
then `occ(i, t) = 1`; otherwise `Γ(i) = ⊥` and `occ(i, t) = 0`. -/
theorem FLLTyped.occ_spec {Γ : FEnv A} {t : Term C} {α : Ty A}
    (h : FLLTyped τ Γ t α) (i : ℕ) (hi : i < Γ.length) :
    ((∃ β, Γ[i]? = some (some β)) → occ i t = 1) ∧
      (¬ (∃ β, Γ[i]? = some (some β)) → Γ[i]? = some none ∧ occ i t = 0) := by
  rcases h.occ_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun hn => absurd h1 hn⟩
  · refine ⟨fun hn => absurd hn h1, fun _ => ⟨?_, h2⟩⟩
    rw [List.getElem?_eq_getElem hi] at h1 ⊢
    rcases hΓ : Γ[i] with _ | β
    · rfl
    · exact absurd ⟨β, by rw [hΓ]⟩ h1

/-! ### Proposition `fll2fst` -/

theorem FLLTyped.toST_of_le {Γ : FEnv A} {t : Term C} {α : Ty A}
    (h : FLLTyped τ Γ t α) : ∀ Θ : Env A, FEnv.le Γ (FEnv.ofEnv Θ) → STTyped τ Θ t α := by
  induction h with
  | const n c => intro Θ _; exact STTyped.const Θ c
  | var n α =>
    intro Θ hΘ
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.le_nil_right] at hΘ
    · simp only [FEnv.ofEnv_cons, FEnv.le_cons_cons, QTy.le] at hΘ
      obtain ⟨h1 | h1, -⟩ := hΘ
      · simp at h1
      · cases h1; exact STTyped.var _ _
  | weak _ ih =>
    intro Θ hΘ
    rcases Θ with _ | ⟨θ, Θ⟩
    · simp [FEnv.le_nil_right] at hΘ
    · simp only [FEnv.ofEnv_cons, FEnv.le_cons_cons] at hΘ
      exact STTyped.weak θ (ih Θ hΘ.2)
  | app _ _ hadd ih₁ ih₂ =>
    intro Θ hΘ
    exact STTyped.app (ih₁ Θ (FEnv.le_trans (FEnv.le_add_left hadd) hΘ))
      (ih₂ Θ (FEnv.le_trans (FEnv.le_add_right hadd) hΘ))
  | @abs Γ t α β _ ih =>
    intro Θ hΘ
    exact STTyped.abs (ih (α :: Θ) (by simpa using ⟨QTy.le_refl _, hΘ⟩))

/-- Proposition `fll2fst`: if `⊢_fll Γ ⊢ t : α`, then `t` is quasi-linear and there exists an
environment `Δ` such that `Γ ⊑ Δ` and `⊢_st Δ ⊢ t : α`. -/
theorem FLLTyped.toST {Γ : FEnv A} {t : Term C} {α : Ty A} (h : FLLTyped τ Γ t α) :
    QuasiLinear t ∧ ∃ Δ : Env A, FEnv.le Γ (FEnv.ofEnv Δ) ∧ STTyped τ Δ t α := by
  have hle : FEnv.le Γ (FEnv.ofEnv (Γ.map (fun a => a.getD α))) := by
    clear h
    induction Γ with
    | nil => exact List.Forall₂.nil
    | cons a Γ ih =>
      refine List.Forall₂.cons ?_ ih
      rcases a with _ | a
      · exact Or.inl rfl
      · exact Or.inr rfl
  refine ⟨⟨?_, fun i hi => ?_⟩, _, hle, h.toST_of_le _ hle⟩
  · clear hle
    intro v hv
    induction h generalizing v with
    | const _ _ => exact absurd hv not_isSubterm_lam_const
    | var _ _ => exact absurd hv not_isSubterm_lam_var
    | weak _ _ => exact absurd hv not_isSubterm_lam_var
    | app _ _ _ ih₁ ih₂ =>
      cases hv with
      | appL _ hv => exact ih₁ _ hv
      | appR _ hv => exact ih₂ _ hv
    | abs h ih =>
      cases hv with
      | refl =>
        rcases h.occ_cases 0 with ⟨-, h3⟩ | ⟨h1, -⟩
        · exact h3
        · exact absurd ⟨_, rfl⟩ h1
      | lam hv => exact ih _ hv
  · rcases h.occ_cases i with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact h2
    · exact absurd h2 hi

/-! ### Proposition `fst2fll` -/

/-- Proposition `fst2fll`: if `t` is quasi-linear and `⊢_st Γ ⊢ t : α`, then there exists a
fragmentary environment `Δ` such that `Δ ⊑ Γ` and `⊢_fll Δ ⊢ t : α`. -/
theorem STTyped.toFLL {Γ : Env A} {t : Term C} {α : Ty A}
    (h : STTyped τ Γ t α) (hq : QuasiLinear t) :
    ∃ Δ : FEnv A, FEnv.le Δ (FEnv.ofEnv Γ) ∧ FLLTyped τ Δ t α := by
  induction h with
  | const Γ c =>
    refine ⟨FEnv.minenv Γ.length, ?_, FLLTyped.const _ c⟩
    simpa using (FEnv.minenv_le (X := FEnv.ofEnv Γ))
  | var Γ α =>
    refine ⟨some α :: FEnv.minenv Γ.length, ?_, FLLTyped.var _ α⟩
    exact FEnv.le_cons_cons.2 ⟨QTy.le_refl _, by simpa using (FEnv.minenv_le (X := FEnv.ofEnv Γ))⟩
  | @weak Γ i α β _ ih =>
    obtain ⟨Δ, hΔ, hΔ'⟩ := ih (quasiLinear_var i)
    exact ⟨none :: Δ, FEnv.le_cons_cons.2 ⟨Or.inl rfl, hΔ⟩, FLLTyped.weak hΔ'⟩
  | @app Γ t u α β _ _ ih₁ ih₂ =>
    obtain ⟨Δ₁, hΔ₁, h₁⟩ := ih₁ hq.app_left
    obtain ⟨Δ₂, hΔ₂, h₂⟩ := ih₂ hq.app_right
    obtain ⟨Θ, hΘ⟩ := FEnv.add_exists (Γ := Δ₁) (Δ := Δ₂)
      ((FEnv.le_length hΔ₁).trans (FEnv.le_length hΔ₂).symm) (fun i a b ha hb => by
        rcases h₁.occ_cases i with ⟨-, e1⟩ | ⟨n1, -⟩
        · rcases h₂.occ_cases i with ⟨-, e2⟩ | ⟨n2, -⟩
          · have := hq.2 i (by simp [fv, occ, e1, e2])
            simp [occ, e1, e2] at this
          · exact n2 ⟨b, hb⟩
        · exact n1 ⟨a, ha⟩)
    exact ⟨Θ, FEnv.le_of_add hΔ₁ hΔ₂ hΘ, FLLTyped.app h₁ h₂ hΘ⟩
  | @abs Γ t α β _ ih =>
    obtain ⟨Δ', hΔ', h'⟩ := ih hq.of_lam
    obtain ⟨d, Δ, rfl, hd, hΔ⟩ := FEnv.le_cons_right hΔ'
    rcases h'.occ_cases 0 with ⟨⟨γ, hγ⟩, -⟩ | ⟨-, h0⟩
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hγ
      subst hγ
      rcases hd with hd | hd
      · simp at hd
      · cases hd
        exact ⟨Δ, hΔ, FLLTyped.abs h'⟩
    · rw [hq.occ_zero_of_lam] at h0; simp at h0

end LinearDB
