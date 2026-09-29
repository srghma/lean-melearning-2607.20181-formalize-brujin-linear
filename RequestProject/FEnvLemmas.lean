module

public import RequestProject.FEnv

/-!
# Algebraic properties of quasi-types and fragmentary environments

Lemma `qtSimpleEq` and Lemma `envSimpleEq` (end of Section 3) and Lemma `envdefined`
(end of Section 4) of the paper, together with the componentwise characterization of the
operations on fragmentary environments.
-/

@[expose] public section

namespace LinearDB

variable {A : Type*}

namespace FEnv

section zipOp

variable (f : QTy A → QTy A → Option (QTy A))

@[simp] lemma zipOp_nil_nil : zipOp f [] [] = some [] := rfl

@[simp] lemma zipOp_nil_cons (b : QTy A) (Δ : FEnv A) : zipOp f [] (b :: Δ) = none := rfl

@[simp] lemma zipOp_cons_nil (a : QTy A) (Γ : FEnv A) : zipOp f (a :: Γ) [] = none := rfl

lemma zipOp_cons_cons_eq_some {a b : QTy A} {Γ Δ Θ : FEnv A} :
    zipOp f (a :: Γ) (b :: Δ) = some Θ ↔
      ∃ c Θ', f a b = some c ∧ zipOp f Γ Δ = some Θ' ∧ Θ = c :: Θ' := by
  simp only [zipOp]
  rcases h1 : f a b with _ | c <;> rcases h2 : zipOp f Γ Δ with _ | Θ' <;> simp [eq_comm]

lemma zipOp_nil_left_eq_some {Δ Θ : FEnv A} :
    zipOp f [] Δ = some Θ ↔ Δ = [] ∧ Θ = [] := by
  cases Δ <;> simp [eq_comm]

lemma zipOp_nil_right_eq_some {Γ Θ : FEnv A} :
    zipOp f Γ [] = some Θ ↔ Γ = [] ∧ Θ = [] := by
  cases Γ <;> simp [eq_comm]

lemma zipOp_length {Γ Δ Θ : FEnv A} (h : zipOp f Γ Δ = some Θ) :
    Γ.length = Δ.length ∧ Θ.length = Γ.length := by
  induction Γ generalizing Δ Θ with
  | nil => rw [zipOp_nil_left_eq_some] at h; simp [h.1, h.2]
  | cons a Γ ih =>
    cases Δ with
    | nil => simp at h
    | cons b Δ =>
      obtain ⟨c, Θ', -, h2, rfl⟩ := (zipOp_cons_cons_eq_some f).1 h
      have := ih h2
      simp [this.1, this.2]

/-- Componentwise characterization of the lifted operations. -/
lemma zipOp_eq_some_iff {Γ Δ Θ : FEnv A} :
    zipOp f Γ Δ = some Θ ↔
      ∃ (h₁ : Γ.length = Δ.length) (h₂ : Θ.length = Γ.length),
        ∀ i (hi : i < Γ.length), f Γ[i] (Δ[i]'(h₁ ▸ hi)) = some (Θ[i]'(h₂ ▸ hi)) := by
  induction Γ generalizing Δ Θ with
  | nil =>
    rw [zipOp_nil_left_eq_some]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl, fun i hi => by simp at hi⟩
    · rintro ⟨h₁, h₂, -⟩
      exact ⟨List.eq_nil_of_length_eq_zero h₁.symm, List.eq_nil_of_length_eq_zero h₂⟩
  | cons a Γ ih =>
    cases Δ with
    | nil => simp
    | cons b Δ =>
      rw [zipOp_cons_cons_eq_some]
      constructor
      · rintro ⟨c, Θ', hc, hΘ', rfl⟩
        obtain ⟨h₁, h₂, h⟩ := ih.1 hΘ'
        refine ⟨by simp [h₁], by simp [h₂], ?_⟩
        rintro (_ | i) hi
        · simpa using hc
        · simpa using h i (by simpa using hi)
      · rintro ⟨h₁, h₂, h⟩
        cases Θ with
        | nil => simp at h₂
        | cons c Θ' =>
          refine ⟨c, Θ', by simpa using h 0 (by simp), ?_, rfl⟩
          refine ih.2 ⟨by simpa using h₁, by simpa using h₂, fun i hi => ?_⟩
          simpa using h (i + 1) (by simpa using hi)

end zipOp

/-- The paper's definition of the addition of fragmentary environments:
`Γ + Δ` is defined (and equal to `Θ`) iff `|Γ + Δ| = |Γ| = |Δ|` and
`(Γ + Δ)(i) = Γ(i) + Δ(i)` for all `0 ≤ i < |Γ|`. -/
theorem add_eq_some_iff {Γ Δ Θ : FEnv A} :
    add Γ Δ = some Θ ↔
      ∃ (h₁ : Γ.length = Δ.length) (h₂ : Θ.length = Γ.length),
        ∀ i (hi : i < Γ.length), QTy.add Γ[i] (Δ[i]'(h₁ ▸ hi)) = some (Θ[i]'(h₂ ▸ hi)) :=
  zipOp_eq_some_iff _

/-- The paper's definition of the subtraction of fragmentary environments:
`Γ - Δ` is defined (and equal to `Θ`) iff `|Γ - Δ| = |Γ| = |Δ|` and
`(Γ - Δ)(i) = Γ(i) - Δ(i)` for all `0 ≤ i < |Γ|`. -/
theorem sub_eq_some_iff [DecidableEq A] {Γ Δ Θ : FEnv A} :
    sub Γ Δ = some Θ ↔
      ∃ (h₁ : Γ.length = Δ.length) (h₂ : Θ.length = Γ.length),
        ∀ i (hi : i < Γ.length), QTy.sub Γ[i] (Δ[i]'(h₁ ▸ hi)) = some (Θ[i]'(h₂ ▸ hi)) :=
  zipOp_eq_some_iff _

end FEnv

namespace QTy

variable [DecidableEq A]

/-- Lemma `qtSimpleEq` (a): `φ + (ψ - ω) = ψ - (ω - φ)`, if all operations are defined. -/
theorem simpleEq_a {φ ψ ω x y l r : QTy A}
    (hx : sub ψ ω = some x) (hl : add φ x = some l)
    (hy : sub ω φ = some y) (hr : sub ψ y = some r) : l = r := by
  rcases φ with _ | φ <;> rcases ψ with _ | ψ <;> rcases ω with _ | ω <;>
    rcases x with _ | x <;> rcases y with _ | y <;>
    simp only [sub, add, Option.some.injEq, reduceCtorEq] at hx hl hy hr <;>
    (try split_ifs at hx hy hr) <;> simp_all

/-- Lemma `qtSimpleEq` (b): `φ + (ψ - φ) = ψ`, if all operations are defined. -/
theorem simpleEq_b {φ ψ x l : QTy A}
    (hx : sub ψ φ = some x) (hl : add φ x = some l) : l = ψ := by
  rcases φ with _ | φ <;> rcases ψ with _ | ψ <;> rcases x with _ | x <;>
    simp only [sub, add, Option.some.injEq, reduceCtorEq] at hx hl <;>
    (try split_ifs at hx) <;> simp_all

/-- Lemma `qtSimpleEq` (c): `φ - (φ - ψ) = ψ`, if all operations are defined. -/
theorem simpleEq_c {φ ψ x l : QTy A}
    (hx : sub φ ψ = some x) (hl : sub φ x = some l) : l = ψ := by
  rcases φ with _ | φ <;> rcases ψ with _ | ψ <;> rcases x with _ | x <;>
    simp only [sub, Option.some.injEq, reduceCtorEq] at hx hl <;>
    (try split_ifs at hx hl) <;> simp_all

end QTy

namespace FEnv

variable [DecidableEq A]

/-- Lemma `envSimpleEq` (a): `Γ + (Δ - Θ) = Δ - (Θ - Γ)`, if all operations are defined. -/
theorem simpleEq_a {Γ Δ Θ X Y L R : FEnv A}
    (hX : sub Δ Θ = some X) (hL : add Γ X = some L)
    (hY : sub Θ Γ = some Y) (hR : sub Δ Y = some R) : L = R := by
  rw [sub_eq_some_iff] at hX hY hR
  rw [add_eq_some_iff] at hL
  obtain ⟨a1, a2, a⟩ := hX
  obtain ⟨b1, b2, b⟩ := hL
  obtain ⟨c1, c2, c⟩ := hY
  obtain ⟨d1, d2, d⟩ := hR
  apply List.ext_getElem (by omega)
  intro i h1 h2
  exact QTy.simpleEq_a (a i (by omega)) (b i (by omega)) (c i (by omega)) (d i (by omega))

/-- Lemma `envSimpleEq` (b): `Γ + (Δ - Γ) = Δ`, if all operations are defined. -/
theorem simpleEq_b {Γ Δ X L : FEnv A}
    (hX : sub Δ Γ = some X) (hL : add Γ X = some L) : L = Δ := by
  rw [sub_eq_some_iff] at hX
  rw [add_eq_some_iff] at hL
  obtain ⟨a1, a2, a⟩ := hX
  obtain ⟨b1, b2, b⟩ := hL
  apply List.ext_getElem (by omega)
  intro i h1 h2
  exact QTy.simpleEq_b (a i (by omega)) (b i (by omega))

/-- Lemma `envSimpleEq` (c): `Γ - (Γ - Δ) = Δ`, if all operations are defined. -/
theorem simpleEq_c {Γ Δ X L : FEnv A}
    (hX : sub Γ Δ = some X) (hL : sub Γ X = some L) : L = Δ := by
  rw [sub_eq_some_iff] at hX hL
  obtain ⟨a1, a2, a⟩ := hX
  obtain ⟨b1, b2, b⟩ := hL
  apply List.ext_getElem (by omega)
  intro i h1 h2
  exact QTy.simpleEq_c (a i (by omega)) (b i (by omega))

end FEnv

end LinearDB

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
      obtain ⟨c, X', hc, hX', rfl⟩ := (zipOp_cons_cons_eq_some _).1 hX
      obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 (ih (Θ := Θ) (by simp [add, hX']))
      rcases hdg with rfl | rfl
      · simp [add, zipOp, QTy.add, show zipOp QTy.add Δ Θ = some Y from hY]
      · simp [add, zipOp, hc, show zipOp QTy.add Δ Θ = some Y from hY]

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
      obtain ⟨c, X', hc, hX', rfl⟩ := (zipOp_cons_cons_eq_some _).1 hX
      obtain ⟨Y, hY⟩ := Option.isSome_iff_exists.1 (ih (Θ := Θ) (by simp [sub, hX']))
      rcases hdg with rfl | rfl
      · cases θ <;> simp [sub, zipOp, QTy.sub, show zipOp QTy.sub Θ Δ = some Y from hY]
      · simp [sub, zipOp, hc, show zipOp QTy.sub Θ Δ = some Y from hY]

end LinearDB.FEnv
