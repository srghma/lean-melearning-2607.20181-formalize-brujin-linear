module

public import RequestProject.Sec3FragmentaryEnv.FEnv

/-!
# Algebraic properties of quasi-types and fragmentary environments

Lemma `qtSimpleEq` and Lemma `envSimpleEq` (end of Section 3 of the paper), together with the
componentwise characterization of the operations on fragmentary environments and basic facts
about the order `⊑`.
-/

@[expose] public section

namespace LinearDB

variable {A : Type*}

namespace FEnv

section List.zipWithExactM

variable (f : QTy A → QTy A → Option (QTy A))

@[simp] lemma List.zipWithExactM_nil_nil : List.zipWithExactM f [] [] = some [] := rfl

@[simp] lemma List.zipWithExactM_nil_cons (b : QTy A) (Δ : FEnv A) : List.zipWithExactM f [] (b :: Δ) = none := rfl

@[simp] lemma List.zipWithExactM_cons_nil (a : QTy A) (Γ : FEnv A) : List.zipWithExactM f (a :: Γ) [] = none := rfl

lemma List.zipWithExactM_cons_cons_eq_some {a b : QTy A} {Γ Δ Θ : FEnv A} :
    List.zipWithExactM f (a :: Γ) (b :: Δ) = some Θ ↔
      ∃ c Θ', f a b = some c ∧ List.zipWithExactM f Γ Δ = some Θ' ∧ Θ = c :: Θ' := by
  simp only [List.zipWithExactM]
  rcases h1 : f a b with _ | c <;> rcases h2 : List.zipWithExactM f Γ Δ with _ | Θ' <;> simp [eq_comm]

lemma List.zipWithExactM_nil_left_eq_some {Δ Θ : FEnv A} :
    List.zipWithExactM f [] Δ = some Θ ↔ Δ = [] ∧ Θ = [] := by
  cases Δ <;> simp [eq_comm]

lemma List.zipWithExactM_nil_right_eq_some {Γ Θ : FEnv A} :
    List.zipWithExactM f Γ [] = some Θ ↔ Γ = [] ∧ Θ = [] := by
  cases Γ <;> simp [eq_comm]

lemma List.zipWithExactM_length {Γ Δ Θ : FEnv A} (h : List.zipWithExactM f Γ Δ = some Θ) :
    Γ.length = Δ.length ∧ Θ.length = Γ.length := by
  induction Γ generalizing Δ Θ with
  | nil => rw [List.zipWithExactM_nil_left_eq_some] at h; simp [h.1, h.2]
  | cons a Γ ih =>
    cases Δ with
    | nil => simp at h
    | cons b Δ =>
      obtain ⟨c, Θ', -, h2, rfl⟩ := (List.zipWithExactM_cons_cons_eq_some f).1 h
      have := ih h2
      simp [this.1, this.2]

/-- Componentwise characterization of the lifted operations. -/
lemma List.zipWithExactM_eq_some_iff {Γ Δ Θ : FEnv A} :
    List.zipWithExactM f Γ Δ = some Θ ↔
      ∃ (h₁ : Γ.length = Δ.length) (h₂ : Θ.length = Γ.length),
        ∀ i (hi : i < Γ.length), f Γ[i] (Δ[i]'(h₁ ▸ hi)) = some (Θ[i]'(h₂ ▸ hi)) := by
  induction Γ generalizing Δ Θ with
  | nil =>
    rw [List.zipWithExactM_nil_left_eq_some]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl, fun i hi => by simp at hi⟩
    · rintro ⟨h₁, h₂, -⟩
      exact ⟨List.eq_nil_of_length_eq_zero h₁.symm, List.eq_nil_of_length_eq_zero h₂⟩
  | cons a Γ ih =>
    cases Δ with
    | nil => simp
    | cons b Δ =>
      rw [List.zipWithExactM_cons_cons_eq_some]
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

end List.zipWithExactM

/-- The paper's definition of the addition of fragmentary environments:
`Γ + Δ` is defined (and equal to `Θ`) iff `|Γ + Δ| = |Γ| = |Δ|` and
`(Γ + Δ)(i) = Γ(i) + Δ(i)` for all `0 ≤ i < |Γ|`. -/
theorem add_eq_some_iff {Γ Δ Θ : FEnv A} :
    add Γ Δ = some Θ ↔
      ∃ (h₁ : Γ.length = Δ.length) (h₂ : Θ.length = Γ.length),
        ∀ i (hi : i < Γ.length), QTy.add Γ[i] (Δ[i]'(h₁ ▸ hi)) = some (Θ[i]'(h₂ ▸ hi)) :=
  List.zipWithExactM_eq_some_iff _

/-- The paper's definition of the subtraction of fragmentary environments:
`Γ - Δ` is defined (and equal to `Θ`) iff `|Γ - Δ| = |Γ| = |Δ|` and
`(Γ - Δ)(i) = Γ(i) - Δ(i)` for all `0 ≤ i < |Γ|`. -/
theorem sub_eq_some_iff [DecidableEq A] {Γ Δ Θ : FEnv A} :
    sub Γ Δ = some Θ ↔
      ∃ (h₁ : Γ.length = Δ.length) (h₂ : Θ.length = Γ.length),
        ∀ i (hi : i < Γ.length), QTy.sub Γ[i] (Δ[i]'(h₁ ▸ hi)) = some (Θ[i]'(h₂ ▸ hi)) :=
  List.zipWithExactM_eq_some_iff _

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
  List.zipWithExactM_cons_cons_eq_some _

lemma sub_cons_cons_eq_some [DecidableEq A] {a b : QTy A} {Γ Δ Θ : FEnv A} :
    sub (a :: Γ) (b :: Δ) = some Θ ↔
      ∃ c Θ', QTy.sub a b = some c ∧ sub Γ Δ = some Θ' ∧ Θ = c :: Θ' :=
  List.zipWithExactM_cons_cons_eq_some _

@[simp] lemma add_cons_cons_some_iff {a b c : QTy A} {Γ Δ Θ : FEnv A} :
    add (a :: Γ) (b :: Δ) = some (c :: Θ) ↔ QTy.add a b = some c ∧ add Γ Δ = some Θ := by
  rw [add_cons_cons_eq_some]; simp

@[simp] lemma sub_cons_cons_some_iff [DecidableEq A] {a b c : QTy A} {Γ Δ Θ : FEnv A} :
    sub (a :: Γ) (b :: Δ) = some (c :: Θ) ↔ QTy.sub a b = some c ∧ sub Γ Δ = some Θ := by
  rw [sub_cons_cons_eq_some]; simp

end FEnv

end LinearDB
