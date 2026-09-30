module

public import Mathlib

@[expose] public section

set_option autoImplicit false

/-!
# Resource environments (input / output contexts)

The bookkeeping behind a Hodas–Miller style judgement `{Γ} t {Δ}`, for resources of any
type `X`: a *resource environment* is a list of slots `Option X`, a slot being `none` once its
resource has been used.  This is the paper's notion of fragmentary environment
(`LinearDB.FEnv`), for arbitrary resources instead of simple types.

* `Res.Le Δ Γ` (`Δ ⊑ Γ`): `Δ` is `Γ` with some slots emptied;
* `Res.consumed Γ Δ`: the resources of the slots that are full in `Γ` and empty in `Δ`;
* `Res.Slot Γ x Δ`: use one slot of `Γ`, holding `x` (the rule (var) with its weakenings).

The two facts used by both toy linear logics are that consumption is additive along a chain
`Θ ⊑ Δ ⊑ Γ` (`consumed_trans`), and that any splitting of what is consumed can be realised by
an intermediate environment (`exists_split`).
-/

namespace LinearDB

namespace Toy

namespace Res

variable {X : Type*}

/-- `Δ ⊑ Γ`: the two environments have the same length and each slot of `Δ` is either empty or
    equal to that of `Γ`. -/
def Le (Δ Γ : List (Option X)) : Prop := List.Forall₂ (fun b a => b = none ∨ b = a) Δ Γ

/-- What a single slot contributes to `consumed`. -/
def step : Option X → Option X → List X
  | some x, none => [x]
  | _, _ => []

/-- The resources used between an input `Γ` and an output `Δ`: those of the slots that are full
    in `Γ` and empty in `Δ`. -/
def consumed : List (Option X) → List (Option X) → List X
  | a :: Γ, b :: Δ => step a b ++ consumed Γ Δ
  | _, _ => []

@[simp] lemma consumed_cons_cons (a b : Option X) (Γ Δ : List (Option X)) :
    consumed (a :: Γ) (b :: Δ) = step a b ++ consumed Γ Δ := rfl

@[simp] lemma step_some_none (x : X) : step (some x) none = [x] := rfl
@[simp] lemma step_none (b : Option X) : step none b = [] := by cases b <;> rfl
@[simp] lemma step_self (a : Option X) : step a a = [] := by cases a <;> rfl

@[simp] lemma le_cons_cons {a b : Option X} {Γ Δ : List (Option X)} :
    Le (b :: Δ) (a :: Γ) ↔ (b = none ∨ b = a) ∧ Le Δ Γ := List.forall₂_cons

lemma le_refl (Γ : List (Option X)) : Le Γ Γ := List.forall₂_same.2 fun _ _ => Or.inr rfl

lemma le_trans {Γ Δ Θ : List (Option X)} (h₁ : Le Θ Δ) (h₂ : Le Δ Γ) : Le Θ Γ := by
  unfold Le at *
  induction h₂ generalizing Θ with
  | nil => cases h₁; exact .nil
  | cons hab _ ih =>
    cases h₁ with
    | cons hc h =>
      refine .cons ?_ (ih h)
      rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact hab

@[simp] lemma consumed_self (Γ : List (Option X)) : consumed Γ Γ = [] := by
  induction Γ with
  | nil => rfl
  | cons a Γ ih => simp [ih]

/-- **Consumption is additive** along `Θ ⊑ Δ ⊑ Γ`. -/
lemma consumed_trans {Γ Δ Θ : List (Option X)} (h₁ : Le Θ Δ) (h₂ : Le Δ Γ) :
    (consumed Γ Θ).Perm (consumed Γ Δ ++ consumed Δ Θ) := by
  unfold Le at *
  induction h₂ generalizing Θ with
  | nil => cases h₁; simp [consumed]
  | @cons b a Δ Γ hab _ ih =>
    cases h₁ with
    | @cons c _ Θ _ hc h =>
      have := ih h
      rcases a with _ | x <;> rcases b with _ | y <;> rcases c with _ | z <;>
        simp only [reduceCtorEq, false_or, Option.some.injEq, or_false,
          or_self] at hab hc <;> subst_vars <;>
        first
          | simpa using this
          | simpa using this.cons _
          | simpa using (this.cons _).trans List.perm_middle.symm

/-- Nothing is consumed exactly when nothing changed. -/
lemma eq_of_consumed_eq_nil {Γ Δ : List (Option X)} (h : Le Δ Γ) (hc : consumed Γ Δ = []) :
    Δ = Γ := by
  unfold Le at h
  induction h with
  | nil => rfl
  | @cons b a Δ Γ hab _ ih =>
    rcases hab with rfl | rfl
    · cases a with
      | none => simp_all
      | some x => simp at hc
    · simp_all

/-! ## Using one slot -/

/-- Use one slot of `Γ`, holding `x`; the output is `Γ` with that slot emptied. -/
inductive Slot : List (Option X) → X → List (Option X) → Type _ where
  | here (Γ : List (Option X)) (x : X) : Slot (some x :: Γ) x (none :: Γ)
  | skip {Γ Δ : List (Option X)} {x : X} (o : Option X) : Slot Γ x Δ → Slot (o :: Γ) x (o :: Δ)

/-- The de Bruijn index of a slot. -/
def Slot.idx {Γ Δ : List (Option X)} {x : X} : Slot Γ x Δ → ℕ
  | .here _ _ => 0
  | .skip _ s => s.idx + 1

lemma Slot.le {Γ Δ : List (Option X)} {x : X} (s : Slot Γ x Δ) : Le Δ Γ := by
  induction s with
  | here Γ x => exact le_cons_cons.2 ⟨Or.inl rfl, le_refl Γ⟩
  | skip o _ ih => exact le_cons_cons.2 ⟨Or.inr rfl, ih⟩

lemma Slot.consumed {Γ Δ : List (Option X)} {x : X} (s : Slot Γ x Δ) :
    Res.consumed Γ Δ = [x] := by
  induction s with
  | here Γ x => simp
  | skip o _ ih => simp [ih]

/-- If `x` is among the consumed resources, some slot holding `x` can be used first. -/
lemma exists_slot {Γ Δ : List (Option X)} {x : X} {rest : List X} (h : Le Δ Γ)
    (hc : (consumed Γ Δ).Perm (x :: rest)) :
    ∃ Γ', Nonempty (Slot Γ x Γ') ∧ Le Δ Γ' ∧ (consumed Γ' Δ).Perm rest := by
  classical
  unfold Le at h
  induction h generalizing rest with
  | nil => simp [consumed] at hc
  | @cons b a Δ Γ hab h ih =>
    rcases hab with rfl | rfl
    · cases a with
      | none =>
        simp only [consumed_cons_cons, step_none, List.nil_append] at hc
        obtain ⟨Γ', ⟨s⟩, hl, hp⟩ := ih hc
        exact ⟨none :: Γ', ⟨.skip _ s⟩, le_cons_cons.2 ⟨Or.inl rfl, hl⟩, by simpa using hp⟩
      | some y =>
        simp only [consumed_cons_cons, step_some_none, List.singleton_append] at hc
        by_cases hxy : x = y
        · subst hxy
          exact ⟨none :: Γ, ⟨.here _ _⟩, le_cons_cons.2 ⟨Or.inl rfl, h⟩,
            by simpa using hc.cons_inv⟩
        · have hmem : x ∈ consumed Γ Δ := by
            have : x ∈ y :: consumed Γ Δ := hc.symm.subset (by simp)
            simpa [hxy] using this
          have hp := List.perm_cons_erase hmem
          obtain ⟨Γ', ⟨s⟩, hl, hp'⟩ := ih hp
          refine ⟨some y :: Γ', ⟨.skip _ s⟩, le_cons_cons.2 ⟨Or.inl rfl, hl⟩, ?_⟩
          simp only [consumed_cons_cons, step_some_none, List.singleton_append]
          refine (hp'.cons y).trans ?_
          have h2 : (y :: consumed Γ Δ).Perm (y :: x :: (consumed Γ Δ).erase x) := hp.cons y
          have h3 := (hc.symm.trans h2).trans (List.Perm.swap x y _)
          exact (h3.cons_inv).symm
    · simp only [consumed_cons_cons, step_self, List.nil_append] at hc
      obtain ⟨Γ', ⟨s⟩, hl, hp⟩ := ih hc
      exact ⟨b :: Γ', ⟨.skip _ s⟩, le_cons_cons.2 ⟨Or.inr rfl, hl⟩, by simpa using hp⟩

/-- **Splitting.** Any splitting `xs ++ ys` of what is consumed between `Γ` and `Δ` is realised
    by an intermediate environment `M`: first `xs` is consumed, then `ys`. -/
lemma exists_split {Γ Δ : List (Option X)} {xs ys : List X} (h : Le Δ Γ)
    (hc : (consumed Γ Δ).Perm (xs ++ ys)) :
    ∃ M, Le M Γ ∧ Le Δ M ∧ (consumed Γ M).Perm xs ∧ (consumed M Δ).Perm ys := by
  induction xs generalizing Γ with
  | nil => exact ⟨Γ, le_refl Γ, h, by simp, by simpa using hc⟩
  | cons x xs ih =>
    obtain ⟨Γ', ⟨s⟩, hl, hp⟩ := exists_slot h hc
    obtain ⟨M, hM, hΔ, h1, h2⟩ := ih hl hp
    refine ⟨M, le_trans hM s.le, hΔ, ?_, h2⟩
    refine (consumed_trans hM s.le).trans ?_
    simpa [s.consumed] using h1.cons x

/-! ## Renaming the resources -/

lemma le_map {Y : Type*} (f : X → Y) {Γ Δ : List (Option X)} (h : Le Δ Γ) :
    Le (Δ.map (Option.map f)) (Γ.map (Option.map f)) := by
  unfold Le at *
  induction h with
  | nil => exact .nil
  | cons hab _ ih =>
    refine .cons ?_ ih
    rcases hab with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

lemma consumed_map {Y : Type*} (f : X → Y) (Γ Δ : List (Option X)) :
    consumed (Γ.map (Option.map f)) (Δ.map (Option.map f)) = (consumed Γ Δ).map f := by
  induction Γ generalizing Δ with
  | nil => rfl
  | cons a Γ ih =>
    cases Δ with
    | nil => rfl
    | cons b Δ =>
      rcases a with _ | x <;> rcases b with _ | y <;> simp [ih, step]

lemma consumed_replicate_none (xs : List X) :
    consumed (xs.map some) (List.replicate xs.length none) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.replicate_succ, ih]

lemma le_replicate_none (Γ : List (Option X)) : Le (List.replicate Γ.length none) Γ := by
  induction Γ with
  | nil => exact .nil
  | cons a Γ ih => exact le_cons_cons.2 ⟨Or.inl rfl, ih⟩

lemma le_append {Γ Δ Γ' Δ' : List (Option X)} (h : Le Δ Γ) (h' : Le Δ' Γ') :
    Le (Δ ++ Δ') (Γ ++ Γ') := List.rel_append h h'

lemma consumed_append {Γ Δ Γ' Δ' : List (Option X)} (h : Γ.length = Δ.length) :
    consumed (Γ ++ Γ') (Δ ++ Δ') = consumed Γ Δ ++ consumed Γ' Δ' := by
  induction Γ generalizing Δ with
  | nil => cases Δ with
    | nil => rfl
    | cons => simp at h
  | cons a Γ ih => cases Δ with
    | nil => simp at h
    | cons b Δ => simp [ih (by simpa using h)]

lemma Le.length_eq {Γ Δ : List (Option X)} (h : Le Δ Γ) : Δ.length = Γ.length :=
  List.Forall₂.length_eq h

end Res

end Toy

end LinearDB
