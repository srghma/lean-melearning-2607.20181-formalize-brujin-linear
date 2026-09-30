module

public import RequestProject.Toy.Anf
public import RequestProject.Toy.Resource

@[expose] public section

set_option autoImplicit false

/-!
# ToyLinearLogic: the sequent calculus of classical linear logic, as typed proof terms

The two-sided sequent calculus of classical linear logic, with exactly the rules of the
specification (initial sequents, cut, the two exchanges, and the left / right rules of
negation, `⊗`, `⅋`, `&`, `⊕`, `!` and `?`).

In the style of the typed A-normal grammar (`Toy/Anf.lean`), a derivation is a **typed proof
term**: `CLL Γ Ψ` is the `Type` of derivations of the sequent `Γ ⊢ Ψ`, an inductive family
indexed by its two sides, and each rule is a constructor.  A sequence `Γ, A` is the Lean list
`Γ ++ [A]` and `A, Ψ` is `A :: Ψ`, i.e. lists are read left to right exactly as written in the
rules.  `Derivable Γ Ψ` is `Nonempty (CLL Γ Ψ)`.

```
Fml ::= atom a | neg A                 -- A^⊥
      | tensor A B | par A B           -- A ⊗ B, A ⅋ B
      | amp A B | plus A B             -- A & B, A ⊕ B
      | bang A | quest A               -- !A, ?A
```

Results:

* exchange is admissible for arbitrary permutations of either side (`Derivable.perm`);
* linear implication `A ⊸ B := A^⊥ ⅋ B` has derived right and left rules (`lolliR`,
  `lolliL`);
* **the typed A-normal terms are linear-logic proofs**: every statement of `Toy/Anf.lean`
  from `Γ` to `Δ` of type `α` gives a derivation of `!Θ, used ⊢ ⟦α⟧`, where `used` lists the
  types of the variables it consumed and `!Θ` are `!`-hypotheses from which the constants follow
  (`Stmt.toCLL`); a function type `α → β` is read as `⟦α⟧ ⊸ ⟦β⟧`.  In particular every closed
  A-normal program of type `α` proves `!Θ ⊢ ⟦α⟧` (`AProgram.toCLL`), with the constants' own
  types as `Θ` (`AProgram.toCLL_of_list`), and `⊢ ⟦α⟧` when there are no constants
  (`AProgram.toCLL_of_isEmpty`).
-/

namespace LinearDB

namespace ToyLinearLogic

variable {A : Type}

/-- Formulas of classical linear logic over atoms `A`. -/
inductive Fml (A : Type) where
  | atom : A → Fml A
  /-- `A^⊥` -/
  | neg : Fml A → Fml A
  /-- `A ⊗ B` -/
  | tensor : Fml A → Fml A → Fml A
  /-- `A ⅋ B` -/
  | par : Fml A → Fml A → Fml A
  /-- `A & B` -/
  | amp : Fml A → Fml A → Fml A
  /-- `A ⊕ B` -/
  | plus : Fml A → Fml A → Fml A
  /-- `!A` -/
  | bang : Fml A → Fml A
  /-- `?A` -/
  | quest : Fml A → Fml A
  deriving DecidableEq

/-- **Derivations** of the sequent `Γ ⊢ Ψ`, one constructor per rule. -/
inductive CLL : List (Fml A) → List (Fml A) → Type where
  /-- Initial sequent `A ⊢ A`. -/
  | ax (a : Fml A) : CLL [a] [a]
  /-- `Γ ⊢ Λ, A` and `A, Δ ⊢ Ψ` give `Γ, Δ ⊢ Λ, Ψ`. -/
  | cut {Γ Δ Λ Ψ : List (Fml A)} {a : Fml A} :
      CLL Γ (Λ ++ [a]) → CLL (a :: Δ) Ψ → CLL (Γ ++ Δ) (Λ ++ Ψ)
  /-- L exch. -/
  | exchL {Γ Δ Ψ : List (Fml A)} {a b : Fml A} :
      CLL (Γ ++ a :: b :: Δ) Ψ → CLL (Γ ++ b :: a :: Δ) Ψ
  /-- R exch. -/
  | exchR {Γ Ψ Λ : List (Fml A)} {a b : Fml A} :
      CLL Γ (Ψ ++ a :: b :: Λ) → CLL Γ (Ψ ++ b :: a :: Λ)
  /-- L⊥: `Γ ⊢ Λ, A` gives `A^⊥, Γ ⊢ Λ`. -/
  | negL {Γ Λ : List (Fml A)} {a : Fml A} : CLL Γ (Λ ++ [a]) → CLL (.neg a :: Γ) Λ
  /-- R⊥: `A, Γ ⊢ Λ` gives `Γ ⊢ Λ, A^⊥`. -/
  | negR {Γ Λ : List (Fml A)} {a : Fml A} : CLL (a :: Γ) Λ → CLL Γ (Λ ++ [.neg a])
  /-- L⊗. -/
  | tensorL {Γ Ψ : List (Fml A)} {a b : Fml A} :
      CLL (Γ ++ [a, b]) Ψ → CLL (Γ ++ [.tensor a b]) Ψ
  /-- R⊗. -/
  | tensorR {Γ Δ Ψ Λ : List (Fml A)} {a b : Fml A} :
      CLL Γ (a :: Ψ) → CLL Δ (b :: Λ) → CLL (Γ ++ Δ) (.tensor a b :: (Ψ ++ Λ))
  /-- L⅋. -/
  | parL {Γ Δ Ψ Λ : List (Fml A)} {a b : Fml A} :
      CLL (Γ ++ [a]) Ψ → CLL (Δ ++ [b]) Λ → CLL (Γ ++ Δ ++ [.par a b]) (Ψ ++ Λ)
  /-- R⅋. -/
  | parR {Γ Ψ : List (Fml A)} {a b : Fml A} : CLL Γ (a :: b :: Ψ) → CLL Γ (.par a b :: Ψ)
  /-- L&₁. -/
  | withL₁ {Γ Ψ : List (Fml A)} {a b : Fml A} : CLL (Γ ++ [a]) Ψ → CLL (Γ ++ [.amp a b]) Ψ
  /-- L&₂. -/
  | withL₂ {Γ Ψ : List (Fml A)} {a b : Fml A} : CLL (Γ ++ [b]) Ψ → CLL (Γ ++ [.amp a b]) Ψ
  /-- R&. -/
  | withR {Γ Ψ : List (Fml A)} {a b : Fml A} :
      CLL Γ (a :: Ψ) → CLL Γ (b :: Ψ) → CLL Γ (.amp a b :: Ψ)
  /-- L⊕. -/
  | plusL {Γ Ψ : List (Fml A)} {a b : Fml A} :
      CLL (Γ ++ [a]) Ψ → CLL (Γ ++ [b]) Ψ → CLL (Γ ++ [.plus a b]) Ψ
  /-- R⊕₁. -/
  | plusR₁ {Γ Ψ : List (Fml A)} {a b : Fml A} : CLL Γ (a :: Ψ) → CLL Γ (.plus a b :: Ψ)
  /-- R⊕₂. -/
  | plusR₂ {Γ Ψ : List (Fml A)} {a b : Fml A} : CLL Γ (b :: Ψ) → CLL Γ (.plus a b :: Ψ)
  /-- ! weak. -/
  | bangW {Γ Ψ : List (Fml A)} {a : Fml A} : CLL Γ Ψ → CLL (Γ ++ [.bang a]) Ψ
  /-- ! contr. -/
  | bangC {Γ Ψ : List (Fml A)} {a : Fml A} :
      CLL (Γ ++ [.bang a, .bang a]) Ψ → CLL (Γ ++ [.bang a]) Ψ
  /-- ! der. -/
  | bangD {Γ Ψ : List (Fml A)} {a : Fml A} : CLL (Γ ++ [a]) Ψ → CLL (Γ ++ [.bang a]) Ψ
  /-- ? weak. -/
  | questW {Γ Ψ : List (Fml A)} {a : Fml A} : CLL Γ Ψ → CLL Γ (.quest a :: Ψ)
  /-- ? contr. -/
  | questC {Γ Ψ : List (Fml A)} {a : Fml A} :
      CLL Γ (.quest a :: .quest a :: Ψ) → CLL Γ (.quest a :: Ψ)
  /-- ? der. -/
  | questD {Γ Ψ : List (Fml A)} {a : Fml A} : CLL Γ (a :: Ψ) → CLL Γ (.quest a :: Ψ)
  /-- ! R: `!Γ ⊢ B, ?Ψ` gives `!Γ ⊢ !B, ?Ψ`. -/
  | bangR (Γ Ψ : List (Fml A)) {b : Fml A} :
      CLL (Γ.map .bang) (b :: Ψ.map .quest) → CLL (Γ.map .bang) (.bang b :: Ψ.map .quest)
  /-- ? L: `!Γ, B ⊢ ?Ψ` gives `!Γ, ?B ⊢ ?Ψ`. -/
  | questL (Γ Ψ : List (Fml A)) {b : Fml A} :
      CLL (Γ.map .bang ++ [b]) (Ψ.map .quest) → CLL (Γ.map .bang ++ [.quest b]) (Ψ.map .quest)

/-- The sequent `Γ ⊢ Ψ` is derivable. -/
abbrev Derivable (Γ Ψ : List (Fml A)) : Prop := Nonempty (CLL Γ Ψ)

/-! ## Exchange is admissible for any permutation -/

lemma CLL.permL_aux {Γ Γ' : List (Fml A)} (h : Γ.Perm Γ') :
    ∀ (pre Ψ : List (Fml A)), CLL (pre ++ Γ) Ψ → Derivable (pre ++ Γ') Ψ := by
  induction h with
  | nil => exact fun _ _ d => ⟨d⟩
  | cons x _ ih =>
    intro pre Ψ d
    simpa using ih (pre ++ [x]) Ψ (by simpa using d)
  | swap x y l => exact fun pre Ψ d => ⟨.exchL d⟩
  | trans _ _ ih₁ ih₂ =>
    intro pre Ψ d
    obtain ⟨d'⟩ := ih₁ pre Ψ d
    exact ih₂ pre Ψ d'

lemma CLL.permR_aux {Ψ Ψ' : List (Fml A)} (h : Ψ.Perm Ψ') :
    ∀ (pre Γ : List (Fml A)), CLL Γ (pre ++ Ψ) → Derivable Γ (pre ++ Ψ') := by
  induction h with
  | nil => exact fun _ _ d => ⟨d⟩
  | cons x _ ih =>
    intro pre Γ d
    simpa using ih (pre ++ [x]) Γ (by simpa using d)
  | swap x y l => exact fun pre Γ d => ⟨.exchR d⟩
  | trans _ _ ih₁ ih₂ =>
    intro pre Γ d
    obtain ⟨d'⟩ := ih₁ pre Γ d
    exact ih₂ pre Γ d'

/-- **Exchange** is admissible for arbitrary permutations of both sides of a sequent. -/
theorem Derivable.perm {Γ Γ' Ψ Ψ' : List (Fml A)} (d : Derivable Γ Ψ) (hΓ : Γ.Perm Γ')
    (hΨ : Ψ.Perm Ψ') : Derivable Γ' Ψ' := by
  obtain ⟨d⟩ := d
  obtain ⟨d⟩ := CLL.permL_aux hΓ [] Ψ d
  exact CLL.permR_aux hΨ [] Γ' d

/-! ## Linear implication -/

/-- Linear implication `A ⊸ B := A^⊥ ⅋ B`. -/
def Fml.lolli (a b : Fml A) : Fml A := .par (.neg a) b

/-- Derived right rule of `⊸`: `A, Γ ⊢ B, Ψ` gives `Γ ⊢ A ⊸ B, Ψ`. -/
theorem lolliR {Γ Ψ : List (Fml A)} {a b : Fml A} (d : Derivable (a :: Γ) (b :: Ψ)) :
    Derivable Γ (a.lolli b :: Ψ) := by
  obtain ⟨d⟩ := d
  obtain ⟨d'⟩ := Derivable.perm ⟨CLL.negR d⟩ (List.Perm.refl _)
    (List.perm_append_comm (l₁ := b :: Ψ) (l₂ := [Fml.neg a]))
  exact ⟨.parR d'⟩

/-- Derived left rule of `⊸`: `Γ ⊢ A, Ψ` and `B, Δ ⊢ Λ` give `A ⊸ B, Γ, Δ ⊢ Ψ, Λ`. -/
theorem lolliL {Γ Δ Ψ Λ : List (Fml A)} {a b : Fml A} (d₁ : Derivable Γ (a :: Ψ))
    (d₂ : Derivable (b :: Δ) Λ) : Derivable (a.lolli b :: (Γ ++ Δ)) (Ψ ++ Λ) := by
  obtain ⟨d₁⟩ := Derivable.perm d₁ (List.Perm.refl _) (List.perm_append_comm (l₁ := [a]))
  obtain ⟨d₁⟩ := Derivable.perm ⟨CLL.negL d₁⟩ (List.perm_append_comm (l₁ := [Fml.neg a]))
    (List.Perm.refl _)
  obtain ⟨d₂⟩ := Derivable.perm d₂ (List.perm_append_comm (l₁ := [b])) (List.Perm.refl _)
  exact Derivable.perm ⟨CLL.parL d₁ d₂⟩ (List.perm_append_comm (l₂ := [a.lolli b]))
    (List.Perm.refl _)

/-! ## Small examples -/

/-- `A ⊗ B ⊢ B ⊗ A`. -/
def tensorComm (a b : Fml A) : CLL [.tensor a b] [.tensor b a] :=
  .tensorL (Γ := []) (.exchL (Γ := []) (Δ := []) (.tensorR (.ax b) (.ax a)))

/-- `A ⊢ A^⊥^⊥`. -/
def dnegIntro (a : Fml A) : CLL [a] [.neg (.neg a)] :=
  .negR (Λ := []) (.negL (Λ := []) (.ax a))

/-- `⊢ A ⅋ A^⊥`. -/
def parExcludedMiddle (a : Fml A) : CLL [] [.par a (.neg a)] :=
  .parR (Ψ := []) (.negR (Γ := []) (Λ := [a]) (.ax a))

/-- `!A ⊢ !A ⊗ !A`. -/
def bangDup (a : Fml A) : CLL [.bang a] [.tensor (.bang a) (.bang a)] :=
  .bangC (Γ := []) (.tensorR (.ax (.bang a)) (.ax (.bang a)))

/-- `!A ⊢ !!A` (promotion). -/
def bangBang (a : Fml A) : CLL [.bang a] [.bang (.bang a)] :=
  .bangR [a] [] (.ax (.bang a))

/-! ## The typed A-normal terms are linear-logic proofs -/

/-- Simple types as linear-logic formulas: `α → β` is `⟦α⟧ ⊸ ⟦β⟧`. -/
def _root_.LinearDB.Ty.toFml : Ty A → Fml A
  | .atom a => .atom a
  | .arr α β => α.toFml.lolli β.toFml

open Toy

/-- The formulas of the variables consumed between the environments `Γ` and `Δ`. -/
def used (Γ Δ : FEnv A) : List (Fml A) := (Res.consumed Γ Δ).map Ty.toFml

lemma Var.consumed {Γ Δ : FEnv A} {α : Ty A} (x : Var Γ α Δ) :
    Res.consumed Γ Δ = [α] := by
  induction x with
  | here Γ α => simp
  | there₁ β _ ih => simp [ih]
  | there₂ _ ih => simp [ih]

lemma used_self (Γ : FEnv A) : used Γ Γ = [] := by simp [used]

lemma used_trans {Γ Δ Θ : FEnv A} (h₁ : Res.Le Θ Δ) (h₂ : Res.Le Δ Γ) :
    (used Γ Θ).Perm (used Γ Δ ++ used Δ Θ) := by
  simpa [used] using (Res.consumed_trans h₁ h₂).map Ty.toFml

variable {C : Type} {τ : C → Ty A}

lemma le_of_llTyped {Γ Δ : FEnv A} {t : Term C} {α : Ty A} (h : LLTyped τ Γ t α Δ) :
    Res.Le Δ Γ := h.le

/-! ### Constants as reusable hypotheses

A constant may be used any number of times, so it is not a linear resource: the constants are
given as `!`-hypotheses `!Θ`, which the translation weakens and contracts as needed. -/

/-- Proves a permutation between two explicit lists by counting. -/
local macro "perm_tac" : tactic =>
  `(tactic| (classical
             exact List.perm_iff_count.2 fun _ => by
               simp [List.count_cons, List.count_append] <;> omega))

/-- The `!`-hypotheses `!Θ`. -/
def bangs (Θ : List (Fml A)) : List (Fml A) := Θ.map .bang

@[simp] lemma bangs_nil : bangs ([] : List (Fml A)) = [] := rfl
@[simp] lemma bangs_cons (a : Fml A) (Θ : List (Fml A)) : bangs (a :: Θ) = .bang a :: bangs Θ :=
  rfl

/-- Weakening by `!Θ`. -/
theorem Derivable.weakenBangs (Θ : List (Fml A)) {Γ Ψ : List (Fml A)} (d : Derivable Γ Ψ) :
    Derivable (bangs Θ ++ Γ) Ψ := by
  induction Θ with
  | nil => simpa using d
  | cons a Θ ih =>
    obtain ⟨e⟩ := ih
    exact Derivable.perm ⟨CLL.bangW (a := a) e⟩ (by perm_tac) (List.Perm.refl _)

/-- Contraction of two copies of `!Θ`. -/
theorem Derivable.contractBangs (Θ : List (Fml A)) {Γ Ψ : List (Fml A)}
    (d : Derivable (bangs Θ ++ (bangs Θ ++ Γ)) Ψ) : Derivable (bangs Θ ++ Γ) Ψ := by
  induction Θ generalizing Γ with
  | nil => simpa using d
  | cons a Θ ih =>
    obtain ⟨e⟩ := d.perm (Γ' := (bangs Θ ++ bangs Θ ++ Γ) ++ [.bang a, .bang a]) (by perm_tac)
      (List.Perm.refl _)
    obtain ⟨e⟩ := Derivable.perm ⟨CLL.bangC e⟩ (Γ' := bangs Θ ++ (bangs Θ ++ (.bang a :: Γ)))
      (by perm_tac) (List.Perm.refl _)
    exact (ih ⟨e⟩).perm (by perm_tac) (List.Perm.refl _)

/-- A formula of `Θ` follows from `!Θ` (by dereliction and weakening). -/
theorem derivable_bangs_of_mem {Θ : List (Fml A)} {a : Fml A} (h : a ∈ Θ) :
    Derivable (bangs Θ) [a] := by
  classical
  have d : Derivable [.bang a] [a] := ⟨CLL.bangD (Γ := []) (CLL.ax a)⟩
  refine (d.weakenBangs (Θ.erase a)).perm ?_ (List.Perm.refl _)
  have := ((List.perm_cons_erase h).map Fml.bang).symm
  simpa [bangs] using List.perm_append_comm.trans this

/-- A head (a variable or a constant) is a proof of its type from what it uses. -/
theorem _root_.LinearDB.Toy.Head.toCLL {Θ : List (Fml A)}
    (κ : ∀ c, Derivable (bangs Θ) [(τ c).toFml]) {Γ Δ : FEnv A} {α : Ty A}
    (h : Head τ Γ α Δ) : Derivable (bangs Θ ++ used Γ Δ) [α.toFml] := by
  cases h with
  | var x => simpa [used, Var.consumed x] using Derivable.weakenBangs Θ ⟨CLL.ax α.toFml⟩
  | const c => simpa [used_self] using κ c

mutual
/-- A value is a proof of its type from the variables it uses. -/
theorem _root_.LinearDB.Toy.Val.toCLL {Θ : List (Fml A)}
    (κ : ∀ c, Derivable (bangs Θ) [(τ c).toFml]) {Γ Δ : FEnv A} {α : Ty A} :
    Val τ Γ α Δ → Derivable (bangs Θ ++ used Γ Δ) [α.toFml]
  | .head h => h.toCLL κ
  | .lam b => by
    refine lolliR (Ψ := []) ((b.toCLL κ).perm ?_ (List.Perm.refl _))
    simp only [used, Res.consumed_cons_cons, Res.step_some_none, List.map_cons,
      List.singleton_append]
    perm_tac
/-- A computation is a proof of its type from the variables it uses. -/
theorem _root_.LinearDB.Toy.Comp.toCLL {Θ : List (Fml A)}
    (κ : ∀ c, Derivable (bangs Θ) [(τ c).toFml]) {Γ Δ : FEnv A} {α : Ty A} :
    Comp τ Γ α Δ → Derivable (bangs Θ ++ used Γ Δ) [α.toFml]
  | .app (Δ := Δ') (α := α') h v => by
    obtain ⟨dh⟩ := h.toCLL κ
    obtain ⟨dl⟩ := lolliL (Δ := []) (Ψ := []) (v.toCLL κ) ⟨CLL.ax α.toFml⟩
    have dc : CLL ((bangs Θ ++ used Γ Δ') ++ (bangs Θ ++ used Δ' Δ)) ([] ++ [α.toFml]) :=
      CLL.cut (Λ := []) dh (by simpa using dl)
    have hp := used_trans (le_of_llTyped v.sound) (le_of_llTyped h.sound)
    refine Derivable.contractBangs Θ (Derivable.perm ⟨dc⟩ ?_ (List.Perm.refl _))
    classical
    exact List.perm_iff_count.2 fun y => by
      have := List.perm_iff_count.1 hp y
      simp [List.count_append] at this ⊢
      omega
/-- **A-normal statements are proofs.** A statement from `Γ` to `Δ` of type `α` is a proof of
    `!Θ, used ⊢ ⟦α⟧`, where `used` lists the types of the variables it consumed and `!Θ` are
    the (reusable) hypotheses from which the constants follow. -/
theorem _root_.LinearDB.Toy.Stmt.toCLL {Θ : List (Fml A)}
    (κ : ∀ c, Derivable (bangs Θ) [(τ c).toFml]) {Γ Δ : FEnv A} {α : Ty A} :
    Stmt τ Γ α Δ → Derivable (bangs Θ ++ used Γ Δ) [α.toFml]
  | .ret v => v.toCLL κ
  | .letE (Δ := Δ') (σ := σ) c b => by
    obtain ⟨dc⟩ := c.toCLL κ
    obtain ⟨db⟩ := (b.toCLL κ).perm (Γ' := σ.toFml :: (bangs Θ ++ used Γ Δ'))
      (by simp only [used, Res.consumed_cons_cons, Res.step_some_none, List.map_cons,
            List.singleton_append]
          perm_tac) (List.Perm.refl _)
    have d : CLL ((bangs Θ ++ used Δ' Δ) ++ (bangs Θ ++ used Γ Δ')) ([] ++ [α.toFml]) :=
      CLL.cut (Λ := []) (by simpa using dc) db
    have hp := used_trans (le_of_llTyped c.sound) (Res.le_cons_cons.1 (le_of_llTyped b.sound)).2
    refine Derivable.contractBangs Θ (Derivable.perm ⟨d⟩ ?_ (List.Perm.refl _))
    classical
    exact List.perm_iff_count.2 fun y => by
      have := List.perm_iff_count.1 hp y
      simp [List.count_append] at this ⊢
      omega
end

/-- **Every closed A-normal program of type `α` is a proof of `!Θ ⊢ ⟦α⟧`** in classical linear
    logic, when the constants' types follow from `!Θ`. -/
theorem _root_.LinearDB.Toy.AProgram.toCLL {Θ : List (Fml A)}
    (κ : ∀ c, Derivable (bangs Θ) [(τ c).toFml]) {α : Ty A}
    (p : AProgram τ α) : Derivable (bangs Θ) [α.toFml] := by
  simpa [used] using Stmt.toCLL κ p

/-- The same, with the constants themselves as hypotheses: if every constant is listed in `cs`,
    a closed A-normal program of type `α` proves `!⟦τ c₁⟧, …, !⟦τ cₙ⟧ ⊢ ⟦α⟧`. -/
theorem _root_.LinearDB.Toy.AProgram.toCLL_of_list (cs : List C) (hcs : ∀ c, c ∈ cs)
    {α : Ty A} (p : AProgram τ α) :
    Derivable (bangs (cs.map fun c => (τ c).toFml)) [α.toFml] :=
  p.toCLL fun c => derivable_bangs_of_mem (List.mem_map_of_mem (f := fun c => (τ c).toFml) (hcs c))

/-- Without constants (`C` empty), a closed A-normal program of type `α` proves `⊢ ⟦α⟧`. -/
theorem _root_.LinearDB.Toy.AProgram.toCLL_of_isEmpty [IsEmpty C] {α : Ty A}
    (p : AProgram τ α) : Derivable [] [α.toFml] :=
  p.toCLL (Θ := []) fun c => isEmptyElim c

end ToyLinearLogic

end LinearDB
