module

public import RequestProject.Toy.Term

@[expose] public section

set_option autoImplicit false

/-!
# Toy normal forms with *known* and *unknown* parts: every elimination needs an unknown

A third toy grammar of terms, a miniature of a normaliser's output grammar: β-normal linear
terms (indexed, as the other toy grammars, by the paper's judgement `{Γ} t : α {Δ}`,
`LinearDB.LLTyped`) in which **every redex that could be evaluated has been**.  The unknowns
are the variables of `Γ`; the knowns are the literals and the λs.  A call of a constant on
known arguments only (`add 1 2`) is a redex the normaliser would have computed, so it cannot
be written; `add x 1`, stuck on the unknown `x`, can.

```
Neu   Γ α Δ     ::= var x                        -- an unknown
                  | app Neu (PExpr o)            -- calling an unknown function
                  | extern c (Args o) (o = open) -- a saturated call of a constant,
                                                 -- at least one argument open
PExpr Γ α Δ o   ::= neu Neu                      -- o = open
                  | lit c                        -- o = closed: a constant of leaf type
                  | lamC PExpr                   -- o = closed: the body uses only its parameter
                  | lamO PExpr (Γ ≠ Δ)           -- o = open: the body uses an outer unknown
Args  Γ σs Δ o  ::= nil | cons PExpr Args        -- o = the `||` of the arguments' openness
```

**Open and closed.**  The index `o : Bool` says whether the expression mentions an unknown
(`true`: *open*) or not (`false`: *closed*).  It is computed by the constructors, and it is
**exact** (`PExpr.closed_iff`): an expression is closed iff it leaves its environment unchanged,
`Γ = Δ`, i.e. iff it uses no unknown.  In particular a λ cannot be marked open if its body
touches only its own parameter, and cannot be marked closed if it touches anything else
(`lamO` carries a proof that it does, `lamC` is typed so that it does not).

What cannot be written:

* everything the first toy grammar excludes: a variable used twice, a parameter never used,
  a β-redex (`PExpr.sound`, `PExpr.quasiLinear`, `PExpr.normal`, `OProgram.linear`);
* a call that uses no unknown: the head of an `app` is neutral, and neutral terms always use an
  unknown (`Neu.uses_unknown`); an `extern` needs an open argument.  So an application always
  uses an unknown (`PExpr.app_uses_unknown`), and a closed program is a literal or a λ, never
  a computation (`OProgram.closed`, `PExpr.closed_isValue`);
* a partial call of a constant: `extern` is saturated, and ends in a leaf type.  (To keep the
  toy small, constants of function type are only ever called, never passed as values.)
-/

namespace LinearDB

namespace Toy

namespace Open

open Term

variable {A C : Type}

mutual
/-- **Neutral terms**: stuck on an unknown. -/
inductive Neu (τ : C → Ty A) : FEnv A → Ty A → FEnv A → Type where
  /-- An unknown. -/
  | var {Γ Δ : FEnv A} {α : Ty A} : Var Γ α Δ → Neu τ Γ α Δ
  /-- A call of an unknown function. -/
  | app {Γ Δ Θ : FEnv A} {α β : Ty A} {o : Bool} :
      Neu τ Γ (.arr α β) Δ → PExpr τ Δ α Θ o → Neu τ Γ β Θ
  /-- A saturated call of a constant with at least one open argument. -/
  | extern {Γ Δ : FEnv A} {o : Bool} (c : C) :
      Args τ Γ (τ c).args Δ o → o = true → Neu τ Γ (.atom (τ c).result) Δ

/-- **Pure expressions**, open (`o = true`) or closed (`o = false`). -/
inductive PExpr (τ : C → Ty A) : FEnv A → Ty A → FEnv A → Bool → Type where
  /-- A neutral term: open. -/
  | neu {Γ Δ : FEnv A} {α : Ty A} : Neu τ Γ α Δ → PExpr τ Γ α Δ true
  /-- A constant of leaf type (a literal): closed. -/
  | lit {Γ : FEnv A} (c : C) : (τ c).args = [] → PExpr τ Γ (τ c) Γ false
  /-- A closed λ: its body consumes its parameter and nothing else. -/
  | lamC {Γ : FEnv A} {α β : Ty A} {o : Bool} :
      PExpr τ (some α :: Γ) β (none :: Γ) o → PExpr τ Γ (.arr α β) Γ false
  /-- An open λ: its body consumes its parameter and some outer unknown. -/
  | lamO {Γ Δ : FEnv A} {α β : Ty A} {o : Bool} :
      PExpr τ (some α :: Γ) β (none :: Δ) o → Γ ≠ Δ → PExpr τ Γ (.arr α β) Δ true

/-- The arguments of a call, left to right; open iff one of them is. -/
inductive Args (τ : C → Ty A) : FEnv A → List (Ty A) → FEnv A → Bool → Type where
  | nil {Γ : FEnv A} : Args τ Γ [] Γ false
  | cons {Γ Δ Θ : FEnv A} {σ : Ty A} {σs : List (Ty A)} {o₁ o₂ : Bool} :
      PExpr τ Γ σ Δ o₁ → Args τ Δ σs Θ o₂ → Args τ Γ (σ :: σs) Θ (o₁ || o₂)
end

/-- A closed program of type `α`: no unknown is available, none is left over. -/
abbrev OProgram (τ : C → Ty A) (α : Ty A) : Type := Σ o : Bool, PExpr τ [] α [] o

variable {τ : C → Ty A}

/-! ## Into the first toy grammar, and erasure -/

/-- A constant, as a neutral term of the first toy grammar at the type of its spine. -/
def constNeu {Γ : FEnv A} (c : C) : Toy.Neu τ Γ (Ty.ofSpine (τ c).args (τ c).result) Γ :=
  (Ty.ofSpine_args_result (τ c)).symm ▸ Toy.Neu.const c

mutual
/-- A neutral term as a neutral term of the first toy grammar. -/
def Neu.toNeu {Γ Δ : FEnv A} {α : Ty A} : Neu τ Γ α Δ → Toy.Neu τ Γ α Δ
  | .var x => .var x
  | .app n a => .app n.toNeu a.toNf
  | .extern c as _ => as.toNeu (constNeu c)
/-- An expression as a normal form of the first toy grammar. -/
def PExpr.toNf {Γ Δ : FEnv A} {α : Ty A} {o : Bool} : PExpr τ Γ α Δ o → Toy.Nf τ Γ α Δ
  | .neu n => .neu n.toNeu
  | .lit c _ => .neu (.const c)
  | .lamC b => .lam b.toNf
  | .lamO b _ => .lam b.toNf
/-- Apply a function to the arguments, left to right. -/
def Args.toNeu {Γ Δ Θ : FEnv A} {σs : List (Ty A)} {b : A} {o : Bool} :
    Args τ Δ σs Θ o → Toy.Neu τ Γ (Ty.ofSpine σs b) Δ → Toy.Neu τ Γ (.atom b) Θ
  | .nil, f => f
  | .cons a as, f => as.toNeu (.app f a.toNf)
end

/-- The untyped de Bruijn term of an expression. -/
def PExpr.erase {Γ Δ : FEnv A} {α : Ty A} {o : Bool} (e : PExpr τ Γ α Δ o) : Term C :=
  e.toNf.erase

/-! ## What the first toy grammar gives for free -/

/-- **Soundness.** An expression is typed by the paper's system, with the same environments. -/
theorem PExpr.sound {Γ Δ : FEnv A} {α : Ty A} {o : Bool} (e : PExpr τ Γ α Δ o) :
    LLTyped τ Γ e.erase α Δ :=
  e.toNf.sound

/-- Every free unknown is used at most once, and every λ binds exactly one occurrence. -/
theorem PExpr.quasiLinear {Γ Δ : FEnv A} {α : Ty A} {o : Bool} (e : PExpr τ Γ α Δ o) :
    QuasiLinear e.erase :=
  e.sound.quasiLinear

/-- An expression contains no β-redex. -/
theorem PExpr.normal {Γ Δ : FEnv A} {α : Ty A} {o : Bool} (e : PExpr τ Γ α Δ o) :
    Normal e.erase :=
  e.toNf.normal

/-- A closed program is a linear λ-term, simply typed in the empty environment. -/
theorem OProgram.linear {α : Ty A} (p : OProgram τ α) :
    Linear p.2.erase ∧ STTyped τ [] p.2.erase α :=
  Program.linear p.2.toNf

/-! ## Openness is exact -/

/-- `⊑` is antisymmetric. -/
theorem FEnv.le_antisymm {Γ Δ : FEnv A} (h₁ : FEnv.le Γ Δ) (h₂ : FEnv.le Δ Γ) : Γ = Δ := by
  unfold FEnv.le at h₁ h₂
  induction h₁ with
  | nil => rfl
  | @cons a b l₁ l₂ hab _ ih =>
    cases h₂ with
    | cons hba h' =>
      rw [ih h']
      rcases hab with rfl | rfl <;> rcases hba with h'' | h'' <;> simp_all

/-- An environment can only lose slots, so if it went down a step it cannot come back. -/
theorem FEnv.ne_of_le_of_ne {Γ Δ Θ : FEnv A} (h₁ : FEnv.le Θ Δ) (h₂ : FEnv.le Δ Γ)
    (h : Γ ≠ Δ) : Γ ≠ Θ := by
  rintro rfl
  exact h (FEnv.le_antisymm h₁ h₂)

/-- A variable uses an unknown. -/
theorem Var.env_ne {Γ Δ : FEnv A} {α : Ty A} (x : Var Γ α Δ) : Γ ≠ Δ := by
  induction x with
  | here => simp
  | there₁ _ _ ih => simpa using ih
  | there₂ _ ih => simpa using ih

theorem PExpr.le {Γ Δ : FEnv A} {α : Ty A} {o : Bool} (e : PExpr τ Γ α Δ o) : FEnv.le Δ Γ :=
  e.sound.le

theorem Neu.le {Γ Δ : FEnv A} {α : Ty A} (n : Neu τ Γ α Δ) : FEnv.le Δ Γ :=
  (PExpr.neu n).le

theorem Args.le {Γ Δ : FEnv A} {σs : List (Ty A)} {o : Bool} :
    Args τ Γ σs Δ o → FEnv.le Δ Γ
  | .nil => FEnv.le_refl _
  | .cons a as => FEnv.le_trans as.le a.le

mutual
/-- **Every neutral term uses an unknown.** -/
theorem Neu.uses_unknown {Γ Δ : FEnv A} {α : Ty A} : Neu τ Γ α Δ → Γ ≠ Δ
  | .var x => Var.env_ne x
  | .app n a => FEnv.ne_of_le_of_ne a.le n.le n.uses_unknown
  | .extern _ as h => (as.exact).2 h

/-- Openness of an expression is exact: closed means it uses no unknown, open that it does. -/
theorem PExpr.exact {Γ Δ : FEnv A} {α : Ty A} {o : Bool} :
    PExpr τ Γ α Δ o → (o = false → Γ = Δ) ∧ (o = true → Γ ≠ Δ)
  | .neu n => ⟨nofun, fun _ => n.uses_unknown⟩
  | .lit _ _ => ⟨fun _ => rfl, nofun⟩
  | .lamC _ => ⟨fun _ => rfl, nofun⟩
  | .lamO _ h => ⟨nofun, fun _ => h⟩

/-- Openness of arguments is exact. -/
theorem Args.exact {Γ Δ : FEnv A} {σs : List (Ty A)} {o : Bool} :
    Args τ Γ σs Δ o → (o = false → Γ = Δ) ∧ (o = true → Γ ≠ Δ)
  | .nil => ⟨fun _ => rfl, nofun⟩
  | .cons (o₁ := o₁) (o₂ := o₂) a as => by
    have ha := a.exact
    have has := as.exact
    cases o₁ <;> cases o₂
    · exact ⟨fun _ => (ha.1 rfl).trans (has.1 rfl), nofun⟩
    · refine ⟨nofun, fun _ => ?_⟩
      rw [ha.1 rfl]; exact has.2 rfl
    · exact ⟨nofun, fun _ => FEnv.ne_of_le_of_ne as.le a.le (ha.2 rfl)⟩
    · exact ⟨nofun, fun _ => FEnv.ne_of_le_of_ne as.le a.le (ha.2 rfl)⟩
end

/-- **Openness is exact.**  An expression is closed iff it uses no unknown. -/
theorem PExpr.closed_iff {Γ Δ : FEnv A} {α : Ty A} {o : Bool} (e : PExpr τ Γ α Δ o) :
    o = false ↔ Γ = Δ := by
  refine ⟨e.exact.1, fun h => ?_⟩
  cases o
  · rfl
  · exact absurd h (e.exact.2 rfl)

/-! ## No known redex -/

/-- A closed expression is a value: a literal or a λ. -/
theorem PExpr.closed_isValue {Γ Δ : FEnv A} {α : Ty A} (e : PExpr τ Γ α Δ false) :
    (∃ c, e.erase = .const c) ∨ ∃ s, e.erase = .lam s := by
  cases e with
  | lit c _ => exact .inl ⟨c, rfl⟩
  | lamC b => exact .inr ⟨b.toNf.erase, rfl⟩

/-- **Every application uses an unknown**: an expression whose erasure is an application
    changes its environment.  So `add 1 2`, a redex between knowns, cannot be written. -/
theorem PExpr.app_uses_unknown {Γ Δ : FEnv A} {α : Ty A} {o : Bool} (e : PExpr τ Γ α Δ o)
    {f a : Term C} (h : e.erase = .app f a) : Γ ≠ Δ := by
  cases e with
  | neu n => exact n.uses_unknown
  | lit => simp [PExpr.erase, PExpr.toNf, Toy.Nf.erase, Toy.Neu.erase] at h
  | lamC => simp [PExpr.erase, PExpr.toNf, Toy.Nf.erase] at h
  | lamO _ hne => exact hne

/-- A closed program is closed, so it is a literal or a λ: it contains no computation at top
    level. -/
theorem OProgram.closed {α : Ty A} (p : OProgram τ α) :
    p.1 = false ∧ ((∃ c, p.2.erase = .const c) ∨ ∃ s, p.2.erase = .lam s) := by
  obtain ⟨o, e⟩ := p
  have ho : o = false := (e.closed_iff).2 rfl
  subst ho
  exact ⟨rfl, e.closed_isValue⟩

end Open

end Toy

end LinearDB

end
