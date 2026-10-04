module

public import RequestProject.Toy.Terms.Term

@[expose] public section

set_option autoImplicit false

/-!
# Toy A-normal terms: values, computations, statements

A second toy grammar of terms, in the layered A-normal style (values / computations /
statements), still indexed by the paper's judgement `{Γ} t : α {Δ}` (Figure 4,
`LinearDB.LLTyped`), so that every unknown is used exactly once.

```
Head Γ α Δ ::= var Var | const c            -- what may be called: never a `λ`
Val  Γ α Δ ::= head Head | lam Stmt         -- a closure: its parameter must be consumed
Comp Γ α Δ ::= app Head Val                 -- one call, the result is named by `letE`
Stmt Γ α Δ ::= ret Val
             | letE Comp Stmt               -- `let x := c; body`, `x` used exactly once
```

**The environments.**  As in the paper's rule (app), the environment is threaded through a
statement from left to right *in the erased term*: `let x := c; body` erases to
`(λ body) c`, so `body` runs from `x :: Γ` to `⊥ :: Δ` (it consumes `x`) and `c` runs from
`Δ` to `Θ`, using some of the variables the body left over.

What cannot be written:

* a variable used twice, or a `λ`-parameter or a `let`-bound unknown never used
  (`Stmt.quasiLinear`);
* a closed program (`AProgram`, from `[]` to `[]`) whose erasure is not a linear λ-term
  (`AProgram.linear`);
* a call of a `λ` (`Comp.app` takes a `Head`, which is a variable or a constant:
  `Comp.head_ne_lam`): the only β-redexes of the erasure are the `let`s.

Nothing typable is lost among these shapes: the erasure of each class is typed by the paper's
system with the same environments (`Head.sound`, `Val.sound`, `Comp.sound`, `Stmt.sound`).
-/

namespace LinearDB

namespace Toy

open Term

variable {A C : Type}

/-- What may be called: a variable or a constant. -/
inductive Head (τ : C → Ty A) : FEnv A → Ty A → FEnv A → Type where
  | var {Γ Δ : FEnv A} {α : Ty A} : Var Γ α Δ → Head τ Γ α Δ
  | const {Γ : FEnv A} (c : C) : Head τ Γ (τ c) Γ

mutual
/-- **Values**: a head, or a closure whose parameter the body consumes. -/
inductive Val (τ : C → Ty A) : FEnv A → Ty A → FEnv A → Type where
  | head {Γ Δ : FEnv A} {α : Ty A} : Head τ Γ α Δ → Val τ Γ α Δ
  | lam {Γ Δ : FEnv A} {α β : Ty A} : Stmt τ (some α :: Γ) β (none :: Δ) → Val τ Γ (.arr α β) Δ
/-- **Computations**: one call of a head on a value. -/
inductive Comp (τ : C → Ty A) : FEnv A → Ty A → FEnv A → Type where
  | app {Γ Δ Θ : FEnv A} {α β : Ty A} : Head τ Γ (.arr α β) Δ → Val τ Δ α Θ → Comp τ Γ β Θ
/-- **Statements**: `let`s of computations ending in a value. -/
inductive Stmt (τ : C → Ty A) : FEnv A → Ty A → FEnv A → Type where
  | ret {Γ Δ : FEnv A} {α : Ty A} : Val τ Γ α Δ → Stmt τ Γ α Δ
  /-- `let x := c; body`: the body consumes `x` and leaves `Δ`, from which `c` is computed. -/
  | letE {Γ Δ Θ : FEnv A} {σ α : Ty A} :
      Comp τ Δ σ Θ → Stmt τ (some σ :: Γ) α (none :: Δ) → Stmt τ Γ α Θ
end

/-- A closed A-normal program of type `α`. -/
abbrev AProgram (τ : C → Ty A) (α : Ty A) : Type := Stmt τ [] α []

variable {τ : C → Ty A}

/-! ## Erasure -/

/-- The untyped term of a head. -/
def Head.erase {Γ Δ : FEnv A} {α : Ty A} : Head τ Γ α Δ → Term C
  | .var x => .var x.idx
  | .const c => .const c

mutual
/-- The untyped term of a value. -/
def Val.erase {Γ Δ : FEnv A} {α : Ty A} : Val τ Γ α Δ → Term C
  | .head h => h.erase
  | .lam b => .lam b.erase
/-- The untyped term of a computation. -/
def Comp.erase {Γ Δ : FEnv A} {α : Ty A} : Comp τ Γ α Δ → Term C
  | .app h v => .app h.erase v.erase
/-- The untyped term of a statement: `let x := c; body` is `(λ body) c`. -/
def Stmt.erase {Γ Δ : FEnv A} {α : Ty A} : Stmt τ Γ α Δ → Term C
  | .ret v => v.erase
  | .letE c b => .app (.lam b.erase) c.erase
end

/-! ## Soundness -/

/-- A head is typed by the paper's system. -/
theorem Head.sound {Γ Δ : FEnv A} {α : Ty A} (h : Head τ Γ α Δ) :
    LLTyped τ Γ h.erase α Δ := by
  cases h with
  | var x => exact x.sound
  | const c => exact .const _ c

mutual
/-- A value is typed by the paper's system. -/
theorem Val.sound {Γ Δ : FEnv A} {α : Ty A} : (v : Val τ Γ α Δ) → LLTyped τ Γ v.erase α Δ
  | .head h => h.sound
  | .lam b => .abs b.sound
/-- A computation is typed by the paper's system. -/
theorem Comp.sound {Γ Δ : FEnv A} {α : Ty A} : (c : Comp τ Γ α Δ) → LLTyped τ Γ c.erase α Δ
  | .app h v => .app h.sound v.sound
/-- **Soundness.** A statement is typed by the paper's system, with the same environments. -/
theorem Stmt.sound {Γ Δ : FEnv A} {α : Ty A} : (s : Stmt τ Γ α Δ) → LLTyped τ Γ s.erase α Δ
  | .ret v => v.sound
  | .letE c b => .app (.abs b.sound) c.sound
end

/-- Every free unknown of a statement is used at most once, and every `λ` and every `let`
    binds exactly one occurrence. -/
theorem Stmt.quasiLinear {Γ Δ : FEnv A} {α : Ty A} (s : Stmt τ Γ α Δ) :
    QuasiLinear s.erase :=
  s.sound.quasiLinear

/-- The erasure of a closed A-normal program is a linear λ-term, simply typed in the empty
    environment. -/
theorem AProgram.linear {α : Ty A} (p : AProgram τ α) :
    Linear p.erase ∧ STTyped τ [] p.erase α := by
  have h := (llTyped_minenv_iff (τ := τ) (Γ := []) (t := p.erase) (α := α)).1 p.sound
  exact ⟨h.1, h.2.2⟩

/-- A head is never a `λ`. -/
theorem Head.erase_ne_lam {Γ Δ : FEnv A} {α : Ty A} (h : Head τ Γ α Δ) (s : Term C) :
    h.erase ≠ .lam s := by
  cases h <;> simp [Head.erase]

/-- The callee of a computation is never a `λ`. -/
theorem Comp.head_ne_lam {Γ Δ : FEnv A} {α : Ty A} (c : Comp τ Γ α Δ) :
    ∃ f a : Term C, c.erase = .app f a ∧ ∀ s, f ≠ .lam s := by
  cases c with
  | app h v => exact ⟨h.erase, v.erase, rfl, h.erase_ne_lam⟩

/-- The typed A-normal statements are closed under β-reduction of their erasure, as terms of
    the first toy grammar (`Tm`), between the same environments. -/
theorem Stmt.subject_reduction {Γ Δ : FEnv A} {α : Ty A} (s : Stmt τ Γ α Δ) {u : Term C}
    (h : BetaRed s.erase u) : ∃ e : Tm τ Γ α Δ, e.erase = u :=
  Tm.complete (s.sound.subject_reduction_star h)

end Toy

end LinearDB

end
