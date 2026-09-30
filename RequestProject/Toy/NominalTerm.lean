module

public import RequestProject.Toy.Nominal
public import RequestProject.Toy.Term

@[expose] public section

set_option autoImplicit false

/-!
# Toy normal forms over named datatypes and delays

The term grammar that goes with `LinearDB.Toy.NTy`: β-normal linear terms, indexed by the
paper's judgement `{Γ} t : α {Δ}` (the variables available before, the type, the variables
left over), with a delay and its force.

```
NVar Γ α Δ ::= here | there₁ β NVar | there₂ NVar     -- use one slot
NNeu Γ α Δ ::= var NVar | const c
             | app NNeu NNf                            -- call something stuck
             | force NNeu                              -- force something stuck
NNf  Γ α Δ ::= neu NNeu | lam NNf | delay NNf
```

`Γ, Δ : NEnv n` are fragmentary environments of toy types (`none` = a used slot).  The
constructors of the datatypes are constants `c : C`, typed by `τ : C → NTy n`.

What cannot be written:

* a variable used twice, or a parameter never used (`NNf.sound`, then `NNf.quasiLinear`);
* a β-redex `(λ t) u`: the function of an `app` is neutral (`NNf.normal`);
* a forced literal delay `force (delay t)`: `force` takes a neutral term, `delay` builds a
  normal form, so a delay is only forced when it is stuck;
* a delay of a delay: `delay` builds `lazy α` from `α : NTy n false`
  (`NTy.lazy_not_in_lazy`).

Delays are evaluated as the identity: the erasure to the paper's untyped terms drops `delay`
and `force`, and the erasure of types (`NTy.toTy`) drops `lazy`, so every normal form is typed
by the paper's system (`NNf.sound`), and a closed program is a linear λ-term
(`NProgram.linear`).
-/

namespace LinearDB

namespace Toy

open Term

variable {n : Nat} {C : Type}

/-- Fragmentary environments of toy types. -/
abbrev NEnv (n : Nat) : Type := List (Option (NTy n))

/-- The paper's fragmentary environment of a toy one. -/
def NEnv.toFEnv (Γ : NEnv n) : FEnv (Base ⊕ Fin n) := Γ.map (Option.map NTy.toTy)

/-- A variable occurrence: it consumes one slot. -/
inductive NVar {n : Nat} : NEnv n → NTy n → NEnv n → Type where
  | here (Γ : NEnv n) (α : NTy n) : NVar (some α :: Γ) α (none :: Γ)
  | there₁ {Γ Δ : NEnv n} {α : NTy n} (β : NTy n) : NVar Γ α Δ → NVar (some β :: Γ) α (some β :: Δ)
  | there₂ {Γ Δ : NEnv n} {α : NTy n} : NVar Γ α Δ → NVar (none :: Γ) α (none :: Δ)

/-- The de Bruijn index of a variable. -/
def NVar.idx {Γ Δ : NEnv n} {α : NTy n} : NVar Γ α Δ → ℕ
  | .here _ _ => 0
  | .there₁ _ x => x.idx + 1
  | .there₂ x => x.idx + 1

mutual
/-- **Neutral terms**: a variable or a constant, called or forced. -/
inductive NNeu {n : Nat} {C : Type} (τ : C → NTy n) : NEnv n → NTy n → NEnv n → Type where
  | var {Γ Δ : NEnv n} {α : NTy n} : NVar Γ α Δ → NNeu τ Γ α Δ
  | const {Γ : NEnv n} (c : C) : NNeu τ Γ (τ c) Γ
  | app {Γ Δ Θ : NEnv n} {α β : NTy n} : NNeu τ Γ (.fn α β) Δ → NNf τ Δ α Θ → NNeu τ Γ β Θ
  | force {Γ Δ : NEnv n} {α : NTy n false} : NNeu τ Γ (.lazy α) Δ → NNeu τ Γ α.relax Δ
/-- **Normal forms**: a neutral term, a `λ`, or a delay. -/
inductive NNf {n : Nat} {C : Type} (τ : C → NTy n) : NEnv n → NTy n → NEnv n → Type where
  | neu {Γ Δ : NEnv n} {α : NTy n} : NNeu τ Γ α Δ → NNf τ Γ α Δ
  | lam {Γ Δ : NEnv n} {α β : NTy n} : NNf τ (some α :: Γ) β (none :: Δ) → NNf τ Γ (.fn α β) Δ
  | delay {Γ Δ : NEnv n} {α : NTy n false} : NNf τ Γ α.relax Δ → NNf τ Γ (.lazy α) Δ
end

/-- A closed program of type `α`. -/
abbrev NProgram (τ : C → NTy n) (α : NTy n) : Type := NNf τ [] α []

variable {τ : C → NTy n}

mutual
/-- The untyped term of a neutral term: `force` is the identity. -/
def NNeu.erase {Γ Δ : NEnv n} {α : NTy n} : NNeu τ Γ α Δ → Term C
  | .var x => .var x.idx
  | .const c => .const c
  | .app t u => .app t.erase u.erase
  | .force t => t.erase
/-- The untyped term of a normal form: `delay` is the identity. -/
def NNf.erase {Γ Δ : NEnv n} {α : NTy n} : NNf τ Γ α Δ → Term C
  | .neu t => t.erase
  | .lam t => .lam t.erase
  | .delay t => t.erase
end

/-- The paper's typing of the constants. -/
def NTy.constTy (τ : C → NTy n) : C → Ty (Base ⊕ Fin n) := fun c => (τ c).toTy

theorem NVar.sound {Γ Δ : NEnv n} {α : NTy n} (x : NVar Γ α Δ) :
    LLTyped (NTy.constTy τ) Γ.toFEnv (.var x.idx) α.toTy Δ.toFEnv := by
  induction x with
  | here Γ α => exact .var _ _
  | there₁ β _ ih => exact .weak₁ _ ih
  | there₂ _ ih => exact .weak₂ ih

/-- **Soundness.** A normal form is typed by the paper's system (Figure 4), with the erased
    environments and type. -/
theorem NNf.sound {Γ Δ : NEnv n} {α : NTy n} (t : NNf τ Γ α Δ) :
    LLTyped (NTy.constTy τ) Γ.toFEnv t.erase α.toTy Δ.toFEnv := by
  induction t using NNf.rec
    (motive_1 := fun Γ α Δ t => LLTyped (NTy.constTy τ) Γ.toFEnv t.erase α.toTy Δ.toFEnv) with
  | var x => exact x.sound
  | const c => exact .const _ c
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | force _ ih => simpa [NNeu.erase] using ih
  | neu _ ih => exact ih
  | lam _ ih => exact .abs ih
  | delay _ ih => simpa [NNf.erase] using ih

/-- Every free variable is used at most once, and every `λ` uses its parameter exactly once. -/
theorem NNf.quasiLinear {Γ Δ : NEnv n} {α : NTy n} (t : NNf τ Γ α Δ) : QuasiLinear t.erase :=
  t.sound.quasiLinear

/-- A closed program is a linear λ-term, simply typed in the empty environment. -/
theorem NProgram.linear {α : NTy n} (p : NProgram τ α) :
    Linear p.erase ∧ STTyped (NTy.constTy τ) [] p.erase α.toTy := by
  have h := (llTyped_minenv_iff (τ := NTy.constTy τ) (Γ := []) (t := p.erase)
    (α := α.toTy)).1 p.sound
  exact ⟨h.1, h.2.2⟩

/-- The erasure of a neutral term is never a `λ`. -/
theorem NNeu.erase_ne_lam {Γ Δ : NEnv n} {α : NTy n} (t : NNeu τ Γ α Δ) (s : Term C) :
    t.erase ≠ .lam s := by
  induction t using NNeu.rec (motive_2 := fun _ _ _ _ => True) with
  | force _ ih => simpa [NNeu.erase] using ih
  | _ => simp_all [NNeu.erase]

/-- **A normal form contains no β-redex.** -/
theorem NNf.normal {Γ Δ : NEnv n} {α : NTy n} (t : NNf τ Γ α Δ) : Normal t.erase := by
  induction t using NNf.rec (motive_1 := fun _ _ _ m => Normal m.erase) with
  | var x => intro u hu; cases hu
  | const c => intro u hu; cases hu
  | @app _ _ _ _ _ f a ih₁ ih₂ =>
    have key : ∀ a b u : Term C, Beta (.app a b) u → Normal a → Normal b →
        (∀ s, a ≠ .lam s) → False := by
      intro a b u hu ha hb hl
      cases hu with
      | beta b' _ => exact hl b' rfl
      | appL _ h => exact ha _ h
      | appR _ h => exact hb _ h
    exact fun u hu => key _ _ u hu ih₁ ih₂ f.erase_ne_lam
  | force _ ih => simpa [NNeu.erase] using ih
  | neu _ ih => simpa [NNf.erase] using ih
  | lam _ ih =>
    intro u hu
    cases hu with
    | lam h => exact ih _ h
  | delay _ ih => simpa [NNf.erase] using ih

end Toy

end LinearDB

end
