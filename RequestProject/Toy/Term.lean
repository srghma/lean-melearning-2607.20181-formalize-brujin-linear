module

public import RequestProject.Toy.Ty
public import RequestProject.SubjectReduction

@[expose] public section

set_option autoImplicit false

/-!
# Toy terms: linear λ-terms that cannot be written non-linearly

The grammar of terms of the toy language.  Every class is indexed, exactly as the judgement
`{Γ} t : α {Δ}` of the paper (Figure 4, `LinearDB.LLTyped`), by an **input** fragmentary
environment `Γ`, a type `α`, and an **output** fragmentary environment `Δ`: the variables of
`Γ` that the term has *not* used.  A variable, once used, is `⊥` (`none`) in the output, so it
cannot be used again.

```
Var  Γ α Δ   ::= here                          -- {α, Γ} 0 : α {⊥, Γ}
               | there₁ β Var | there₂ Var     -- skip a live / a used slot
Tm   Γ α Δ   ::= var Var | const c
               | app Tm Tm                     -- threads the environment left to right
               | lam Tm                        -- the parameter must be consumed
Neu  Γ α Δ   ::= var Var | const c | app Neu Nf
Nf   Γ α Δ   ::= neu Neu | lam Nf
```

**The environments.**  `app t u` runs `t` from `Γ` to `Δ`, then `u` from `Δ` to `Θ`
(rule (app)), so a variable used by `t` is no longer available to `u`.  `lam b` extends the
input with its parameter `α` and requires the body to end with `⊥` in its place (rule (abs)):
the parameter is used, and used once.

**Normal forms.**  `Neu` / `Nf` is the sub-grammar of β-normal terms: an application's head is
a `Neu` (a variable, a constant, or an application), never a `lam`, so a redex `(λ t) u`
cannot be written (`Nf.normal`), and every β-normal typed term can (`Nf.complete`).

What cannot be written:

* a variable used twice, or not at all under its `λ` (`Tm.sound`, then the paper's
  `LLTyped.quasiLinear`: every free index occurs at most once, and every `λ` binds exactly one
  occurrence);
* a closed program (`Program`: from `[]` to `[]`) whose erasure is not a linear λ-term
  (`Program.linear`, from the paper's characterisation `llTyped_minenv_iff`);
* a β-redex in a normal form (`Nf.normal`).

Conversely nothing is lost: the typed terms are exactly the terms the paper types
(`Tm.sound`, `Tm.complete`), and the normal forms exactly the β-normal ones among them.
-/

namespace LinearDB

namespace Toy

open Term

variable {A C : Type}

/-! ## Variables -/

/-- A variable occurrence in `Γ`, of type `α`, leaving `Δ`: it consumes one slot.  These are
    the rules (var), (weak₁), (weak₂) of Figure 4. -/
inductive Var : FEnv A → Ty A → FEnv A → Type where
  /-- Index `0`: consume the newest slot. -/
  | here (Γ : FEnv A) (α : Ty A) : Var (some α :: Γ) α (none :: Γ)
  /-- Skip a slot that is still live. -/
  | there₁ {Γ Δ : FEnv A} {α : Ty A} (β : Ty A) : Var Γ α Δ → Var (some β :: Γ) α (some β :: Δ)
  /-- Skip a slot that is already used. -/
  | there₂ {Γ Δ : FEnv A} {α : Ty A} : Var Γ α Δ → Var (none :: Γ) α (none :: Δ)

/-- The de Bruijn index of a variable. -/
def Var.idx {Γ Δ : FEnv A} {α : Ty A} : Var Γ α Δ → ℕ
  | .here _ _ => 0
  | .there₁ _ x => x.idx + 1
  | .there₂ x => x.idx + 1

/-! ## Terms -/

/-- Linear terms over constants `C` typed by `τ`, from `Γ` to `Δ`. -/
inductive Tm (τ : C → Ty A) : FEnv A → Ty A → FEnv A → Type where
  | var {Γ Δ : FEnv A} {α : Ty A} : Var Γ α Δ → Tm τ Γ α Δ
  | const {Γ : FEnv A} (c : C) : Tm τ Γ (τ c) Γ
  | app {Γ Δ Θ : FEnv A} {α β : Ty A} : Tm τ Γ (.arr α β) Δ → Tm τ Δ α Θ → Tm τ Γ β Θ
  | lam {Γ Δ : FEnv A} {α β : Ty A} : Tm τ (some α :: Γ) β (none :: Δ) → Tm τ Γ (.arr α β) Δ

mutual
/-- **Neutral terms**: a variable or a constant applied to normal forms. -/
inductive Neu (τ : C → Ty A) : FEnv A → Ty A → FEnv A → Type where
  | var {Γ Δ : FEnv A} {α : Ty A} : Var Γ α Δ → Neu τ Γ α Δ
  | const {Γ : FEnv A} (c : C) : Neu τ Γ (τ c) Γ
  | app {Γ Δ Θ : FEnv A} {α β : Ty A} : Neu τ Γ (.arr α β) Δ → Nf τ Δ α Θ → Neu τ Γ β Θ
/-- **Normal forms**: a neutral term, or a `λ` of a normal form. -/
inductive Nf (τ : C → Ty A) : FEnv A → Ty A → FEnv A → Type where
  | neu {Γ Δ : FEnv A} {α : Ty A} : Neu τ Γ α Δ → Nf τ Γ α Δ
  | lam {Γ Δ : FEnv A} {α β : Ty A} : Nf τ (some α :: Γ) β (none :: Δ) → Nf τ Γ (.arr α β) Δ
end

/-- A closed program of type `α`: no free variable is available, none is left over. -/
abbrev Program (τ : C → Ty A) (α : Ty A) : Type := Nf τ [] α []

variable {τ : C → Ty A}

/-! ## Erasure to the untyped de Bruijn terms of the paper -/

/-- The untyped term of a typed term. -/
def Tm.erase {Γ Δ : FEnv A} {α : Ty A} : Tm τ Γ α Δ → Term C
  | .var x => .var x.idx
  | .const c => .const c
  | .app t u => .app t.erase u.erase
  | .lam t => .lam t.erase

mutual
/-- The untyped term of a neutral term. -/
def Neu.erase {Γ Δ : FEnv A} {α : Ty A} : Neu τ Γ α Δ → Term C
  | .var x => .var x.idx
  | .const c => .const c
  | .app t u => .app t.erase u.erase
/-- The untyped term of a normal form. -/
def Nf.erase {Γ Δ : FEnv A} {α : Ty A} : Nf τ Γ α Δ → Term C
  | .neu n => n.erase
  | .lam t => .lam t.erase
end

mutual
/-- A neutral term as a term. -/
def Neu.toTm {Γ Δ : FEnv A} {α : Ty A} : Neu τ Γ α Δ → Tm τ Γ α Δ
  | .var x => .var x
  | .const c => .const c
  | .app t u => .app t.toTm u.toTm
/-- A normal form as a term. -/
def Nf.toTm {Γ Δ : FEnv A} {α : Ty A} : Nf τ Γ α Δ → Tm τ Γ α Δ
  | .neu n => n.toTm
  | .lam t => .lam t.toTm
end

/-! ## Soundness: the typed terms are typed by the paper's system -/

/-- A variable is typed by rules (var), (weak₁), (weak₂). -/
theorem Var.sound {Γ Δ : FEnv A} {α : Ty A} (x : Var Γ α Δ) :
    LLTyped τ Γ (.var x.idx) α Δ := by
  induction x with
  | here Γ α => exact .var Γ α
  | there₁ β _ ih => exact .weak₁ β ih
  | there₂ _ ih => exact .weak₂ ih

/-- **Soundness.** The erasure of a typed term is typed by Figure 4, with the same input and
    output environments. -/
theorem Tm.sound {Γ Δ : FEnv A} {α : Ty A} (t : Tm τ Γ α Δ) : LLTyped τ Γ t.erase α Δ := by
  induction t with
  | var x => exact x.sound
  | const c => exact .const _ c
  | app _ _ ih₁ ih₂ => exact .app ih₁ ih₂
  | lam _ ih => exact .abs ih

theorem Neu.erase_toTm {Γ Δ : FEnv A} {α : Ty A} (n : Neu τ Γ α Δ) : n.toTm.erase = n.erase := by
  induction n using Neu.rec (motive_2 := fun _ _ _ m => m.toTm.erase = m.erase) with
  | var x => rfl
  | const c => rfl
  | app _ _ ih₁ ih₂ => simp [Neu.toTm, Neu.erase, Tm.erase, ih₁, ih₂]
  | neu _ ih => simpa [Nf.toTm, Nf.erase] using ih
  | lam _ ih => simp [Nf.toTm, Nf.erase, Tm.erase, ih]

theorem Nf.erase_toTm {Γ Δ : FEnv A} {α : Ty A} (n : Nf τ Γ α Δ) : n.toTm.erase = n.erase := by
  induction n using Nf.rec (motive_1 := fun _ _ _ m => m.toTm.erase = m.erase) with
  | var x => rfl
  | const c => rfl
  | app _ _ ih₁ ih₂ => simp [Neu.toTm, Neu.erase, Tm.erase, ih₁, ih₂]
  | neu _ ih => simpa [Nf.toTm, Nf.erase] using ih
  | lam _ ih => simp [Nf.toTm, Nf.erase, Tm.erase, ih]

/-- **Soundness** for normal forms. -/
theorem Nf.sound {Γ Δ : FEnv A} {α : Ty A} (n : Nf τ Γ α Δ) : LLTyped τ Γ n.erase α Δ := by
  simpa [Nf.erase_toTm] using n.toTm.sound

/-- Every free index of a typed term occurs at most once, and every `λ` binds exactly one
    occurrence (the paper's quasi-linearity). -/
theorem Tm.quasiLinear {Γ Δ : FEnv A} {α : Ty A} (t : Tm τ Γ α Δ) : QuasiLinear t.erase :=
  t.sound.quasiLinear

/-! ## Completeness: every term typed by the paper's system can be written -/

/-- A variable typing judgement is a `Var`. -/
theorem Var.complete {Γ Δ : FEnv A} {α : Ty A} {i : ℕ} (h : LLTyped τ Γ (.var i) α Δ) :
    ∃ x : Var Γ α Δ, x.idx = i := by
  generalize ht : (Term.var i : Term C) = t at h
  induction h generalizing i with
  | const => cases ht
  | var Γ α => cases ht; exact ⟨.here Γ α, rfl⟩
  | weak₁ β _ ih =>
    cases ht; obtain ⟨x, hx⟩ := ih rfl; exact ⟨.there₁ β x, by simp [Var.idx, hx]⟩
  | weak₂ _ ih =>
    cases ht; obtain ⟨x, hx⟩ := ih rfl; exact ⟨.there₂ x, by simp [Var.idx, hx]⟩
  | app => cases ht
  | abs => cases ht

/-- **Completeness.** Every term typed by Figure 4 is the erasure of a typed term. -/
theorem Tm.complete {Γ Δ : FEnv A} {α : Ty A} {t : Term C} (h : LLTyped τ Γ t α Δ) :
    ∃ e : Tm τ Γ α Δ, e.erase = t := by
  induction h with
  | const Γ c => exact ⟨.const c, rfl⟩
  | var Γ α => exact ⟨.var (.here Γ α), rfl⟩
  | weak₁ β h _ =>
    obtain ⟨x, hx⟩ := Var.complete (LLTyped.weak₁ β h)
    exact ⟨.var x, by simp [Tm.erase, hx]⟩
  | weak₂ h _ =>
    obtain ⟨x, hx⟩ := Var.complete (LLTyped.weak₂ h)
    exact ⟨.var x, by simp [Tm.erase, hx]⟩
  | app _ _ ih₁ ih₂ =>
    obtain ⟨e₁, rfl⟩ := ih₁; obtain ⟨e₂, rfl⟩ := ih₂
    exact ⟨.app e₁ e₂, rfl⟩
  | abs _ ih =>
    obtain ⟨e, rfl⟩ := ih
    exact ⟨.lam e, rfl⟩

/-- The typed terms are exactly the terms typed by the paper's system. -/
theorem llTyped_iff_exists_tm {Γ Δ : FEnv A} {α : Ty A} {t : Term C} :
    LLTyped τ Γ t α Δ ↔ ∃ e : Tm τ Γ α Δ, e.erase = t :=
  ⟨Tm.complete, fun ⟨e, he⟩ => he ▸ e.sound⟩

/-! ## Normal forms -/

/-- A term is β-normal if it does not β-contract. -/
def Normal (t : Term C) : Prop := ∀ u, ¬ Beta t u

theorem Normal.app_left {t s : Term C} (h : Normal (.app t s)) : Normal t :=
  fun _ hu => h _ (Beta.appL s hu)

theorem Normal.app_right {t s : Term C} (h : Normal (.app t s)) : Normal s :=
  fun _ hu => h _ (Beta.appR t hu)

theorem Normal.of_lam {t : Term C} (h : Normal (.lam t)) : Normal t :=
  fun _ hu => h _ (Beta.lam hu)

/-- The erasure of a neutral term is never a `λ`. -/
theorem Neu.erase_ne_lam {Γ Δ : FEnv A} {α : Ty A} (n : Neu τ Γ α Δ) (s : Term C) :
    n.erase ≠ .lam s := by
  cases n <;> simp [Neu.erase]

/-- **A normal form contains no redex.** -/
theorem Nf.normal {Γ Δ : FEnv A} {α : Ty A} (n : Nf τ Γ α Δ) : Normal n.erase := by
  induction n using Nf.rec (motive_1 := fun _ _ _ m => Normal m.erase) with
  | var x => intro u hu; cases hu
  | const c => intro u hu; cases hu
  | @app _ _ _ _ _ t s ih₁ ih₂ =>
    have key : ∀ a b u : Term C, Beta (.app a b) u → Normal a → Normal b →
        (∀ s, a ≠ .lam s) → False := by
      intro a b u hu ha hb hl
      cases hu with
      | beta b' _ => exact hl b' rfl
      | appL _ h => exact ha _ h
      | appR _ h => exact hb _ h
    exact fun u hu => key _ _ u hu ih₁ ih₂ t.erase_ne_lam
  | neu _ ih => simpa [Nf.erase] using ih
  | lam _ ih =>
    intro u hu
    cases hu with
    | lam h => exact ih _ h

/-- **Completeness of normal forms**, strengthened: a β-normal typed term is a normal form,
    and a neutral term if it is not a `λ`. -/
theorem Nf.complete_aux {Γ Δ : FEnv A} {α : Ty A} {t : Term C} (h : LLTyped τ Γ t α Δ)
    (hn : Normal t) :
    (∃ e : Nf τ Γ α Δ, e.erase = t) ∧ ((∀ s, t ≠ .lam s) → ∃ e : Neu τ Γ α Δ, e.erase = t) := by
  suffices hneu : (∀ s, t ≠ .lam s) → ∃ e : Neu τ Γ α Δ, e.erase = t by
    refine ⟨?_, hneu⟩
    cases h with
    | abs hb =>
      obtain ⟨e, he⟩ := (Nf.complete_aux hb hn.of_lam).1
      exact ⟨.lam e, by simp [Nf.erase, he]⟩
    | _ =>
      obtain ⟨e, he⟩ := hneu (fun s hs => by cases hs)
      exact ⟨.neu e, by simpa [Nf.erase] using he⟩
  intro hl
  cases h with
  | const Γ c => exact ⟨.const c, rfl⟩
  | var Γ α => exact ⟨.var (.here Γ α), rfl⟩
  | weak₁ β h =>
    obtain ⟨x, hx⟩ := Var.complete (LLTyped.weak₁ β h)
    exact ⟨.var x, by simp [Neu.erase, hx]⟩
  | weak₂ h =>
    obtain ⟨x, hx⟩ := Var.complete (LLTyped.weak₂ h)
    exact ⟨.var x, by simp [Neu.erase, hx]⟩
  | @app _ _ _ t₁ t₂ _ _ h₁ h₂ =>
    have hn₁ := hn.app_left
    have hn₂ := hn.app_right
    have hnl : ∀ s, t₁ ≠ .lam s := by
      rintro s rfl; exact hn _ (Beta.beta s t₂)
    obtain ⟨e₁, he₁⟩ := (Nf.complete_aux h₁ hn₁).2 hnl
    obtain ⟨e₂, he₂⟩ := (Nf.complete_aux h₂ hn₂).1
    exact ⟨.app e₁ e₂, by simp [Neu.erase, he₁, he₂]⟩
  | abs => exact absurd rfl (hl _)
termination_by sizeOf t

/-- **Completeness of normal forms.** Every β-normal term typed by Figure 4 is the erasure of
    a normal form. -/
theorem Nf.complete {Γ Δ : FEnv A} {α : Ty A} {t : Term C} (h : LLTyped τ Γ t α Δ)
    (hn : Normal t) : ∃ e : Nf τ Γ α Δ, e.erase = t :=
  (Nf.complete_aux h hn).1

/-! ## Closed programs are linear -/

/-- The erasure of a closed program is a linear λ-term, simply typed in the empty
    environment (the paper's `llTyped_minenv_iff` at `Γ = []`). -/
theorem Program.linear {α : Ty A} (p : Program τ α) :
    Linear p.erase ∧ STTyped τ [] p.erase α := by
  have h := (llTyped_minenv_iff (τ := τ) (Γ := []) (t := p.erase) (α := α)).1 p.sound
  exact ⟨h.1, h.2.2⟩

/-- More generally, a normal form that consumes all of a typing environment `Γ` erases to a
    linear λ-term for which `Γ` is minimal. -/
theorem Nf.linear_of_consumes {Γ : Env A} {α : Ty A}
    (n : Nf τ (FEnv.ofEnv Γ) α (FEnv.minenv Γ.length)) :
    Linear n.erase ∧ Minimal Γ n.erase ∧ STTyped τ Γ n.erase α :=
  llTyped_minenv_iff.1 n.sound

/-- Typed terms are closed under β-reduction of their erasure (the paper's subject reduction):
    a reduct of a typed term is again a typed term, between the same environments. -/
theorem Tm.subject_reduction {Γ Δ : FEnv A} {α : Ty A} (e : Tm τ Γ α Δ) {u : Term C}
    (h : BetaRed e.erase u) : ∃ e' : Tm τ Γ α Δ, e'.erase = u :=
  Tm.complete (e.sound.subject_reduction_star h)

end Toy

end LinearDB

end
