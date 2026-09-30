module

public import RequestProject.Toy.LinearLogic

@[expose] public section

set_option autoImplicit false

/-!
# ToyLinearLogic2: classical linear logic with Hodas–Miller input / output contexts

The same sequent calculus as `ToyLinearLogic` (`Toy/LinearLogic.lean`), presented with the
resource management of the paper's judgement `{Γ} t : α {Δ}` (Hodas–Miller style): a
derivation `t : IO Γ Δ`, written `{Γ} t {Δ}`, receives an **input** environment `Γ` of slots
and returns an **output** environment `Δ`, the slots it has not used.

A slot holds a *signed formula*: `L A` is a hypothesis `A` (left of `⊢`), `R A` a conclusion
`A` (right of `⊢`), and an empty slot (`none`, the paper's `⊥`) is a formula already used.
The judgement `{Γ} t : A {Δ}` (`Proves Γ A Δ`) is `{R A, Γ} t {⊥, Δ}`: `t` proves `A` from the
resources of `Γ`, leaving `Δ`.

Each rule uses its principal formula through a slot (`Res.Slot`, the analogue of the paper's
rules (var), (weak₁), (weak₂)), pushes the active formulas as new slots, and requires them to
be empty at the end of the premise, exactly as the paper's rule (abs) does for a λ.  The
multiplicative rules (cut, `R⊗`, `L⅋`) thread the environment from the first premise to the
second, as the paper's rule (app) does; the additive rules (`R&`, `L⊕`) run both premises from
the same input to the same output.  No context splitting is ever guessed, and exchange is not a
rule: slots are named by position.  The promotion rules `! R` and `? L` require every other
formula they use to be a `!`-hypothesis or a `?`-conclusion (`ExpOnly`).

Results:

* **soundness** (`IO.sound`): `{Γ} t {Δ}` gives a `ToyLinearLogic` derivation of the sequent
  made of the formulas it used;
* **completeness** (`CLL.toIO`): every `ToyLinearLogic` derivation of `Γ ⊢ Ψ` gives `{Γ₀} t {Δ₀}`
  whenever `Δ₀ ⊑ Γ₀` and the resources used between them are `Γ ⊢ Ψ`, in any order;
* hence the two calculi prove the same sequents (`derivable_iff_io`);
* the paper's judgement carries over: every typed A-normal statement
  `{Γ} s : α {Δ}` (`Toy/Anf.lean`) gives `{Γ, !Θ} t : ⟦α⟧ {Δ, ⊥…⊥}` here, the environments
  `Γ`, `Δ` being read as hypotheses and `!Θ` being `!`-hypotheses from which the constants
  follow (`Stmt.toIO`).
-/

namespace LinearDB

namespace ToyLinearLogic2

open ToyLinearLogic Toy Res

variable {A : Type}

/-- A signed formula: a hypothesis `L A` or a conclusion `R A`. -/
inductive SFml (A : Type) where
  | L : Fml A → SFml A
  | R : Fml A → SFml A
  deriving DecidableEq

namespace SFml

/-- The formula of a hypothesis. -/
def getL : SFml A → Option (Fml A)
  | .L a => some a
  | .R _ => none

/-- The formula of a conclusion. -/
def getR : SFml A → Option (Fml A)
  | .L _ => none
  | .R a => some a

/-- The formulas that may stay around a promotion: `!`-hypotheses and `?`-conclusions. -/
def Exponential : SFml A → Prop
  | .L (.bang _) => True
  | .R (.quest _) => True
  | _ => False

end SFml

/-- Resource environments of signed formulas (`none` is a used slot). -/
abbrev REnv (A : Type) := List (Option (SFml A))

/-- The hypotheses among signed formulas. -/
def lefts (c : List (SFml A)) : List (Fml A) := c.filterMap SFml.getL

/-- The conclusions among signed formulas. -/
def rights (c : List (SFml A)) : List (Fml A) := c.filterMap SFml.getR

/-- Everything used between `Γ` and `Δ` is a `!`-hypothesis or a `?`-conclusion. -/
def ExpOnly (Γ Δ : REnv A) : Prop := ∀ s ∈ consumed Γ Δ, s.Exponential

/-- **Derivations with input and output contexts**: `IO Γ Δ` is the type of derivations
    `{Γ} t {Δ}`. -/
inductive IO : REnv A → REnv A → Type where
  /-- Initial sequent: use a hypothesis `A` and a conclusion `A`. -/
  | ax {Γ₀ Γ₁ Γ₂ : REnv A} {a : Fml A} :
      Slot Γ₀ (.L a) Γ₁ → Slot Γ₁ (.R a) Γ₂ → IO Γ₀ Γ₂
  /-- Cut: prove `A`, then use it as a hypothesis with what is left. -/
  | cut {Γ₀ Γ₁ Γ₂ : REnv A} (a : Fml A) :
      IO (some (.R a) :: Γ₀) (none :: Γ₁) → IO (some (.L a) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  | negL {Γ₀ Γ₁ Γ₂ : REnv A} {a : Fml A} :
      Slot Γ₀ (.L (.neg a)) Γ₁ → IO (some (.R a) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  | negR {Γ₀ Γ₁ Γ₂ : REnv A} {a : Fml A} :
      Slot Γ₀ (.R (.neg a)) Γ₁ → IO (some (.L a) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  | tensorL {Γ₀ Γ₁ Γ₂ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.L (.tensor a b)) Γ₁ →
      IO (some (.L b) :: some (.L a) :: Γ₁) (none :: none :: Γ₂) → IO Γ₀ Γ₂
  | tensorR {Γ₀ Γ₁ Γ₂ Γ₃ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.R (.tensor a b)) Γ₁ → IO (some (.R a) :: Γ₁) (none :: Γ₂) →
      IO (some (.R b) :: Γ₂) (none :: Γ₃) → IO Γ₀ Γ₃
  | parL {Γ₀ Γ₁ Γ₂ Γ₃ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.L (.par a b)) Γ₁ → IO (some (.L a) :: Γ₁) (none :: Γ₂) →
      IO (some (.L b) :: Γ₂) (none :: Γ₃) → IO Γ₀ Γ₃
  | parR {Γ₀ Γ₁ Γ₂ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.R (.par a b)) Γ₁ →
      IO (some (.R b) :: some (.R a) :: Γ₁) (none :: none :: Γ₂) → IO Γ₀ Γ₂
  | withL₁ {Γ₀ Γ₁ Γ₂ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.L (.amp a b)) Γ₁ → IO (some (.L a) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  | withL₂ {Γ₀ Γ₁ Γ₂ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.L (.amp a b)) Γ₁ → IO (some (.L b) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  /-- Additive: both premises run from the same input to the same output. -/
  | withR {Γ₀ Γ₁ Γ₂ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.R (.amp a b)) Γ₁ → IO (some (.R a) :: Γ₁) (none :: Γ₂) →
      IO (some (.R b) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  | plusL {Γ₀ Γ₁ Γ₂ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.L (.plus a b)) Γ₁ → IO (some (.L a) :: Γ₁) (none :: Γ₂) →
      IO (some (.L b) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  | plusR₁ {Γ₀ Γ₁ Γ₂ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.R (.plus a b)) Γ₁ → IO (some (.R a) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  | plusR₂ {Γ₀ Γ₁ Γ₂ : REnv A} {a b : Fml A} :
      Slot Γ₀ (.R (.plus a b)) Γ₁ → IO (some (.R b) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  | bangW {Γ₀ Γ₁ Γ₂ : REnv A} {a : Fml A} :
      Slot Γ₀ (.L (.bang a)) Γ₁ → IO Γ₁ Γ₂ → IO Γ₀ Γ₂
  | bangC {Γ₀ Γ₁ Γ₂ : REnv A} {a : Fml A} :
      Slot Γ₀ (.L (.bang a)) Γ₁ →
      IO (some (.L (.bang a)) :: some (.L (.bang a)) :: Γ₁) (none :: none :: Γ₂) → IO Γ₀ Γ₂
  | bangD {Γ₀ Γ₁ Γ₂ : REnv A} {a : Fml A} :
      Slot Γ₀ (.L (.bang a)) Γ₁ → IO (some (.L a) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  | questW {Γ₀ Γ₁ Γ₂ : REnv A} {a : Fml A} :
      Slot Γ₀ (.R (.quest a)) Γ₁ → IO Γ₁ Γ₂ → IO Γ₀ Γ₂
  | questC {Γ₀ Γ₁ Γ₂ : REnv A} {a : Fml A} :
      Slot Γ₀ (.R (.quest a)) Γ₁ →
      IO (some (.R (.quest a)) :: some (.R (.quest a)) :: Γ₁) (none :: none :: Γ₂) → IO Γ₀ Γ₂
  | questD {Γ₀ Γ₁ Γ₂ : REnv A} {a : Fml A} :
      Slot Γ₀ (.R (.quest a)) Γ₁ → IO (some (.R a) :: Γ₁) (none :: Γ₂) → IO Γ₀ Γ₂
  /-- `! R`: everything else used must be a `!`-hypothesis or a `?`-conclusion. -/
  | bangR {Γ₀ Γ₁ Γ₂ : REnv A} {b : Fml A} :
      Slot Γ₀ (.R (.bang b)) Γ₁ → IO (some (.R b) :: Γ₁) (none :: Γ₂) → ExpOnly Γ₁ Γ₂ →
      IO Γ₀ Γ₂
  /-- `? L`: everything else used must be a `!`-hypothesis or a `?`-conclusion. -/
  | questL {Γ₀ Γ₁ Γ₂ : REnv A} {b : Fml A} :
      Slot Γ₀ (.L (.quest b)) Γ₁ → IO (some (.L b) :: Γ₁) (none :: Γ₂) → ExpOnly Γ₁ Γ₂ →
      IO Γ₀ Γ₂

/-- The Hodas–Miller judgement `{Γ} t : A {Δ}`: `t` proves `A` from the resources of `Γ`,
    leaving `Δ`. -/
abbrev Proves (Γ : REnv A) (a : Fml A) (Δ : REnv A) : Type := IO (some (.R a) :: Γ) (none :: Δ)

/-! ## Soundness -/

/-- The output of a derivation is its input with some slots used (the paper's Lemma `subeq`). -/
theorem IO.le {Γ Δ : REnv A} (d : IO Γ Δ) : Le Δ Γ := by
  induction d with
  | ax s₁ s₂ => exact le_trans s₂.le s₁.le
  | cut _ _ _ ih₁ ih₂ => exact le_trans (le_cons_cons.1 ih₂).2 (le_cons_cons.1 ih₁).2
  | negL s _ ih | negR s _ ih | withL₁ s _ ih | withL₂ s _ ih | plusR₁ s _ ih
  | plusR₂ s _ ih | bangD s _ ih | questD s _ ih | withR s _ _ ih _ | plusL s _ _ ih _
  | bangR s _ _ ih | questL s _ _ ih => exact le_trans (le_cons_cons.1 ih).2 s.le
  | tensorL s _ ih | parR s _ ih | bangC s _ ih | questC s _ ih =>
    exact le_trans (le_cons_cons.1 (le_cons_cons.1 ih).2).2 s.le
  | tensorR s _ _ ih₁ ih₂ | parL s _ _ ih₁ ih₂ =>
    exact le_trans (le_trans (le_cons_cons.1 ih₂).2 (le_cons_cons.1 ih₁).2) s.le
  | bangW s _ ih | questW s _ ih => exact le_trans ih s.le

/-- Proves a permutation between two explicit lists by counting. -/
local macro "perm_tac" : tactic =>
  `(tactic| (classical
             exact List.perm_iff_count.2 fun _ => by
               simp [List.count_cons, List.count_append] <;> omega))


@[simp] lemma lefts_nil : lefts ([] : List (SFml A)) = [] := rfl
@[simp] lemma rights_nil : rights ([] : List (SFml A)) = [] := rfl
@[simp] lemma lefts_cons_L (a : Fml A) (c : List (SFml A)) : lefts (.L a :: c) = a :: lefts c :=
  rfl
@[simp] lemma lefts_cons_R (a : Fml A) (c : List (SFml A)) : lefts (.R a :: c) = lefts c := rfl
@[simp] lemma rights_cons_L (a : Fml A) (c : List (SFml A)) : rights (.L a :: c) = rights c :=
  rfl
@[simp] lemma rights_cons_R (a : Fml A) (c : List (SFml A)) :
    rights (.R a :: c) = a :: rights c := rfl
@[simp] lemma lefts_map_L (Γ : List (Fml A)) : lefts (Γ.map .L) = Γ := by
  induction Γ <;> simp_all
@[simp] lemma lefts_map_R (Γ : List (Fml A)) : lefts (Γ.map .R) = [] := by
  induction Γ <;> simp_all
@[simp] lemma rights_map_L (Γ : List (Fml A)) : rights (Γ.map .L) = [] := by
  induction Γ <;> simp_all
@[simp] lemma rights_map_R (Γ : List (Fml A)) : rights (Γ.map .R) = Γ := by
  induction Γ <;> simp_all
@[simp] lemma lefts_append (c c' : List (SFml A)) : lefts (c ++ c') = lefts c ++ lefts c' :=
  List.filterMap_append
@[simp] lemma rights_append (c c' : List (SFml A)) :
    rights (c ++ c') = rights c ++ rights c' := List.filterMap_append

/-- Computes the formulas used by a derivation whose new slots are all consumed. -/
local macro "io_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [consumed_cons_cons, step_some_none, List.singleton_append, lefts_cons_R,
      rights_cons_R, lefts_cons_L, rights_cons_L, lefts_append, rights_append] $[$loc]?)

lemma derivable_transport {c c' : List (SFml A)} (hc : c.Perm c')
    (d : Derivable (lefts c') (rights c')) : Derivable (lefts c) (rights c) :=
  d.perm (hc.filterMap _).symm (hc.filterMap _).symm

lemma consumed_slot {Γ₀ Γ₁ Γ₂ : REnv A} {x : SFml A} (s : Slot Γ₀ x Γ₁) (h : Le Γ₂ Γ₁) :
    (consumed Γ₀ Γ₂).Perm (x :: consumed Γ₁ Γ₂) := by
  simpa [s.consumed] using consumed_trans h s.le

lemma consumed_slot₂ {Γ₀ Γ₁ Γ₂ Γ₃ : REnv A} {x : SFml A} (s : Slot Γ₀ x Γ₁) (h₁ : Le Γ₂ Γ₁)
    (h₂ : Le Γ₃ Γ₂) :
    (consumed Γ₀ Γ₃).Perm (x :: (consumed Γ₁ Γ₂ ++ consumed Γ₂ Γ₃)) :=
  (consumed_slot s (le_trans h₂ h₁)).trans ((consumed_trans h₂ h₁).cons x)

lemma exists_of_expOnly {c : List (SFml A)} (h : ∀ s ∈ c, s.Exponential) :
    ∃ Γ Ψ : List (Fml A), lefts c = Γ.map .bang ∧ rights c = Ψ.map .quest := by
  induction c with
  | nil => exact ⟨[], [], rfl, rfl⟩
  | cons s c ih =>
    obtain ⟨Γ, Ψ, h₁, h₂⟩ := ih fun t ht => h t (by simp [ht])
    have hs := h s (by simp)
    rcases s with (_ | _ | _ | _ | _ | _ | a | _) | (_ | _ | _ | _ | _ | _ | _ | a) <;>
      simp [SFml.Exponential] at hs
    · exact ⟨a :: Γ, Ψ, by simp [h₁], by simp [h₂]⟩
    · exact ⟨Γ, a :: Ψ, by simp [h₁], by simp [h₂]⟩

/-- **Soundness.** A derivation `{Γ} t {Δ}` gives a `ToyLinearLogic` derivation of the sequent
    made of the hypotheses and conclusions it used. -/
theorem IO.sound {Γ Δ : REnv A} (d : IO Γ Δ) :
    Derivable (lefts (consumed Γ Δ)) (rights (consumed Γ Δ)) := by
  induction d with
  | ax s₁ s₂ =>
    refine derivable_transport (c' := [.L _, .R _])
      ((consumed_slot s₁ s₂.le).trans (by rw [s₂.consumed])) ?_
    exact ⟨CLL.ax _⟩
  | @cut Γ₀ Γ₁ Γ₂ a d₁ d₂ ih₁ ih₂ =>
    refine derivable_transport
      (consumed_trans (le_cons_cons.1 d₂.le).2 (le_cons_cons.1 d₁.le).2) ?_
    io_simp at ih₁ ih₂
    obtain ⟨e₁⟩ := ih₁.perm (Γ' := lefts (consumed Γ₀ Γ₁))
      (Ψ' := rights (consumed Γ₀ Γ₁) ++ [a]) (by perm_tac) (by perm_tac)
    obtain ⟨e₂⟩ := ih₂
    simpa using ⟨CLL.cut e₁ e₂⟩
  | @negL Γ₀ Γ₁ Γ₂ a s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih.perm (Γ' := lefts (consumed Γ₁ Γ₂))
      (Ψ' := rights (consumed Γ₁ Γ₂) ++ [a]) (by perm_tac) (by perm_tac)
    exact ⟨CLL.negL e⟩
  | @negR Γ₀ Γ₁ Γ₂ a s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih
    exact Derivable.perm ⟨CLL.negR e⟩ (by perm_tac) (by perm_tac)
  | @tensorL Γ₀ Γ₁ Γ₂ a b s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 (le_cons_cons.1 d.le).2).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih.perm (Γ' := lefts (consumed Γ₁ Γ₂) ++ [a, b])
      (Ψ' := rights (consumed Γ₁ Γ₂)) (by perm_tac) (by perm_tac)
    exact Derivable.perm ⟨CLL.tensorL e⟩ (by perm_tac) (by perm_tac)
  | @tensorR Γ₀ Γ₁ Γ₂ Γ₃ a b s d₁ d₂ ih₁ ih₂ =>
    refine derivable_transport
      (consumed_slot₂ s (le_cons_cons.1 d₁.le).2 (le_cons_cons.1 d₂.le).2) ?_
    io_simp at ih₁ ih₂ ⊢
    obtain ⟨e₁⟩ := ih₁
    obtain ⟨e₂⟩ := ih₂
    exact ⟨CLL.tensorR e₁ e₂⟩
  | @parL Γ₀ Γ₁ Γ₂ Γ₃ a b s d₁ d₂ ih₁ ih₂ =>
    refine derivable_transport
      (consumed_slot₂ s (le_cons_cons.1 d₁.le).2 (le_cons_cons.1 d₂.le).2) ?_
    io_simp at ih₁ ih₂ ⊢
    obtain ⟨e₁⟩ := ih₁.perm (Γ' := lefts (consumed Γ₁ Γ₂) ++ [a])
      (Ψ' := rights (consumed Γ₁ Γ₂)) (by perm_tac) (by perm_tac)
    obtain ⟨e₂⟩ := ih₂.perm (Γ' := lefts (consumed Γ₂ Γ₃) ++ [b])
      (Ψ' := rights (consumed Γ₂ Γ₃)) (by perm_tac) (by perm_tac)
    exact Derivable.perm ⟨CLL.parL e₁ e₂⟩ (by perm_tac) (by perm_tac)
  | @parR Γ₀ Γ₁ Γ₂ a b s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 (le_cons_cons.1 d.le).2).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih.perm (Γ' := lefts (consumed Γ₁ Γ₂))
      (Ψ' := a :: b :: rights (consumed Γ₁ Γ₂)) (by perm_tac) (by perm_tac)
    exact ⟨CLL.parR e⟩
  | @withL₁ Γ₀ Γ₁ Γ₂ a b s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih.perm (Γ' := lefts (consumed Γ₁ Γ₂) ++ [a])
      (Ψ' := rights (consumed Γ₁ Γ₂)) (by perm_tac) (by perm_tac)
    exact Derivable.perm ⟨CLL.withL₁ (b := b) e⟩ (by perm_tac) (by perm_tac)
  | @withL₂ Γ₀ Γ₁ Γ₂ a b s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih.perm (Γ' := lefts (consumed Γ₁ Γ₂) ++ [b])
      (Ψ' := rights (consumed Γ₁ Γ₂)) (by perm_tac) (by perm_tac)
    exact Derivable.perm ⟨CLL.withL₂ (a := a) e⟩ (by perm_tac) (by perm_tac)
  | @withR Γ₀ Γ₁ Γ₂ a b s d₁ d₂ ih₁ ih₂ =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d₁.le).2) ?_
    io_simp at ih₁ ih₂ ⊢
    obtain ⟨e₁⟩ := ih₁
    obtain ⟨e₂⟩ := ih₂
    exact ⟨CLL.withR e₁ e₂⟩
  | @plusL Γ₀ Γ₁ Γ₂ a b s d₁ d₂ ih₁ ih₂ =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d₁.le).2) ?_
    io_simp at ih₁ ih₂ ⊢
    obtain ⟨e₁⟩ := ih₁.perm (Γ' := lefts (consumed Γ₁ Γ₂) ++ [a])
      (Ψ' := rights (consumed Γ₁ Γ₂)) (by perm_tac) (by perm_tac)
    obtain ⟨e₂⟩ := ih₂.perm (Γ' := lefts (consumed Γ₁ Γ₂) ++ [b])
      (Ψ' := rights (consumed Γ₁ Γ₂)) (by perm_tac) (by perm_tac)
    exact Derivable.perm ⟨CLL.plusL e₁ e₂⟩ (by perm_tac) (by perm_tac)
  | @plusR₁ Γ₀ Γ₁ Γ₂ a b s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih
    exact ⟨CLL.plusR₁ e⟩
  | @plusR₂ Γ₀ Γ₁ Γ₂ a b s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih
    exact ⟨CLL.plusR₂ e⟩
  | @bangW Γ₀ Γ₁ Γ₂ a s d ih =>
    refine derivable_transport (consumed_slot s d.le) ?_
    simp only [lefts_cons_L, rights_cons_L]
    obtain ⟨e⟩ := ih
    exact Derivable.perm ⟨CLL.bangW (a := a) e⟩ (by perm_tac) (by perm_tac)
  | @bangC Γ₀ Γ₁ Γ₂ a s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 (le_cons_cons.1 d.le).2).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih.perm (Γ' := lefts (consumed Γ₁ Γ₂) ++ [.bang a, .bang a])
      (Ψ' := rights (consumed Γ₁ Γ₂)) (by perm_tac) (by perm_tac)
    exact Derivable.perm ⟨CLL.bangC e⟩ (by perm_tac) (by perm_tac)
  | @bangD Γ₀ Γ₁ Γ₂ a s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih.perm (Γ' := lefts (consumed Γ₁ Γ₂) ++ [a])
      (Ψ' := rights (consumed Γ₁ Γ₂)) (by perm_tac) (by perm_tac)
    exact Derivable.perm ⟨CLL.bangD e⟩ (by perm_tac) (by perm_tac)
  | @questW Γ₀ Γ₁ Γ₂ a s d ih =>
    refine derivable_transport (consumed_slot s d.le) ?_
    simp only [lefts_cons_R, rights_cons_R]
    obtain ⟨e⟩ := ih
    exact ⟨CLL.questW e⟩
  | @questC Γ₀ Γ₁ Γ₂ a s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 (le_cons_cons.1 d.le).2).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih
    exact ⟨CLL.questC e⟩
  | @questD Γ₀ Γ₁ Γ₂ a s d ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨e⟩ := ih
    exact ⟨CLL.questD e⟩
  | @bangR Γ₀ Γ₁ Γ₂ b s d hx ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨Γ, Ψ, h₁, h₂⟩ := exists_of_expOnly hx
    rw [h₁, h₂] at ih ⊢
    obtain ⟨e⟩ := ih
    exact ⟨CLL.bangR Γ Ψ e⟩
  | @questL Γ₀ Γ₁ Γ₂ b s d hx ih =>
    refine derivable_transport (consumed_slot s (le_cons_cons.1 d.le).2) ?_
    io_simp at ih ⊢
    obtain ⟨Γ, Ψ, h₁, h₂⟩ := exists_of_expOnly hx
    rw [h₁, h₂] at ih ⊢
    obtain ⟨e⟩ := ih.perm (Γ' := Γ.map .bang ++ [b]) (Ψ' := Ψ.map .quest) (by perm_tac)
      (by perm_tac)
    exact Derivable.perm ⟨CLL.questL Γ Ψ e⟩ (by perm_tac) (by perm_tac)

/-! ## Completeness -/

lemma premise₁ {E₁ E' : REnv A} {s : SFml A} {rest L : List (SFml A)} (h : Le E' E₁)
    (hc : (consumed E₁ E').Perm rest) (hp : (s :: rest).Perm L) :
    Le (none :: E') (some s :: E₁) ∧ (consumed (some s :: E₁) (none :: E')).Perm L :=
  ⟨le_cons_cons.2 ⟨Or.inl rfl, h⟩, by simpa using (hc.cons s).trans hp⟩

lemma premise₂ {E₁ E' : REnv A} {s t : SFml A} {rest L : List (SFml A)} (h : Le E' E₁)
    (hc : (consumed E₁ E').Perm rest) (hp : (t :: s :: rest).Perm L) :
    Le (none :: none :: E') (some t :: some s :: E₁) ∧
      (consumed (some t :: some s :: E₁) (none :: none :: E')).Perm L :=
  ⟨le_cons_cons.2 ⟨Or.inl rfl, le_cons_cons.2 ⟨Or.inl rfl, h⟩⟩,
    by simpa using ((hc.cons s).cons t).trans hp⟩

/-- **Completeness.** A `ToyLinearLogic` derivation of `Γ ⊢ Ψ` gives a derivation `{E} t {E'}`
    between any two environments `E' ⊑ E` such that what is used between them is `Γ ⊢ Ψ`, in
    any order. -/
theorem CLL.toIO {Γ Ψ : List (Fml A)} (d : CLL Γ Ψ) :
    ∀ E E' : REnv A, Le E' E → (consumed E E').Perm (Γ.map .L ++ Ψ.map .R) →
      Nonempty (IO E E') := by
  induction d with
  | ax a =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s₁⟩, h₁, hc₁⟩ := exists_slot (x := .L a) (rest := [.R a]) hle (by simpa using hc)
    obtain ⟨E₂, ⟨s₂⟩, h₂, hc₂⟩ := exists_slot (x := .R a) (rest := []) h₁ hc₁
    obtain rfl := eq_of_consumed_eq_nil h₂ hc₂.eq_nil
    exact ⟨.ax s₁ s₂⟩
  | @cut Γ Δ Λ Ψ a _ _ ih₁ ih₂ =>
    intro E E' hle hc
    obtain ⟨M, hM, hM', h₁, h₂⟩ := exists_split (xs := Γ.map .L ++ Λ.map .R)
      (ys := Δ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl₁, hc₁⟩ := premise₁ (s := .R a) hM h₁ (L := Γ.map .L ++ (Λ ++ [a]).map .R)
      (by perm_tac)
    obtain ⟨hl₂, hc₂⟩ := premise₁ (s := .L a) hM' h₂ (L := (a :: Δ).map .L ++ Ψ.map .R)
      (by perm_tac)
    obtain ⟨e₁⟩ := ih₁ _ _ hl₁ hc₁
    obtain ⟨e₂⟩ := ih₂ _ _ hl₂ hc₂
    exact ⟨.cut a e₁ e₂⟩
  | exchL _ ih | exchR _ ih =>
    intro E E' hle hc
    exact ih E E' hle (hc.trans (by perm_tac))
  | @negL Γ Λ a _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.neg a))
      (rest := Γ.map .L ++ Λ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .R a) h₁ hc₁ (L := Γ.map .L ++ (Λ ++ [a]).map .R)
      (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.negL s e⟩
  | @negR Γ Λ a _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.neg a))
      (rest := Γ.map .L ++ Λ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .L a) h₁ hc₁ (L := (a :: Γ).map .L ++ Λ.map .R)
      (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.negR s e⟩
  | @tensorL Γ Ψ a b _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.tensor a b))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₂ (s := .L a) (t := .L b) h₁ hc₁
      (L := (Γ ++ [a, b]).map .L ++ Ψ.map .R) (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.tensorL s e⟩
  | @tensorR Γ Δ Ψ Λ a b _ _ ih₁ ih₂ =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.tensor a b))
      (rest := (Γ.map .L ++ Ψ.map .R) ++ (Δ.map .L ++ Λ.map .R)) hle (hc.trans (by perm_tac))
    obtain ⟨M, hM, hM', hm₁, hm₂⟩ := exists_split h₁ hc₁
    obtain ⟨hl₁, hc₁'⟩ := premise₁ (s := .R a) hM hm₁ (L := Γ.map .L ++ (a :: Ψ).map .R)
      (by perm_tac)
    obtain ⟨hl₂, hc₂'⟩ := premise₁ (s := .R b) hM' hm₂ (L := Δ.map .L ++ (b :: Λ).map .R)
      (by perm_tac)
    obtain ⟨e₁⟩ := ih₁ _ _ hl₁ hc₁'
    obtain ⟨e₂⟩ := ih₂ _ _ hl₂ hc₂'
    exact ⟨.tensorR s e₁ e₂⟩
  | @parL Γ Δ Ψ Λ a b _ _ ih₁ ih₂ =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.par a b))
      (rest := (Γ.map .L ++ Ψ.map .R) ++ (Δ.map .L ++ Λ.map .R)) hle (hc.trans (by perm_tac))
    obtain ⟨M, hM, hM', hm₁, hm₂⟩ := exists_split h₁ hc₁
    obtain ⟨hl₁, hc₁'⟩ := premise₁ (s := .L a) hM hm₁ (L := (Γ ++ [a]).map .L ++ Ψ.map .R)
      (by perm_tac)
    obtain ⟨hl₂, hc₂'⟩ := premise₁ (s := .L b) hM' hm₂ (L := (Δ ++ [b]).map .L ++ Λ.map .R)
      (by perm_tac)
    obtain ⟨e₁⟩ := ih₁ _ _ hl₁ hc₁'
    obtain ⟨e₂⟩ := ih₂ _ _ hl₂ hc₂'
    exact ⟨.parL s e₁ e₂⟩
  | @parR Γ Ψ a b _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.par a b))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₂ (s := .R a) (t := .R b) h₁ hc₁
      (L := Γ.map .L ++ (a :: b :: Ψ).map .R) (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.parR s e⟩
  | @withL₁ Γ Ψ a b _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.amp a b))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .L a) h₁ hc₁ (L := (Γ ++ [a]).map .L ++ Ψ.map .R)
      (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.withL₁ s e⟩
  | @withL₂ Γ Ψ a b _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.amp a b))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .L b) h₁ hc₁ (L := (Γ ++ [b]).map .L ++ Ψ.map .R)
      (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.withL₂ s e⟩
  | @withR Γ Ψ a b _ _ ih₁ ih₂ =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.amp a b))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl₁, hc₁'⟩ := premise₁ (s := .R a) h₁ hc₁ (L := Γ.map .L ++ (a :: Ψ).map .R)
      (by perm_tac)
    obtain ⟨hl₂, hc₂'⟩ := premise₁ (s := .R b) h₁ hc₁ (L := Γ.map .L ++ (b :: Ψ).map .R)
      (by perm_tac)
    obtain ⟨e₁⟩ := ih₁ _ _ hl₁ hc₁'
    obtain ⟨e₂⟩ := ih₂ _ _ hl₂ hc₂'
    exact ⟨.withR s e₁ e₂⟩
  | @plusL Γ Ψ a b _ _ ih₁ ih₂ =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.plus a b))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl₁, hc₁'⟩ := premise₁ (s := .L a) h₁ hc₁ (L := (Γ ++ [a]).map .L ++ Ψ.map .R)
      (by perm_tac)
    obtain ⟨hl₂, hc₂'⟩ := premise₁ (s := .L b) h₁ hc₁ (L := (Γ ++ [b]).map .L ++ Ψ.map .R)
      (by perm_tac)
    obtain ⟨e₁⟩ := ih₁ _ _ hl₁ hc₁'
    obtain ⟨e₂⟩ := ih₂ _ _ hl₂ hc₂'
    exact ⟨.plusL s e₁ e₂⟩
  | @plusR₁ Γ Ψ a b _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.plus a b))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .R a) h₁ hc₁ (L := Γ.map .L ++ (a :: Ψ).map .R)
      (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.plusR₁ s e⟩
  | @plusR₂ Γ Ψ a b _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.plus a b))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .R b) h₁ hc₁ (L := Γ.map .L ++ (b :: Ψ).map .R)
      (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.plusR₂ s e⟩
  | @bangW Γ Ψ a _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.bang a))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨e⟩ := ih _ _ h₁ hc₁
    exact ⟨.bangW s e⟩
  | @bangC Γ Ψ a _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.bang a))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₂ (s := .L (.bang a)) (t := .L (.bang a)) h₁ hc₁
      (L := (Γ ++ [Fml.bang a, Fml.bang a]).map .L ++ Ψ.map .R) (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.bangC s e⟩
  | @bangD Γ Ψ a _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.bang a))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .L a) h₁ hc₁ (L := (Γ ++ [a]).map .L ++ Ψ.map .R)
      (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.bangD s e⟩
  | @questW Γ Ψ a _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.quest a))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨e⟩ := ih _ _ h₁ hc₁
    exact ⟨.questW s e⟩
  | @questC Γ Ψ a _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.quest a))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₂ (s := .R (.quest a)) (t := .R (.quest a)) h₁ hc₁
      (L := Γ.map .L ++ (.quest a :: .quest a :: Ψ).map .R) (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.questC s e⟩
  | @questD Γ Ψ a _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.quest a))
      (rest := Γ.map .L ++ Ψ.map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .R a) h₁ hc₁ (L := Γ.map .L ++ (a :: Ψ).map .R)
      (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    exact ⟨.questD s e⟩
  | @bangR Γ Ψ b _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .R (.bang b))
      (rest := (Γ.map Fml.bang).map .L ++ (Ψ.map Fml.quest).map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .R b) h₁ hc₁
      (L := (Γ.map Fml.bang).map .L ++ (b :: Ψ.map Fml.quest).map .R) (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    refine ⟨.bangR s e fun t ht => ?_⟩
    have := hc₁.subset ht
    simp only [List.map_map, List.mem_append, List.mem_map, Function.comp_apply] at this
    rcases this with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact trivial
  | @questL Γ Ψ b _ ih =>
    intro E E' hle hc
    obtain ⟨E₁, ⟨s⟩, h₁, hc₁⟩ := exists_slot (x := .L (.quest b))
      (rest := (Γ.map Fml.bang).map .L ++ (Ψ.map Fml.quest).map .R) hle (hc.trans (by perm_tac))
    obtain ⟨hl, hc'⟩ := premise₁ (s := .L b) h₁ hc₁
      (L := (Γ.map Fml.bang ++ [b]).map .L ++ (Ψ.map Fml.quest).map .R) (by perm_tac)
    obtain ⟨e⟩ := ih _ _ hl hc'
    refine ⟨.questL s e fun t ht => ?_⟩
    have := hc₁.subset ht
    simp only [List.map_map, List.mem_append, List.mem_map, Function.comp_apply] at this
    rcases this with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact trivial

/-- The environment holding the hypotheses `Γ` and the conclusions `Ψ`. -/
def initial (Γ Ψ : List (Fml A)) : REnv A := (Γ.map SFml.L ++ Ψ.map SFml.R).map some

/-- **The two calculi prove the same sequents**: `Γ ⊢ Ψ` is derivable iff there is a
    derivation using up all of its formulas. -/
theorem derivable_iff_io (Γ Ψ : List (Fml A)) :
    Derivable Γ Ψ ↔
      Nonempty (IO (initial Γ Ψ) (List.replicate (Γ.length + Ψ.length) none)) := by
  have hlen : Γ.length + Ψ.length = (Γ.map SFml.L ++ Ψ.map SFml.R).length := by simp
  have hc : consumed (initial Γ Ψ) (List.replicate (Γ.length + Ψ.length) none) =
      Γ.map .L ++ Ψ.map .R := by
    rw [hlen]
    simpa [initial] using consumed_replicate_none (Γ.map SFml.L ++ Ψ.map SFml.R)
  have hle : Le (List.replicate (Γ.length + Ψ.length) none) (initial Γ Ψ) := by
    rw [hlen]
    simpa [initial] using le_replicate_none (initial Γ Ψ)
  constructor
  · rintro ⟨d⟩
    exact CLL.toIO d _ _ hle (by rw [hc])
  · rintro ⟨t⟩
    simpa [hc] using t.sound

/-! ## An example -/

/-- `A ⊗ B ⊢ B ⊗ A`, with its two formulas used up.  No exchange is needed: each rule picks
    its formula by position. -/
def tensorCommIO (a b : Fml A) :
    IO (initial [.tensor a b] [.tensor b a]) (List.replicate 2 none) :=
  .tensorL (.here _ _)
    (.tensorR (.skip _ (.skip _ (.skip _ (.here _ _))))
      (.ax (.skip _ (.here _ _)) (.here _ _))
      (.ax (.skip _ (.skip _ (.here _ _))) (.here _ _)))

/-! ## The paper's judgement carries over -/

variable {C : Type} {τ : C → Ty A}

/-- The hypotheses of a typing environment of the paper. -/
def hyps (Γ : FEnv A) : REnv A := Γ.map (Option.map fun α => .L α.toFml)

/-- The `!`-hypotheses `!Θ` as slots. -/
def bangHyps (Θ : List (Fml A)) : REnv A := Θ.map fun a => some (.L (.bang a))

/-- **Typed A-normal statements give Hodas–Miller derivations.** A statement
    `{Γ} s : α {Δ}` of `Toy/Anf.lean` gives `{Γ, !Θ} t : ⟦α⟧ {Δ, ⊥…⊥}`, with the same
    environments read as hypotheses, when the constants' types follow from `!Θ`. -/
theorem _root_.LinearDB.Toy.Stmt.toIO {Θ : List (Fml A)}
    (κ : ∀ c, Derivable (bangs Θ) [(τ c).toFml]) {Γ Δ : FEnv A} {α : Ty A}
    (s : Stmt τ Γ α Δ) :
    Nonempty (Proves (hyps Γ ++ bangHyps Θ) α.toFml
      (hyps Δ ++ List.replicate Θ.length none)) := by
  obtain ⟨d⟩ := Stmt.toCLL κ s
  have hΔΓ := le_map (fun α => SFml.L α.toFml) (le_of_llTyped s.sound)
  have hcB : consumed (bangHyps Θ) (List.replicate Θ.length none) =
      Θ.map fun a => SFml.L (.bang a) := by
    have hB : bangHyps Θ = (Θ.map fun a => SFml.L (.bang a)).map some := by
      simp [bangHyps, Function.comp_def]
    have hlen : Θ.length = (Θ.map fun a => SFml.L (.bang a)).length := by simp
    rw [hB, hlen, consumed_replicate_none]
  refine CLL.toIO d _ _ (le_cons_cons.2 ⟨Or.inl rfl, le_append hΔΓ ?_⟩) ?_
  · simpa [bangHyps] using le_replicate_none (bangHyps Θ)
  · rw [consumed_cons_cons, consumed_append (Γ := hyps Γ) (Δ := hyps Δ) hΔΓ.length_eq.symm, hcB]
    simp only [hyps, step_some_none, consumed_map, used, bangs, List.map_map,
      Function.comp_def, List.singleton_append, List.map_append]
    perm_tac

end ToyLinearLogic2

end LinearDB
