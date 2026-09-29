module

public import RequestProject.Toy.Anf

@[expose] public section

set_option autoImplicit false

/-!
# Toy programs

A tiny signature of constants over the leaves `nat`, `bool`, `string`, and some programs
written in the toy grammar.  The last theorem shows that the non-linear `λx. add x x` cannot
be written.
-/

namespace LinearDB

namespace Toy

open Term

/-- The constants of the toy language. -/
inductive Const : Type where
  /-- A natural-number literal. -/
  | natLit (n : ℕ)
  /-- A Boolean literal. -/
  | boolLit (b : Bool)
  /-- A string literal. -/
  | strLit (s : String)
  /-- Addition. -/
  | add
  /-- Negation. -/
  | not
  /-- The length of a string. -/
  | length
  deriving DecidableEq, Repr

/-- The type of each constant. -/
def Const.ty : Const → LTy
  | .natLit _ => .nat
  | .boolLit _ => .bool
  | .strLit _ => .string
  | .add => .fn .nat (.fn .nat .nat)
  | .not => .fn .bool .bool
  | .length => .fn .string .nat

/-- The value of each constant. -/
def Const.den : (c : Const) → LTy.den c.ty
  | .natLit n => n
  | .boolLit b => b
  | .strLit s => s
  | .add => fun (m n : ℕ) => m + n
  | .not => fun (b : Bool) => !b
  | .length => fun (s : String) => s.length

/-- Programs of the toy language. -/
abbrev ToyProgram (α : LTy) : Type := Program Const.ty α

/-- `λx. x : nat ⊸ nat`. -/
def idNat : ToyProgram (.fn .nat .nat) := .lam (.neu (.var (.here _ _)))

/-- `λx. add x 1 : nat ⊸ nat`. -/
def succ : ToyProgram (.fn .nat .nat) :=
  .lam (.neu (.app (.app (.const Const.add) (.neu (.var (.here _ _))))
    (.neu (.const (Const.natLit 1)))))

/-- `λs. add (length s) 1 : string ⊸ nat`. -/
def lenSucc : ToyProgram (.fn .string .nat) :=
  .lam (.neu (.app (.app (.const Const.add)
    (.neu (.app (.const Const.length) (.neu (.var (.here _ _))))))
    (.neu (.const (Const.natLit 1)))))

/-- The paper's example (ex2dbn), `λλλ(1 (2 0)) : (a ⊸ b) ⊸ (b ⊸ c) ⊸ (a ⊸ c)`, at
    `a = string`, `b = nat`, `c = bool`. -/
def compose : ToyProgram (.fn (.fn .string .nat) (.fn (.fn .nat .bool) (.fn .string .bool))) :=
  .lam <| .lam <| .lam <| .neu <|
    .app (Δ := [some LTy.string, none, some (LTy.fn .string .nat)])
      (.var (.there₁ _ (.here _ _)))
      (.neu (.app (Δ := [some LTy.string, none, none])
        (.var (.there₁ _ (.there₂ (.here _ _))))
        (.neu (.var (.here _ _)))))

example : compose.erase = lam (lam (lam (app (var 1) (app (var 2) (var 0))))) := rfl

example : succ.erase = lam (app (app (const .add) (var 0)) (const (.natLit 1))) := rfl

/-- The non-linear `λx. add x x` is not a program of the toy grammar: it uses `x` twice. -/
theorem no_add_self_self :
    ¬ ∃ p : ToyProgram (.fn .nat .nat), p.erase = lam (app (app (const .add) (var 0)) (var 0)) := by
  rintro ⟨p, hp⟩
  have h := (Program.linear p).1.1.1
  rw [hp] at h
  have := h _ (IsSubterm.refl _)
  simp [occ] at this

/-- The discarding `λx. 1` is not a program of the toy grammar: it does not use `x`. -/
theorem no_const_fun :
    ¬ ∃ p : ToyProgram (.fn .nat .nat), p.erase = lam (const (.natLit 1)) := by
  rintro ⟨p, hp⟩
  have h := (Program.linear p).1.1.1
  rw [hp] at h
  have := h _ (IsSubterm.refl _)
  simp [occ] at this

/-! ## A-normal programs -/

/-- `λs. let n := length s; let f := add n; let r := f 1; r : string ⊸ nat`, in the
    A-normal grammar. -/
def lenSuccA : AProgram Const.ty (LTy.fn LTy.string LTy.nat) :=
  .ret <| .lam <|
    .letE (.app (.const Const.length) (.head (.var (.here _ _)))) <|
    .letE (.app (.const Const.add) (.head (.var (.here _ _)))) <|
    .letE (.app (.var (.here _ _)) (.head (.const (Const.natLit 1)))) <|
    .ret (.head (.var (.here _ _)))

example : lenSuccA.erase =
    lam (app (lam (app (lam (app (lam (var 0)) (app (var 0) (const (.natLit 1)))))
      (app (const .add) (var 0)))) (app (const .length) (var 0))) := rfl

/-- `λx. let y := add x; y x` is not an A-normal program: it uses `x` twice. -/
theorem no_anf_add_self_self :
    ¬ ∃ p : AProgram Const.ty (LTy.fn LTy.nat LTy.nat),
      p.erase = lam (app (lam (app (var 0) (var 1))) (app (const .add) (var 0))) := by
  rintro ⟨p, hp⟩
  have h := (AProgram.linear p).1.1.1
  rw [hp] at h
  have := h _ (IsSubterm.refl _)
  simp [occ] at this

end Toy

end LinearDB

end
