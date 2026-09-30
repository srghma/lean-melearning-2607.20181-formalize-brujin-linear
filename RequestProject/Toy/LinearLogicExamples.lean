module

public import RequestProject.Toy.LinearLogic2
public import RequestProject.Toy.Examples

@[expose] public section

set_option autoImplicit false

/-!
# Examples for `ToyLinearLogic` and `ToyLinearLogic2`

The A-normal program `lenSuccA` of `Toy/Examples.lean`,
`λs. let n := length s; let f := add n; let r := f 1; r : string ⊸ nat`,
read as a proof in both linear-logic calculi.  The constants of `Toy/Examples.lean` are
infinitely many (one per literal) but have only six types; these six formulas, as
`!`-hypotheses, are the reusable hypotheses `!Θ` from which every constant follows.
-/

namespace LinearDB

namespace Toy

open ToyLinearLogic ToyLinearLogic2

/-- The types of the constants of `Toy/Examples.lean`, as formulas. -/
def constFmls : List (Fml Base) :=
  [LTy.nat.toFml, LTy.bool.toFml, LTy.string.toFml, (LTy.fn .nat (.fn .nat .nat)).toFml,
    (LTy.fn .bool .bool).toFml, (LTy.fn .string .nat).toFml]

/-- Every constant follows from `!Θ`, by dereliction. -/
theorem const_derivable (c : Const) : Derivable (bangs constFmls) [c.ty.toFml] :=
  derivable_bangs_of_mem (by cases c <;> simp [constFmls, Const.ty])

/-- `lenSuccA` as a proof of `!Θ ⊢ string ⊸ nat` in `ToyLinearLogic`. -/
theorem lenSuccA_toCLL :
    Derivable (bangs constFmls) [(LTy.fn LTy.string LTy.nat).toFml] :=
  lenSuccA.toCLL const_derivable

/-- `lenSuccA` as a Hodas–Miller derivation `{!Θ} t : string ⊸ nat {⊥…⊥}` in
    `ToyLinearLogic2`. -/
theorem lenSuccA_toIO :
    Nonempty (Proves (bangHyps constFmls) (LTy.fn LTy.string LTy.nat).toFml
      (List.replicate constFmls.length none)) := by
  simpa [hyps] using Stmt.toIO const_derivable lenSuccA

end Toy

end LinearDB
