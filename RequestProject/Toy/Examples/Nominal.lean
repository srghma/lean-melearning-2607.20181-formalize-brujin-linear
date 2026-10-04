module

public import RequestProject.Toy.Terms.NominalTerm

@[expose] public section

set_option autoImplicit false

/-!
# Toy programs over one declared datatype

One declared datatype, `data 0`, the lists of naturals; its constructors are constants.
-/

namespace LinearDB

namespace Toy

namespace NominalExamples

open Term

/-- The constants: `zero`, `succ`, and the constructors of the declared list type. -/
inductive LCon : Type where
  | zero | succ | nil | cons
  deriving DecidableEq, Repr

/-- The declared list type, by its de Bruijn name. -/
abbrev natList : NTy 1 := .data 0

/-- The types of the constants. -/
def LCon.ty : LCon → NTy 1
  | .zero => .nat
  | .succ => .fn .nat .nat
  | .nil => natList
  | .cons => .fn .nat (.fn natList natList)

/-- `λx. λxs. delay (cons x xs)`: build a list, lazily. -/
def consLazy : NProgram LCon.ty (.fn .nat (.fn natList (.lazy (.data 0)))) :=
  .lam (.lam (.delay (.neu (.app (.app (.const LCon.cons)
    (.neu (.var (.there₁ _ (.here _ _))))) (.neu (.var (.here _ _)))))))

example : consLazy.erase = .lam (.lam (.app (.app (.const LCon.cons) (.var 1)) (.var 0))) := rfl

/-- `λt. cons zero (force t)`: the delay is an unknown, so its force is stuck and kept. -/
def forceCons : NProgram LCon.ty (.fn (.lazy (.data 0)) natList) :=
  .lam (.neu (.app (.app (.const LCon.cons) (.neu (.const LCon.zero)))
    (.neu (.force (α := .data 0) (.var (.here _ _))))))

example : forceCons.erase = .lam (.app (.app (.const LCon.cons) (.const LCon.zero)) (.var 0)) := rfl

/-- Both programs are linear λ-terms. -/
example : Linear consLazy.erase ∧ Linear forceCons.erase :=
  ⟨(NProgram.linear consLazy).1, (NProgram.linear forceCons).1⟩

/-- `Unit → Unit → natList` is read as `Unit → natList`. -/
example : NTy.mkLazy (NTy.mkLazy natList) = .lazy (.data 0) := rfl

/-- Declaring a new datatype renames the list type to `data 1`. -/
example : (natList.weaken : NTy 2) = .data 1 := rfl

end NominalExamples

end Toy

end LinearDB

end
