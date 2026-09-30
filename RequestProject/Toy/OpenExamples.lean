module

public import RequestProject.Toy.Examples
public import RequestProject.Toy.Open

@[expose] public section

set_option autoImplicit false

/-!
# Toy programs in the known/unknown grammar

Programs of `LinearDB.Toy.Open` over the constants of `LinearDB.Toy.Const`, and the redex
`add 1 2`, which cannot be written as a program.
-/

namespace LinearDB

namespace Toy

namespace Open

open Term

/-- `λx. add x 1`: the call is stuck on the unknown `x`, the λ uses nothing else (closed). -/
def succO : OProgram Const.ty (LTy.fn LTy.nat LTy.nat) :=
  ⟨false, .lamC (.neu (.extern Const.add
    (.cons (.neu (.var (.here _ _))) (.cons (.lit (Const.natLit 1) rfl) .nil)) rfl))⟩

example : succO.2.erase = .lam (.app (.app (.const Const.add) (.var 0)) (.const (.natLit 1))) :=
  rfl

/-- `λf. λx. f x`: the inner λ uses the outer unknown `f`, so it is open (`lamO`); the outer λ
    uses only its own parameter, so it is closed (`lamC`). -/
def applyO : OProgram Const.ty (LTy.fn (LTy.fn LTy.nat LTy.nat) (LTy.fn LTy.nat LTy.nat)) :=
  ⟨false, .lamC (.lamO (.neu (.app (.var (.there₁ _ (.here _ _))) (.neu (.var (.here _ _)))))
    (by simp))⟩

example : applyO.2.erase = .lam (.lam (.app (.var 1) (.var 0))) := rfl

/-- The redex `add 1 2`, between known values only, is not a program: the normaliser would
    have computed it. -/
theorem no_add_one_two (p : OProgram Const.ty LTy.nat) :
    p.2.erase ≠ .app (.app (.const Const.add) (.const (.natLit 1))) (.const (.natLit 2)) := by
  intro h
  rcases (OProgram.closed p).2 with ⟨c, hc⟩ | ⟨s, hs⟩
  · rw [hc] at h; cases h
  · rw [hs] at h; cases h

end Open

end Toy

end LinearDB

end
