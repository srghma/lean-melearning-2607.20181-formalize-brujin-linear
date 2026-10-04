module

public import RequestProject.Sec2SimplyTyped.Syntax

/-!
# Examples from Section 2 of the paper
-/

@[expose] public section

namespace LinearDB

open Term

/-- `(λ (1 0))` is a linear λ-term (judgement (tjdb1) of the paper). -/
example : Linear (lam (app (var 1) (var 0)) : Term Empty) := by
  refine ⟨⟨fun u hu => ?_, fun i hi => ?_⟩, fun i j hi hj => ?_⟩
  · cases hu with
    | refl => simp [occ]
    | lam hu =>
      cases hu with
      | appL _ hu => cases hu
      | appR _ hu => cases hu
  · simp only [fv, Set.mem_setOf_eq, occ] at hi ⊢
    rcases i with _ | i <;> simp_all
  · simp only [fv, Set.mem_setOf_eq, occ] at hi ⊢
    rcases i with _ | i <;> simp_all

/-- `(λ (2 0))` is not a linear λ-term: it violates condition (iii) (judgement (tjdb2)). -/
example : ¬ Linear (lam (app (var 2) (var 0)) : Term Empty) := by
  rintro ⟨-, h⟩
  have := h 1 0 (by simp [fv, occ]) (by omega)
  simp [fv, occ] at this

end LinearDB
