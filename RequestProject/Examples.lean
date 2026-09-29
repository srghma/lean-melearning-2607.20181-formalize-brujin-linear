module

public import RequestProject.SubjectReduction

/-!
# Examples from the paper
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

/-- Judgement (ex2dbn) of the paper:
`{} λλλ(1 (2 0)) : (a → b) → ((b → c) → (a → c)) {}` in the system of Figure 4. -/
example (a b c : Ty ℕ) (τ : Empty → Ty ℕ) :
    LLTyped τ [] (lam (lam (lam (app (var 1) (app (var 2) (var 0))))))
      (.arr (.arr a b) (.arr (.arr b c) (.arr a c))) [] :=
  .abs <| .abs <| .abs <|
    .app (Δ := [some a, none, some (.arr a b)])
      (.weak₁ a (.var _ _))
      (.app (Δ := [some a, none, none])
        (.weak₁ a (.weak₂ (.var _ _)))
        (.var _ _))

/-- The body of (ex2dbn) in the system of Figure 3, as in rule (exappf) of the paper. -/
example (a b c : Ty ℕ) (τ : Empty → Ty ℕ) :
    FLLTyped τ [some a, some (.arr b c), some (.arr a b)]
      (app (var 1) (app (var 2) (var 0))) c :=
  .app (Γ := [none, some (.arr b c), none]) (Δ := [some a, none, some (.arr a b)])
    (.weak (.var 1 _))
    (.app (Γ := [none, none, some (.arr a b)]) (Δ := [some a, none, none])
      (.weak (.weak (.var 0 _))) (.var 2 _) rfl)
    rfl

end LinearDB
