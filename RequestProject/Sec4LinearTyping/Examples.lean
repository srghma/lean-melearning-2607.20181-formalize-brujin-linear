module

public import RequestProject.Sec4LinearTyping.Typing

/-!
# Examples from Section 4 of the paper
-/

@[expose] public section

namespace LinearDB

open Term

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

end LinearDB
