module

public import RequestProject.Sec3FragmentaryEnv.Typing

/-!
# Examples from Section 3 of the paper
-/

@[expose] public section

namespace LinearDB

open Term

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
