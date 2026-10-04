module

public import RequestProject.Sec2SimplyTyped.Syntax

/-!
# β-reduction with de Bruijn indices (Section 5 of the paper)

* lifting `↑ᵏᵢ(t)` (`Term.lift`);
* substitution `t[i := u]` (`Term.subst`);
* β-contraction `Term.Beta` and β-reduction `Term.BetaRed`.
-/

@[expose] public section

namespace LinearDB

namespace Term

variable {C : Type*}

/-- Lifting `↑ᵏᵢ(t)`: add `k` to every index of `t` that is `≥ i` (where `i` counts the
enclosing λ's). Written `lift t k i`. -/
def lift : Term C → ℕ → ℕ → Term C
  | const c, _, _ => const c
  | var j, k, i => if j < i then var j else var (j + k)
  | app t₁ t₂, k, i => app (lift t₁ k i) (lift t₂ k i)
  | lam t₁, k, i => lam (lift t₁ k (i + 1))

/-- Substitution `t[i := u]` of the index `i` by the term `u` in `t`. Written `subst t i u`. -/
def subst : Term C → ℕ → Term C → Term C
  | const c, _, _ => const c
  | var j, i, u => if j < i then var j else if j = i then lift u i 0 else var (j - 1)
  | app t₁ t₂, i, u => app (subst t₁ i u) (subst t₂ i u)
  | lam t₁, i, u => lam (subst t₁ (i + 1) u)

/-- β-contraction `t →β u` (Definition of β-contraction). -/
inductive Beta : Term C → Term C → Prop
  | beta (t u : Term C) : Beta (app (lam t) u) (subst t 0 u)
  | appL {t u : Term C} (v : Term C) : Beta t u → Beta (app t v) (app u v)
  | appR {t u : Term C} (v : Term C) : Beta t u → Beta (app v t) (app v u)
  | lam {t u : Term C} : Beta t u → Beta (lam t) (lam u)

/-- β-reduction: the reflexive, transitive closure of β-contraction. -/
def BetaRed : Term C → Term C → Prop := Relation.ReflTransGen Beta

end Term

end LinearDB
