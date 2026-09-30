about Syntax.lean

1. split

```lean
/-- Condition (i): Every λ-abstraction uses its bound variable exactly once. -/
def BindersLinear (t : Term C) : Prop :=
  ∀ u, IsSubterm (lam u) t → occ 0 u = 1

/-- Condition (ii): Every free variable appears at most once (no duplication). -/
def FreeLinear (t : Term C) : Prop :=
  ∀ i ∈ fv t, occ i t = 1

/-- A term is QuasiLinear if both bound variables and free variables are linear. -/
def QuasiLinear (t : Term C) : Prop :=
  BindersLinear t ∧ FreeLinear t
```

2. BindersLinear2 is same as BindersLinear, but without occ

```lean
/-- Inductive judgment: index `i` does not occur freely in `t`. -/
inductive Fresh : ℕ → Term C → Prop where
  | const (i : ℕ) (c : C) : Fresh i (const c)
  | var {i j : ℕ} (h : i ≠ j) : Fresh i (var j)
  | app {i : ℕ} {t₁ t₂ : Term C} : Fresh i t₁ → Fresh i t₂ → Fresh i (app t₁ t₂)
  | lam {i : ℕ} {t : Term C} : Fresh (i + 1) t → Fresh i (lam t)

/-- Inductive judgment: index `i` occurs freely exactly once in `t`.
    In an application, it must go to either the left or right, but never both. -/
inductive OccursOnce : ℕ → Term C → Prop where
  | var (i : ℕ) : OccursOnce i (var i)
  | appL {i : ℕ} {t₁ t₂ : Term C} :
      OccursOnce i t₁ → Fresh i t₂ → OccursOnce i (app t₁ t₂)
  | appR {i : ℕ} {t₁ t₂ : Term C} :
      Fresh i t₁ → OccursOnce i t₂ → OccursOnce i (app t₁ t₂)
  | lam {i : ℕ} {t : Term C} :
      OccursOnce (i + 1) t → OccursOnce i (lam t)

/-- Purely inductive BindersLinear: no arithmetic `occ` used! -/
inductive BindersLinear2 : Term C → Prop where
  | const (c : C) : BindersLinear2 (const c)
  | var (j : ℕ) : BindersLinear2 (var j)
  | app {t₁ t₂ : Term C} :
      BindersLinear2 t₁ → BindersLinear2 t₂ → BindersLinear2 (app t₁ t₂)
  | lam {u : Term C} :
      OccursOnce 0 u → BindersLinear2 u → BindersLinear2 (lam u)
```

3. FreeLinear2 is same as FreeLinear

```lean
/-- Inductive judgment: index `i` occurs at most once (either 0 or 1 time).
    Uses only inductive propositions, no arithmetic `occ`. -/
inductive OccursAtMostOnce (i : ℕ) (t : Term C) : Prop where
  | fresh : Fresh i t → OccursAtMostOnce i t
  | once  : OccursOnce i t → OccursAtMostOnce i t

/-- Purely inductive formulation of FreeLinear:
    every index appears at most once as a free variable. -/
def FreeLinear2 (t : Term C) : Prop :=
  ∀ i, OccursAtMostOnce i t
```

4.

```lean
def QuasiLinear2 (t : Term C) : Prop :=
  BindersLinear2 t ∧ FreeLinear2 t

-- OR

/-- One-pass inductive judgment:
    - Every binder uses its bound variable once.
    - Free variables are never duplicated (enforced by disjoint unions).
    - `s` is the synthesized set of free variables. -/
inductive HasLinFv : Term C → Set ℕ → Prop where
  | const (c : C) :
      HasLinFv (const c) ∅ -- (fun _ => False)

  | var (j : ℕ) :
      HasLinFv (var j) {j} -- (fun x => x = j)

  | app {t₁ t₂ : Term C} {s₁ s₂ : Set ℕ} :
      HasLinFv t₁ s₁ →
      HasLinFv t₂ s₂ →
      Disjoint s₁ s₂ → -- (∀ i, s₁ i → s₂ i → False) →
      HasLinFv (app t₁ t₂) (s₁ ∪ s₂) -- (fun x => s₁ x ∨ s₂ x)

  | lam {u : Term C} {s : Set ℕ} :
      HasLinFv u s →
      0 ∈ s → -- s 0 →
      HasLinFv (lam u) {i | i + 1 ∈ s} -- (fun i => s (i + 1))

/-- A term is QuasiLinear if it admits a valid derivation in one pass. -/
def QuasiLinear2 (t : Term C) : Prop :=
  ∃ s, HasLinFv t s
```


5.

```lean
def Linear (t : Term C) : Prop :=
  QuasiLinear t ∧ ∀ i j : ℕ, i ∈ fv t → j < i → j ∈ fv t

-- same as

/-- A set of indices has no gaps: if `i` is in the set, all smaller indices are too. -/
def GapFree (s : Set ℕ) : Prop :=
  ∀ ⦃i j : ℕ⦄, i ∈ s → j < i → j ∈ s
  -- same as `∃ n : ℕ, s = {i | i < n}` , but that one is constructive, thus harder

/-- A term is linear if it is quasi-linear and its free variables have no gaps. -/
def Linear (t : Term C) : Prop :=
  QuasiLinear t ∧ GapFree (fv t)

-- same as

/-- A term is Linear if a single tree pass synthesizes its free variables
    as exactly the gap-free initial segment {0, ..., n - 1}. -/
def Linear (t : Term C) : Prop :=
  ∃ n : ℕ, HasLinFv t (fun i => i < n)
```

6.

how to implement Term that is Linear by construction
without using anything
Term should become Term C Nat
and var should take Fin n
therefore Term C 0 means there is no free variables/term is closed
while not 0 will mean that Term is possibly has free variables

```lean
-- this is wrong
inductive Term (C : Type*) : ℕ → Type* where
  | const : C → Term C 0
  | var   : Fin 1 → Term C 1
  | app   {n₁ n₂ n : ℕ} : (h_split : n₁ + n₂ = n) → Term C n₁ → Term C n₂ → Term C n
  | lam   {n : ℕ} : Term C (n + 1) → Term C n
  deriving DecidableEq
```

```lean
-- correct
inductive LinTerm (C : Type*) : ℕ → Type* where
  /-- A constant `c`. It has no free variables, so its context is size 0. -/
  | const : C → LinTerm C 0

  /-- The variable `var 0`. Its context has size 1, containing just itself. -/
  | var : LinTerm C 1

  /-- Application `(t u)`. If `t` uses `m` variables `{0..m-1}` and `u`
  uses `k` variables `{0..k-1}`, the application uses `m+k` variables.
  The variables for `u` are implicitly lifted to avoid collision.
  This constructor enforces that free variables are not shared (disjoint). -/
  | app : LinTerm C m → LinTerm C k → LinTerm C (m + k)

  /-- Lambda abstraction `(λ t)`. It takes a term `t` that uses `n+1`
  variables `{0..n}` and binds index `0`. The remaining variables `{1..n}`
  are re-indexed to `{0..n-1}`, resulting in a term with `n` free variables.
  This constructor enforces that every binder uses its variable. -/
  | lam : LinTerm C (n + 1) → LinTerm C n

  /-- `permute p t`: relabels the free variables of `t` according to a
  permutation `p`. This is essential for constructing terms where variables
  are not used in a simple contiguous block. -/
  | permute : Equiv.Perm (Fin n) → LinTerm C n → LinTerm C n


-- why `permute` is needed?

bc usually `app var (app var var)` eq to `x0 (x1 x2)`
bc usually `app (app var var) var)` eq to `(x0 x1) x2`
but `perm (finRotate 3) (app var (app var var))` eq to `(x1 x2) x0`
```

| Expression in Lean 4 | Mathematical Power | Mapping $(0, 1, 2)$ | Resulting $\lambda$-Term |
| :--- | :---: | :---: | :---: |
| `1` (Identity) | $R^0$ | $(0, 1, 2)$ | $\mathbf{x_0\ (x_1\ x_2)}$ |
| `finRotate 3` | $R^1$ | $(1, 2, 0)$ | $\mathbf{x_1\ (x_2\ x_0)}$ |
| `(finRotate 3) ^ 2` or `(finRotate 3)⁻¹` | $R^2 = R^{-1}$ | $(2, 0, 1)$ | $\mathbf{x_2\ (x_0\ x_1)}$ |
| `(finRotate 3) ^ 3` | $R^3 = 1$ | $(0, 1, 2)$ | $\mathbf{x_0\ (x_1\ x_2)}$ *(back to start)* |

| # | Permutation in Lean 4 | Cycle Notation | Mapping $(0, 1, 2) \mapsto$ | Resulting $\lambda$-Term |
| :-: | :--- | :---: | :---: | :---: |
| **1** | `1` *(or `Equiv.refl _`)* | $()$ *(id)* | $(0, 1, 2)$ | $\mathbf{x_0\ (x_1\ x_2)}$ |
| **2** | `finRotate 3` | $(0\;1\;2)$ | $(1, 2, 0)$ | $\mathbf{x_1\ (x_2\ x_0)}$ |
| **3** | `(finRotate 3) ^ 2` *(or `(finRotate 3)⁻¹`)* | $(0\;2\;1)$ | $(2, 0, 1)$ | $\mathbf{x_2\ (x_0\ x_1)}$ |
| **4** | `Equiv.swap 0 1` | $(0\;1)$ | $(1, 0, 2)$ | $\mathbf{x_1\ (x_0\ x_2)}$ |
| **5** | `Equiv.swap 1 2` | $(1\;2)$ | $(0, 2, 1)$ | $\mathbf{x_0\ (x_2\ x_1)}$ |
| **6** | `Equiv.swap 0 2` *(or `Fin.revPerm`)* | $(0\;2)$ | $(2, 1, 0)$ | $\mathbf{x_2\ (x_1\ x_0)}$ |

Example:

```
--- lets describe both `lam lam lam 1 (2 0)` (3 bound variables) and `1 (2 0)` (3 free variables)
import Mathlib

open LinTerm

-- 1. The body `1 (2 0)` with 3 free variables
def term_body : LinTerm C 3 :=
  permute (finRotate 3) (app var (app var var))

-- 2. The full closed term `λ λ λ (1 (2 0))` with 3 bound variables
def term_closed : LinTerm C 0 :=
  lam (lam (lam term_body))
```

6. BONUS LinAnfTerm

```lean
-- Linear A-Normal Form (Linear ANF):
mutual
  -- 1. Atomic values: variables or constants
  inductive LinAtom (C : Type*) : ℕ → Type* where
    | const : C → LinAtom C 0
    | var   : LinAtom C 1

  -- 2. Expressions: only atomic applications, sequenced by linear `let`
  inductive LinExpr (C : Type*) : ℕ → Type* where
    -- Return an atom
    | ret : LinAtom C n → LinExpr C n

    -- Abstraction: produces an atomic function
    | lam : LinExpr C (n + 1) → LinAtom C n

    -- In ANF, applications ONLY take atoms!
    -- `let x = v1 v2 in body`
    | letApp {m k n : ℕ} :
        LinAtom C m → LinAtom C k → LinExpr C (n + 1) → LinExpr C (m + k + n)
end
```
