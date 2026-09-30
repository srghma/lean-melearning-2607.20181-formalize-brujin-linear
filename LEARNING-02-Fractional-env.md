add is smallest partial operation

```lean
import Mathlib.Data.PFun

namespace LinearDB
namespace QTy

variable {A : Type*}

/-- Addition of quasi-types as a partial function `PFun`.
    We convert the existing `Option`-based `add` into Mathlib's `Part`. -/
def addPFun : PFun (QTy A × QTy A) (QTy A) :=
  fun ⟨a, b⟩ => Part.ofOption (add a b)

/-- A candidate partial operation `g : PFun (QTy A × QTy A) (QTy A)`
    satisfies the two equations: `⊥ + ω = ω` and `ω + ⊥ = ω`. -/
def SatisfiesAddEquations (g : PFun (QTy A × QTy A) (QTy A)) : Prop :=
  (∀ w : QTy A, g (none, w) = Part.some w) ∧
  (∀ w : QTy A, g (w, none) = Part.some w)

/-- "add is the smallest partial operation" literally formalized in Mathlib:
    `addPFun` is the LEAST element among all partial functions satisfying
    the equations, under the partial order of partial functions (`PFun.le`). -/
theorem addPFun_is_least :
    IsLeast { g : PFun (QTy A × QTy A) (QTy A) | SatisfiesAddEquations g } addPFun := by
  refine ⟨?_, ?_⟩
  · -- Part 1: `addPFun` satisfies the equations
    constructor
    · intro w
      dsimp [addPFun, add]
      rfl
    · intro w
      dsimp [addPFun, add]
      cases w <;> rfl

  · -- Part 2: `addPFun ≤ g` for any candidate `g` satisfying the equations
    intro g hg
    obtain ⟨h_left, h_right⟩ := hg
    -- `PFun.le` is pointwise: check `addPFun ⟨a, b⟩ ≤ g ⟨a, b⟩`
    intro ⟨a, b⟩
    cases a with
    | none =>
      -- Case 1: (⊥, b). By left equation, both equal `Part.some b`.
      have h : addPFun (none, b) = g (none, b) := by
        dsimp [addPFun, add]
        rw [h_left]
      rw [h]
    | some ta =>
      cases b with
      | none =>
        -- Case 2: (a, ⊥). By right equation, both equal `Part.some (some ta)`.
        have h : addPFun (some ta, none) = g (some ta, none) := by
          dsimp [addPFun, add]
          rw [h_right]
        rw [h]
      | some tb =>
        -- Case 3: (some ta, some tb). `addPFun` is undefined (`Part.none` / `⊥`).
        -- In order theory, `⊥ ≤ x` is always true!
        dsimp [addPFun, add]
        exact bot_le

end QTy
end LinearDB
```

<details>
<summary>These are not "is smallest"</summary>

Any function in that set must agree with `addPFun` whenever at least one argument is $\bot$. But on inputs of the form **$(\text{some } \tau_1, \text{some } \tau_2)$**, it is free to do **whatever it wants**!

Here are concrete examples of other valid $g$'s, categorized by how they behave when both arguments are actual types:

---

### Category 1: Total Operations (Maximal Elements)

These operations are defined on **$100\%$ of all inputs**. They make an arbitrary choice for what happens when two types collide:

#### 1. Left-Biased Addition (`addLeft`)
*"If both variables exist, pick the first one and drop the second."*
$$\tau_1 + \tau_2 = \tau_1$$

```lean
def addLeft : PFun (QTy A × QTy A) (QTy A)
  | (none, w) => Part.some w
  | (w, none) => Part.some w
  | (some ta, some _) => Part.some (some ta)  -- Left wins!
```
* **Why it satisfies the equations:** If either side is `none`, it returns the other side.
* **Why it is not `IsLeast`:** On `(some ta, some tb)`, it is defined (`Part.some`), whereas the least operation is undefined (`Part.none`).
* **Logic meaning:** This models **Weakening** (silently discarding the right resource).

---

#### 2. Right-Biased Addition (`addRight`)
*"If both variables exist, pick the second one and drop the first."*
$$\tau_1 + \tau_2 = \tau_2$$

```lean
def addRight : PFun (QTy A × QTy A) (QTy A)
  | (none, w) => Part.some w
  | (w, none) => Part.some w
  | (some _, some tb) => Part.some (some tb)  -- Right wins!
```
* **Logic meaning:** Also models Weakening (silently discarding the left resource).

---

#### 3. Annihilation / Reset (`addReset`)
*"If both variables exist, they collide and destroy each other, leaving an empty slot $\bot$."*
$$\tau_1 + \tau_2 = \bot$$

```lean
def addReset : PFun (QTy A × QTy A) (QTy A)
  | (none, w) => Part.some w
  | (w, none) => Part.some w
  | (some _, some _) => Part.some none  -- Returns ⊥!
```
* Notice that `Part.some none` is **defined**, returning the value $\bot$.
* **Logic meaning:** An error-handling style where collisions wipe out the slot.

---

### Category 2: Intermediate Partial Operations

These operations are **strictly larger** than `addPFun`, but still **not total**:

#### 4. Idempotent Addition (`addIdem`)
*"You can only combine two variables if they have the exact same type."*
$$\tau + \tau = \tau, \qquad \tau_1 + \tau_2 = \text{undefined (if } \tau_1 \neq \tau_2)$$

```lean
def addIdem [DecidableEq A] : PFun (QTy A × QTy A) (QTy A)
  | (none, w) => Part.some w
  | (w, none) => Part.some w
  | (some ta, some tb) =>
      if ta = tb then Part.some (some ta) else Part.none
```
* **Domain:** Larger than `addPFun` (it can add $(\tau, \tau)$), but smaller than `addLeft` (it cannot add $(\tau_1, \tau_2)$ when $\tau_1 \neq \tau_2$).
* **Logic meaning:** This models **Contraction** (reusing a variable if its type matches, like in Relevant Logic or standard non-linear $\lambda$-calculus).

---

### Summary of the Partial Order

We can visualize these operations in the domain order $(\le)$ of partial functions:

```text
addLeft         addRight        addReset
   \               /               /
    \             /               /
     \           /               /
      \         /               /
       \       /               /
        addIdem               /
            \                /
             \              /
              \            /
                addPFun   (IsLeast: The Unique Bottom)
```

### Why the Paper Demands `IsLeast`

Every other candidate in this set introduces a **non-linear behavior**:
* `addLeft` and `addRight` allow **Weakening** (dropping variables).
* `addIdem` allows **Contraction** (sharing variables of the same type).
* `addReset` allows **destructive collisions**.

The **least** operation `addPFun` is the **only one** that allows neither sharing nor dropping, preserving the exact conservation of linear resources.
</details>

lowerBounds s = {x : α | ∀ ⦃a : α⦄, a ∈ s → x ≤ a} = (fun x => ∀ ⦃a : α⦄, s a → x ≤ a)
IsLeast s a = (a ∈ s ∧ a ∈ lowerBounds s) = (s a ∧ ∀ ⦃x : α⦄, s x → a ≤ x) -- a is element of set and all other elemnts are eq or bigger
