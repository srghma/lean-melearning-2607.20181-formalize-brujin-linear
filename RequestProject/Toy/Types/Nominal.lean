module

public import RequestProject.Toy.Types.Ty

@[expose] public section

set_option autoImplicit false

/-!
# A toy `Ty` with named datatypes and one kind of delay

A much smaller cousin of a type grammar whose recursive datatypes are *declared once* and
referred to by a de Bruijn name, and whose delays cannot be nested.

```
NTy n d ::= base b              -- a leaf: nat | bool | string
          | fn NTy NTy          -- the linear arrow σ ⊸ τ
          | data r              -- r : Fin n, a declared datatype by its de Bruijn name
          | lazy (NTy n false)  -- a delay (`Unit → τ`); only at index d = true
```

* `n` is the number of declared datatypes; `data 0` is the newest one.  Declaring one more
  datatype renames every older name `r` to `r.succ` (`NTy.weaken`).
* The index `d : Bool` (an optional argument, `NTy n = NTy n true`) says whether the type may
  be a delay.  A delay holds an `NTy n false`, so **a delay inside a delay cannot be written**
  (`NTy.lazy_not_in_lazy`).  `NTy.mkLazy` reads `Unit → Unit → τ` as one delay
  (`NTy.mkLazy_mkLazy`).
* A delay denotes the value it holds: erasing to the simple types of the paper
  (`NTy.toTy`, into `LinearDB.Ty (Base ⊕ Fin n)`, with the datatype names as extra atoms)
  forgets it (`NTy.toTy_lazy`, `NTy.toTy_mkLazy`).

What cannot be written: a delay directly inside a delay; a datatype name that is not declared
(`Fin n`); a product, a sum or a unit (datatypes are opaque names here, their constructors are
constants of the term language).
-/

namespace LinearDB

namespace Toy

/-- Toy types over `n` declared datatypes.  The second index says whether the type may be a
    delay; it defaults to `true` (any type). -/
inductive NTy : Nat → optParam Bool true → Type where
  /-- A leaf. -/
  | base {n : Nat} {d : Bool} (b : Base) : NTy n d
  /-- The linear function type. -/
  | fn {n : Nat} {d : Bool} : NTy n → NTy n → NTy n d
  /-- A declared datatype, by its de Bruijn name. -/
  | data {n : Nat} {d : Bool} : Fin n → NTy n d
  /-- A delay; its contents are not a delay. -/
  | lazy {n : Nat} : NTy n false → NTy n
  deriving DecidableEq, Repr

namespace NTy

variable {n : Nat}

/-- `Nat`. -/
abbrev nat : NTy n := .base .nat
/-- `Bool`. -/
abbrev bool : NTy n := .base .bool

/-! ## Delays -/

/-- A type that is not a delay, as a type. -/
def relax : NTy n false → NTy n
  | .base b => .base b
  | .fn a b => .fn a b
  | .data r => .data r

/-- The type with its delay removed. -/
def undelay : NTy n → NTy n false
  | .base b => .base b
  | .fn a b => .fn a b
  | .data r => .data r
  | .lazy t => t

/-- Is the type a delay? -/
def isDelay : NTy n → Bool
  | .lazy _ => true
  | _ => false

/-- `Unit → t`: `t` itself if it already is a delay, otherwise a `lazy` of it. -/
def mkLazy : NTy n → NTy n
  | .lazy t => .lazy t
  | t => .lazy t.undelay

@[simp] theorem isDelay_relax (t : NTy n false) : t.relax.isDelay = false := by
  cases t <;> rfl

@[simp] theorem undelay_relax (t : NTy n false) : t.relax.undelay = t := by
  cases t <;> rfl

/-- The contents of a delay are never a delay. -/
theorem lazy_not_in_lazy (t u : NTy n false) : t.relax ≠ .lazy u := by
  cases t <;> nofun

/-- `Unit → Unit → τ` is `Unit → τ`. -/
@[simp] theorem mkLazy_mkLazy (t : NTy n) : mkLazy (mkLazy t) = mkLazy t := by
  cases t <;> rfl

/-- `mkLazy` of a type that is not a delay is `lazy`. -/
@[simp] theorem mkLazy_relax (t : NTy n false) : mkLazy t.relax = .lazy t := by
  cases t <;> rfl

/-- The result of `mkLazy` is a delay. -/
theorem isDelay_mkLazy (t : NTy n) : (mkLazy t).isDelay = true := by
  cases t <;> rfl

/-! ## Renaming the datatypes -/

/-- Rename the declared datatypes a type mentions. -/
def map {m : Nat} (f : Fin n → Fin m) {d : Bool} : NTy n d → NTy m d
  | .base b => .base b
  | .fn a b => .fn (map f a) (map f b)
  | .data r => .data (f r)
  | .lazy t => .lazy (map f t)

/-- Weakening into a signature with one more (newest) datatype. -/
abbrev weaken {d : Bool} (t : NTy n d) : NTy (n + 1) d := map Fin.succ t

@[simp] theorem map_id {d : Bool} (t : NTy n d) : map (fun r => r) t = t := by
  induction t <;> simp_all [map]

@[simp] theorem map_map {m k : Nat} (f : Fin n → Fin m) (g : Fin m → Fin k) {d : Bool}
    (t : NTy n d) : map g (map f t) = map (fun r => g (f r)) t := by
  induction t <;> simp_all [map]

/-- Renaming commutes with forgetting that a type is not a delay. -/
theorem map_relax {m : Nat} (f : Fin n → Fin m) (t : NTy n false) :
    map f t.relax = (map f t).relax := by
  cases t <;> rfl

/-! ## Erasure to the simple types of the paper -/

/-- The paper's simple type of a toy type: the leaves and the datatype names become atoms, a
    delay is forgotten (it denotes the value it holds). -/
def toTy {d : Bool} : NTy n d → Ty (Base ⊕ Fin n)
  | .base b => .atom (.inl b)
  | .fn a b => .arr (toTy a) (toTy b)
  | .data r => .atom (.inr r)
  | .lazy t => toTy t

@[simp] theorem toTy_lazy (t : NTy n false) : (NTy.lazy t).toTy = t.toTy := rfl

@[simp] theorem toTy_relax (t : NTy n false) : t.relax.toTy = t.toTy := by
  cases t <;> rfl

@[simp] theorem toTy_undelay (t : NTy n) : t.undelay.toTy = t.toTy := by
  cases t <;> rfl

/-- A delay does not change what a type denotes. -/
@[simp] theorem toTy_mkLazy (t : NTy n) : (mkLazy t).toTy = t.toTy := by
  cases t <;> rfl

/-- Erasure commutes with renaming (the atoms are renamed by `Sum.map id f`). -/
theorem toTy_map {m : Nat} (f : Fin n → Fin m) {d : Bool} (t : NTy n d) :
    (map f t).toTy = t.toTy.map (Sum.map id f) := by
  induction t <;> simp_all [map, toTy, Ty.map]

end NTy

end Toy

end LinearDB

end
