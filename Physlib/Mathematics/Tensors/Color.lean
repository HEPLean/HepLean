/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Init
/-!

# Colors of tensor slots

A color is a kind of index with a variance, up or down. Its dual has the same kind and the other
variance.

## i. Overview

The color of a tensor slot says which representation the slot carries. It is unrelated to the
color charge of QCD. A color `⟨κ, v⟩ : Color K` pairs a kind of index `κ : K` with a variance `v`,
`up` or `down`. For Lorentz tensors there is one kind, `vec`. The index of `v^μ` has color
`⟨vec, up⟩` and the index of `w_μ` has color `⟨vec, down⟩`. A color is a label, not a space. A
species (`Species.lean`) assigns a space to each color, `V ⟨vec, up⟩ = ℝ⁴` and
`V ⟨vec, down⟩ = (ℝ⁴)*`.

The dual of `⟨κ, v⟩` is `⟨κ, v.dual⟩`, with `up.dual = down` and `down.dual = up`. A contraction
such as `v^μ w_μ` pairs a slot of color `c` with a slot of color `c.dual`.

A variance stores two booleans, whether it is up and whether it is down, and `dual` swaps them.
So `v.dual.dual = v` and `c.dual.dual = c` hold by `rfl` for a variable `v` or `c`, and a
statement that takes a dual twice needs no cast. With an inductive `up | down` the same equation
needs a case split on `v`.

## ii. Key results

- `Variance` : the variance of an index, with `Variance.up`, `Variance.down` and `Variance.dual`.
- `Color` : a kind of index and a variance.
- `Color.dual` : the dual color, with `Color.dual_dual : c.dual.dual = c` by `rfl`.

## iii. Table of contents

- A. Up and down
- B. Colors

## iv. References

-/

@[expose] public section

namespace Tensors

/-!

## A. Up and down

-/

/-- The variance of an index, up (contravariant, `v^μ`) or down (covariant, `w_μ`). It stores
whether the index is up and whether it is down, so that `dual` swaps the two fields and
`v.dual.dual = v` holds by `rfl`. A match on both fields has two impossible cases, closed by
`ne`. -/
structure Variance where
  /-- Whether the index is up. -/
  isUp : Bool
  /-- Whether the index is down. -/
  isDown : Bool
  /-- An index is either up or down. -/
  ne : isUp ≠ isDown
deriving DecidableEq

namespace Variance

/-- An upper index, as in `v^μ`. -/
def up : Variance := ⟨true, false, by decide⟩

/-- A lower index, as in `w_μ`. -/
def down : Variance := ⟨false, true, by decide⟩

/-- The dual variance, which exchanges up and down. It is an `abbrev` because rewriting with the
species laws needs `c.dual.dual` and `c` to agree when only reducible definitions unfold. -/
abbrev dual (v : Variance) : Variance := ⟨v.isDown, v.isUp, v.ne.symm⟩

@[simp]
lemma dual_up : up.dual = down := rfl

@[simp]
lemma dual_down : down.dual = up := rfl

/-- Taking the dual twice gives back the variance, by `rfl`. -/
lemma dual_dual (v : Variance) : v.dual.dual = v := rfl

end Variance

/-!

## B. Colors

-/

/-- A color `⟨κ, v⟩`: a kind of index `κ : K` and its variance `v`. -/
structure Color (K : Type) where
  /-- The kind of index, such as the Lorentz vector index `vec` or a left-handed Weyl index. -/
  kind : K
  /-- Whether the index is up or down. -/
  variance : Variance
deriving DecidableEq

/-- The dual color: the same kind, the other variance. -/
abbrev Color.dual {K : Type} (c : Color K) : Color K := ⟨c.kind, c.variance.dual⟩

/-- The dual of `⟨κ, v⟩` is `⟨κ, v.dual⟩`, so that `simp` rewrites the dual of `⟨κ, up⟩` to
`⟨κ, down⟩`. -/
@[simp]
lemma Color.dual_mk {K : Type} (κ : K) (v : Variance) :
    (⟨κ, v⟩ : Color K).dual = ⟨κ, v.dual⟩ := rfl

/-- Taking the dual twice gives back the color, by `rfl`. -/
lemma Color.dual_dual {K : Type} (c : Color K) : c.dual.dual = c := rfl

end Tensors
