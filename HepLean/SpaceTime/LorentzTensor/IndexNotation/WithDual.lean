/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.GetDual
import Mathlib.Algebra.Order.Ring.Nat
/-!

# Indices with duals.

In this file we define the following finite sets:

- Given an index list `l₁`, the finite set, `l₁.withDual`, of (positions in) `l₁`
  corresponding to those indices which have a dual in `l₁`. This is equivalent to those indices
  of `l₁` for which `getDual?` is `some`.
- Given two index lists `l₁` and `l₂`, the finite set, `l₁.withDualInOther l₂` of (positions in)
  `l₁` corresponding to those indices which have a dual in `l₂`. This is equivalent to those indices
  of `l₁` for which `l₁.getDualInOther? l₂` is `some`.

For example for `l₁ := ['ᵘ¹', 'ᵘ²', 'ᵤ₁', 'ᵘ¹']` and `l₂ := ['ᵘ³', 'ᵘ²', 'ᵘ⁴', 'ᵤ₂']` we have
`l₁.withDual = {0, 2, 3}` and `l₁.withDualInOther l₂ = {1}`.

We prove some properties of these finite sets. In particular, we prove properties
related to how they interact with appending two index lists.

-/

namespace IndexNotation

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

/-!

## Finsets on which getDual? and getDualInOther? are some.

-/

/-- The finite set of indices of an index list which have a dual in that index list. -/
def withDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isSome) Finset.univ

/-- The finite set of indices of an index list which have a dual in another provided index list. -/
def withDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDualInOther? l2 i).isSome) Finset.univ

/-!

## Basic properties of withDual

-/

@[simp]
lemma withDual_isSome (i : l.withDual) : (l.getDual? i).isSome := by
  simpa [withDual] using i.2

@[simp]
lemma mem_withDual_iff_isSome (i : Fin l.length) : i ∈ l.withDual ↔ (l.getDual? i).isSome := by
  simp [withDual]

lemma not_mem_withDual_iff_isNone (i : Fin l.length) :
    i ∉ l.withDual ↔ (l.getDual? i).isNone := by
  simp only [mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none]

lemma mem_withDual_iff_exists : i ∈ l.withDual ↔ ∃ j, l.AreDualInSelf i j := by
  simp [withDual, Finset.mem_filter, Finset.mem_univ, getDual?]
  exact Fin.isSome_find_iff

/-!

## Basic properties of withDualInOther

-/

@[simp]
lemma mem_withInDualOther_iff_isSome (i : Fin l.length) :
    i ∈ l.withDualInOther l2 ↔ (l.getDualInOther? l2 i).isSome := by
  simp only [withDualInOther, getDualInOther?, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_withInDualOther_iff_exists :
    i ∈ l.withDualInOther l2 ↔ ∃ (j : Fin l2.length), l.AreDualInOther l2 i j := by
  simp [withDualInOther, Finset.mem_filter, Finset.mem_univ, getDualInOther?]
  exact Fin.isSome_find_iff

/-!

## Append properties of withDual

-/

lemma withDual_append_eq_disjSum : (l ++ l2).withDual =
    Equiv.finsetCongr appendEquiv
      ((l.withDual ∪ l.withDualInOther l2).disjSum
      (l2.withDual ∪ l2.withDualInOther l)) := by
  ext i
  obtain ⟨k, hk⟩ := appendEquiv.surjective i
  subst hk
  match k with
  | Sum.inl k =>
    simp
  | Sum.inr k =>
    simp

/-!

## Append properties of withDualInOther

-/

lemma append_withDualInOther_eq :
    (l ++ l2).withDualInOther l3 =
    Equiv.finsetCongr appendEquiv ((l.withDualInOther l3).disjSum (l2.withDualInOther l3)) := by
  rw [Finset.ext_iff]
  intro i
  obtain ⟨k, hk⟩ := appendEquiv.surjective i
  subst hk
  match k with
  | Sum.inl k =>
    simp
  | Sum.inr k =>
    simp

lemma withDualInOther_append_eq : l.withDualInOther (l2 ++ l3) =
    l.withDualInOther l2 ∪ l.withDualInOther l3 := by
  ext i
  simp

end IndexList

end IndexNotation
