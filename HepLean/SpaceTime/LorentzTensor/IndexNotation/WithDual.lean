/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.GetDual
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.FinCases
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

## Relationship between membership of withDual and countP on id.

-/

lemma countId_gt_zero_of_mem_withDual (i : Fin l.length) (h : i ∈ l.withDual) :
    1 < l.countId (l.val.get i) := by
  rw [countId]
  rw [mem_withDual_iff_exists] at h
  obtain ⟨j, hj⟩ := h
  simp [AreDualInSelf, idMap] at hj
  by_contra hn
  have hn' := l.countId_index_neq_zero i
  have hl : 2 ≤ l.val.countP (fun J => (l.val.get i).id = J.id) := by
    by_cases hij : i < j
    · have hsub : List.Sublist [l.val.get i, l.val.get j] l.val := by
        rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
        refine ⟨⟨⟨![i, j], ?_⟩, ?_⟩, ?_⟩
        · refine List.nodup_ofFn.mp ?_
          simpa using Fin.ne_of_lt hij
        · intro a b
          fin_cases a, b
            <;> simp [hij]
          exact Fin.le_of_lt hij
        · intro a
          fin_cases a <;> rfl
      simpa [hj.2] using List.Sublist.countP_le
        (fun (j : Index X) => decide (l.val[i].id = j.id)) hsub
    · have hij' : j < i := by omega
      have hsub : List.Sublist [l.val.get j, l.val.get i] l.val := by
        rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
        refine ⟨⟨⟨![j, i], ?_⟩, ?_⟩, ?_⟩
        · refine List.nodup_ofFn.mp ?_
          simpa using Fin.ne_of_lt hij'
        · intro a b
          fin_cases a, b
            <;> simp [hij']
          exact Fin.le_of_lt hij'
        · intro a
          fin_cases a <;> rfl
      simpa [hj.2] using List.Sublist.countP_le
        (fun (j : Index X) => decide (l.val[i].id = j.id)) hsub
  omega

lemma countId_of_not_mem_withDual (i : Fin l.length)(h : i ∉ l.withDual) :
    l.countId (l.val.get i) = 1 := by
  rw [countId]
  rw [mem_withDual_iff_exists] at h
  simp [AreDualInSelf] at h
  have h1 : ¬ l.val.Duplicate (l.val.get i) := by
      by_contra hn
      rw [List.duplicate_iff_exists_distinct_get] at hn
      obtain ⟨k, j, h1, h2, h3⟩ := hn
      by_cases hi : k = i
        <;> by_cases hj : j = i
      · subst hi hj
        simp at h1
      · subst hi
        exact h j (fun a => hj (id (Eq.symm a))) (congrArg Index.id h3)
      · subst hj
        exact h k (fun a => hi (id (Eq.symm a))) (congrArg Index.id h2)
      · exact h j (fun a => hj (id (Eq.symm a))) (congrArg Index.id h3)
  rw [List.duplicate_iff_two_le_count] at h1
  simp at h1
  by_cases hx : List.count l.val[i] l.val = 0
  · rw [List.count_eq_zero] at hx
    refine False.elim (h i (fun _ => hx ?_) rfl)
    exact List.getElem_mem l.val (↑i) (Fin.val_lt_of_le i (le_refl l.length))
  · have hln : List.count l.val[i] l.val = 1 := by
      rw [Nat.lt_succ, Nat.le_one_iff_eq_zero_or_eq_one] at h1
      simp at hx
      simpa [hx] using h1
    rw [← hln, List.count]
    refine (List.countP_congr (fun xt hxt => ?_))
    let xid := l.val.indexOf xt
    have h2 := List.indexOf_lt_length.mpr hxt
    simp only [decide_eq_true_eq, Fin.getElem_fin, beq_iff_eq]
    by_cases hxtx : ⟨xid, h2⟩ = i
    · rw [(List.indexOf_get h2).symm, hxtx]
      simp only [List.get_eq_getElem]
    · refine Iff.intro (fun h' => False.elim (h i (fun _ => ?_) rfl)) (fun h' => ?_)
      · exact h ⟨xid, h2⟩ (fun a => hxtx (id (Eq.symm a))) (by
          rw [(List.indexOf_get h2).symm] at h'; exact h')
      · rw [h']
        rfl

lemma mem_withDual_iff_countId_gt_one (i : Fin l.length) :
    i ∈ l.withDual ↔ 1 < l.countId (l.val.get i) := by
  refine Iff.intro (fun h => countId_gt_zero_of_mem_withDual l i h) (fun h => ?_)
  by_contra hn
  have hn' := countId_of_not_mem_withDual l i hn
  omega

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
