/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.WithDual
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Sort
/-!

# With Unique Dual

Finite sets of indices with a unique dual.

-/

namespace IndexNotation


namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)


/-!

## Unique duals

-/

/-- The finite set of indices of an index list which have a unique dual in that index list. -/
def withUniqueDual : Finset (Fin l.length) :=
  Finset.filter (fun i => i ∈ l.withDual ∧
    ∀ j, l.AreDualInSelf i j → j = l.getDual? i) Finset.univ

/-- The finite set of indices of an index list which have a unique dual in another, provided, index
  list. -/
def withUniqueDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => i ∉ l.withDual ∧ i ∈ l.withDualInOther l2
     ∧ (∀ j, l.AreDualInOther l2 i j → j = l.getDualInOther? l2 i)) Finset.univ

/-!

## Basic properties of withUniqueDual

-/

@[simp, nolint simpNF]
lemma mem_withDual_of_mem_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    i ∈ l.withDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and] at h
  simpa using h.1

@[simp]
lemma mem_withUniqueDual_isSome (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    (l.getDual? i).isSome := by
  simpa using mem_withDual_of_mem_withUniqueDual l i h

lemma mem_withDual_of_withUniqueDual (i : l.withUniqueDual) :
    i.1 ∈ l.withDual :=
  mem_withDual_of_mem_withUniqueDual l (↑i) i.2



/-!

## Basic properties of withUniqueDualInOther

-/

lemma not_mem_withDual_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    i.1 ∉ l.withDual := by
  have hi := i.2
  simp only [withUniqueDualInOther, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
    true_and] at hi
  exact hi.2.1

lemma mem_withDualInOther_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    i.1 ∈ l.withDualInOther l2 := by
  have hi := i.2
  simp only [withUniqueDualInOther, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
    true_and] at hi
  exact hi.2.2.1

@[simp]
lemma mem_withUniqueDualInOther_isSome (i : Fin l.length) (hi : i ∈ l.withUniqueDualInOther l2) :
    (l.getDualInOther? l2 i).isSome := by
  simp only [withUniqueDualInOther, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact (mem_withInDualOther_iff_isSome l l2 i).mp hi.2.1

/-!

## Properties of getDual? and withUniqueDual

-/

lemma all_dual_eq_getDual?_of_mem_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    ∀ j, l.AreDualInSelf i j → j = l.getDual? i := by
  simp [withUniqueDual] at h
  exact fun j hj => h.2 j hj

lemma some_eq_getDual?_of_withUniqueDual_iff (i j : Fin l.length) (h : i ∈ l.withUniqueDual) :
    l.AreDualInSelf i j ↔ some j = l.getDual? i := by
  apply Iff.intro
  exact fun h' => all_dual_eq_getDual?_of_mem_withUniqueDual l i h j h'
  intro h'
  have hj : j = (l.getDual? i).get (mem_withUniqueDual_isSome l i h) :=
    Eq.symm (Option.get_of_mem (mem_withUniqueDual_isSome l i h) (id (Eq.symm h')))
  subst hj
  exact (getDual?_get_areDualInSelf l i (mem_withUniqueDual_isSome l i h)).symm

@[simp]
lemma eq_getDual?_get_of_withUniqueDual_iff (i j : Fin l.length) (h : i ∈ l.withUniqueDual) :
    l.AreDualInSelf i j ↔ j = (l.getDual? i).get (mem_withUniqueDual_isSome l i h) := by
  rw [l.some_eq_getDual?_of_withUniqueDual_iff i j h]
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  exact Eq.symm (Option.get_of_mem (mem_withUniqueDual_isSome l i h) (id (Eq.symm h')))
  simp [h']

lemma eq_of_areDualInSelf_withUniqueDual {j k : Fin l.length} (i : l.withUniqueDual)
    (hj : l.AreDualInSelf i j) (hk : l.AreDualInSelf i k) : j = k := by
  simp at hj hk
  exact hj.trans hk.symm

@[simp, nolint simpNF]
lemma getDual?_get_getDual?_get_of_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    (l.getDual? ((l.getDual? i).get (mem_withUniqueDual_isSome l i h))).get
      (l.getDual?_getDual?_get_isSome i (mem_withUniqueDual_isSome l i h)) = i := by
  by_contra hn
  have h' : l.AreDualInSelf i  ((l.getDual? ((l.getDual? i).get
      (mem_withUniqueDual_isSome l i h))).get (
      getDual?_getDual?_get_isSome l i (mem_withUniqueDual_isSome l i h))) := by
    simp [AreDualInSelf, hn]
    exact fun a => hn (id (Eq.symm a))
  simp [h] at h'

@[simp, nolint simpNF]
lemma getDual?_getDual?_get_of_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    l.getDual? ((l.getDual? i).get (mem_withUniqueDual_isSome l i h)) = some i := by
  nth_rewrite 3 [← l.getDual?_get_getDual?_get_of_withUniqueDual i h]
  exact Option.eq_some_of_isSome
    (getDual?_getDual?_get_isSome l i (mem_withUniqueDual_isSome l i h))

@[simp]
lemma getDual?_getDual?_of_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    (l.getDual? i).bind l.getDual? = some i := by
  have h1 : (l.getDual? i) = some ((l.getDual? i).get (mem_withUniqueDual_isSome l i h)) :=
    Option.eq_some_of_isSome (mem_withUniqueDual_isSome l i h)
  nth_rewrite 1 [h1]
  rw [Option.some_bind']
  exact getDual?_getDual?_get_of_withUniqueDual l i h

@[simp, nolint simpNF]
lemma getDual?_get_of_mem_withUnique_mem (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    (l.getDual? i).get (l.mem_withUniqueDual_isSome i h) ∈ l.withUniqueDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_getDual?_get_isSome, true_and]
  intro j hj
  have h1 : i = j := by
    by_contra hn
    have h' : l.AreDualInSelf i j := by
      simp only [AreDualInSelf, ne_eq, hn, not_false_eq_true, true_and]
      simp_all only [AreDualInSelf, ne_eq, getDual?_get_id]
    simp [h] at h'
    subst h'
    simp_all
  subst h1
  exact Eq.symm (getDual?_getDual?_get_of_withUniqueDual l i h)


/-!

## Properties of getDualInOther? and withUniqueDualInOther

-/

lemma all_dual_eq_of_withUniqueDualInOther (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    ∀ j, l.AreDualInOther l2 i j → j = l.getDualInOther? l2 i := by
  simp [withUniqueDualInOther] at h
  exact fun j hj => h.2.2 j hj

lemma some_eq_getDualInOther?_of_withUniqueDualInOther_iff (i : Fin l.length) (j : Fin l2.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    l.AreDualInOther l2 i j ↔ some j = l.getDualInOther? l2 i := by
  apply Iff.intro
  exact fun h' => l.all_dual_eq_of_withUniqueDualInOther l2 i h j h'
  intro h'
  have hj : j = (l.getDualInOther? l2 i).get (mem_withUniqueDualInOther_isSome l l2 i h) :=
    Eq.symm (Option.get_of_mem  (mem_withUniqueDualInOther_isSome l l2 i h) (id (Eq.symm h')))
  subst hj
  exact getDualInOther?_areDualInOther_get l l2 i (mem_withUniqueDualInOther_isSome l l2 i h)

@[simp]
lemma eq_getDualInOther?_get_of_withUniqueDualInOther_iff (i : Fin l.length) (j : Fin l2.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    l.AreDualInOther l2 i j ↔ j = (l.getDualInOther? l2 i).get
      (mem_withUniqueDualInOther_isSome l l2 i h) := by
  rw [l.some_eq_getDualInOther?_of_withUniqueDualInOther_iff l2 i j h]
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  exact Eq.symm (Option.get_of_mem (mem_withUniqueDualInOther_isSome l l2 i h) (id (Eq.symm h')))
  simp [h']

@[simp, nolint simpNF]
lemma getDualInOther?_get_getDualInOther?_get_of_withUniqueDualInOther
    (i : Fin l.length) (h : i ∈ l.withUniqueDualInOther l2) :
    (l2.getDualInOther? l ((l.getDualInOther? l2 i).get
    (mem_withUniqueDualInOther_isSome l l2 i h))).get
    (l.getDualInOther?_getDualInOther?_get_isSome l2 i
    (mem_withUniqueDualInOther_isSome l l2 i h)) = i := by
  by_contra hn
  have h' : l.AreDualInSelf i  ((l2.getDualInOther? l ((l.getDualInOther? l2 i).get
      (mem_withUniqueDualInOther_isSome l l2 i h))).get
      (l.getDualInOther?_getDualInOther?_get_isSome l2 i
      (mem_withUniqueDualInOther_isSome l l2 i h))):= by
    simp [AreDualInSelf, hn]
    exact fun a => hn (id (Eq.symm a))
  have h1 := l.not_mem_withDual_of_withUniqueDualInOther l2 ⟨i, h⟩
  simp [getDual?] at h1
  rw [Fin.find_eq_none_iff] at h1
  exact h1 _ h'
@[simp, nolint simpNF]
lemma getDualInOther?_getDualInOther?_get_of_withUniqueDualInOther (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    l2.getDualInOther? l ((l.getDualInOther? l2 i).get (mem_withUniqueDualInOther_isSome l l2 i h))
    = some i := by
  nth_rewrite 3 [← l.getDualInOther?_get_getDualInOther?_get_of_withUniqueDualInOther l2 i h]
  exact Option.eq_some_of_isSome
    (getDualInOther?_getDualInOther?_get_isSome l l2 i (mem_withUniqueDualInOther_isSome l l2 i h))

@[simp]
lemma getDualInOther?_getDualInOther?_of_withUniqueDualInOther
    (i : Fin l.length) (h : i ∈ l.withUniqueDualInOther l2) :
    (l.getDualInOther? l2 i).bind (l2.getDualInOther? l) = some i := by
  have h1 : (l.getDualInOther? l2 i) = some ((l.getDualInOther? l2 i).get
      (mem_withUniqueDualInOther_isSome l l2 i h)) :=
    Option.eq_some_of_isSome (mem_withUniqueDualInOther_isSome l l2 i h)
  nth_rewrite 1 [h1]
  rw [Option.some_bind']
  exact getDualInOther?_getDualInOther?_get_of_withUniqueDualInOther l l2 i h

lemma eq_of_areDualInOther_withUniqueDualInOther {j k : Fin l2.length}
    (i : l.withUniqueDualInOther l2)
    (hj : l.AreDualInOther l2 i j) (hk : l.AreDualInOther l2 i k) : j = k := by
  simp at hj hk
  exact hj.trans hk.symm

lemma getDual?_of_getDualInOther?_of_mem_withUniqueInOther_eq_none (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l2) : l2.getDual?
    ((l.getDualInOther? l2 i).get (l.mem_withUniqueDualInOther_isSome l2 i h)) = none := by
  by_contra hn
  rw [← @Option.not_isSome_iff_eq_none, not_not] at hn
  rw [@getDual?_isSome_iff_exists] at hn
  obtain ⟨j, hj⟩ := hn
  have hx : l.AreDualInOther l2 i j := by
    simp [AreDualInOther, hj]
    simp [AreDualInSelf] at hj
    exact hj.2
  have hn := l.eq_of_areDualInOther_withUniqueDualInOther l2 ⟨i, h⟩ hx
    (getDualInOther?_areDualInOther_get l l2 i (mem_withUniqueDualInOther_isSome l l2 i h))
  subst hn
  simp_all

@[simp, nolint simpNF]
lemma getDualInOther?_get_of_mem_withUniqueInOther_mem (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    (l.getDualInOther? l2 i).get
    (l.mem_withUniqueDualInOther_isSome l2 i h) ∈ l2.withUniqueDualInOther l := by
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDualInOther?_getDualInOther?_get_isSome, true_and]
  apply And.intro
  exact getDual?_of_getDualInOther?_of_mem_withUniqueInOther_eq_none l l2 i h
  intro j hj
  simp only [h, getDualInOther?_getDualInOther?_get_of_withUniqueDualInOther, Option.some.injEq]
  by_contra hn
  have hx : l.AreDualInSelf i j := by
    simp [AreDualInSelf, hn]
    simp [AreDualInOther] at hj
    exact ⟨fun a => hn (id (Eq.symm a)), hj⟩
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, getDual?, Bool.not_eq_true,
    Option.not_isSome, Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter,
    Finset.mem_univ, true_and] at h
  rw [Fin.find_eq_none_iff] at h
  simp_all only



@[simp]
lemma getDualInOther?_self_of_mem_withUniqueInOther (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l) :
    l.getDualInOther? l i = some i := by
  rw [all_dual_eq_of_withUniqueDualInOther l l i h i rfl]




/-!

## Properties of getDual?, withUniqueDual and append

-/

lemma append_inl_not_mem_withDual_of_withDualInOther (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l.withDual ↔ ¬ i ∈ l.withDualInOther l2 := by
  refine Iff.intro (fun hs => ?_) (fun ho => ?_)
  · by_contra ho
    obtain ⟨j, hj⟩ := (l.mem_withDual_iff_exists).mp hs
    obtain ⟨k, hk⟩ := (l.mem_withInDualOther_iff_exists l2).mp ho
    have h1 : appendEquiv (Sum.inl j) = appendEquiv (Sum.inr k) := by
      refine (l ++ l2).eq_of_areDualInSelf_withUniqueDual ⟨appendEquiv (Sum.inl i), h⟩ ?_ ?_
      exact AreDualInSelf.append_inl_inl.mpr hj
      simpa using hk
    simp at h1
  · have ht : ((l ++ l2).getDual? (appendEquiv (Sum.inl i))).isSome :=
      mem_withUniqueDual_isSome (l ++ l2) (appendEquiv (Sum.inl i)) h
    simp only [getDual?_isSome_append_inl_iff] at ht
    simp_all


lemma append_inr_not_mem_withDual_of_withDualInOther (i : Fin l2.length)
    (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l2.withDual ↔ ¬ i ∈ l2.withDualInOther l := by
  refine Iff.intro (fun hs => ?_) (fun ho => ?_)
  · by_contra ho
    obtain ⟨j, hj⟩ := (l2.mem_withDual_iff_exists).mp hs
    obtain ⟨k, hk⟩ := (l2.mem_withInDualOther_iff_exists l).mp ho
    have h1 : appendEquiv (Sum.inr j) = appendEquiv (Sum.inl k) := by
      refine (l ++ l2).eq_of_areDualInSelf_withUniqueDual ⟨appendEquiv (Sum.inr i), h⟩ ?_ ?_
      exact (AreDualInSelf.append_inr_inr l l2 i j).mpr hj
      simpa using hk
    simp at h1
  · have ht : ((l ++ l2).getDual? (appendEquiv (Sum.inr i))).isSome :=
      mem_withUniqueDual_isSome (l ++ l2) (appendEquiv (Sum.inr i)) h
    simp only [getDual?_isSome_append_inr_iff] at ht
    simp_all


lemma getDual?_append_symm_of_withUniqueDual_of_inl (i : Fin l.length) (k : Fin l2.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = some (appendEquiv (Sum.inr k))
    ↔ (l2 ++ l).getDual? (appendEquiv (Sum.inr i)) = some (appendEquiv (Sum.inl k)) := by
  have h := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  by_cases hs : (l.getDual? i).isSome
  <;> by_cases ho : (l.getDualInOther? l2 i).isSome
  <;> simp_all [hs, ho]

lemma getDual?_append_symm_of_withUniqueDual_of_inl' (i k : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = some (appendEquiv (Sum.inl k))
    ↔ (l2 ++ l).getDual? (appendEquiv (Sum.inr i)) = some (appendEquiv (Sum.inr k)) := by
  have h := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  by_cases hs : (l.getDual? i).isSome
  <;> by_cases ho : (l.getDualInOther? l2 i).isSome
  <;> simp_all [hs, ho]

lemma getDual?_append_symm_of_withUniqueDual_of_inr (i : Fin l2.length) (k : Fin l.length)
    (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = some (appendEquiv (Sum.inl k))
    ↔ (l2 ++ l).getDual? (appendEquiv (Sum.inl i)) = some (appendEquiv (Sum.inr k)) := by
  have h := l.append_inr_not_mem_withDual_of_withDualInOther l2 i h
  by_cases hs : (l2.getDual? i).isSome
  <;> by_cases ho : (l2.getDualInOther? l i).isSome
  <;> simp_all [hs, ho]

lemma getDual?_append_symm_of_withUniqueDual_of_inr' (i k : Fin l2.length)
    (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = some (appendEquiv (Sum.inr k))
    ↔ (l2 ++ l).getDual? (appendEquiv (Sum.inl i)) = some (appendEquiv (Sum.inl k)) := by
  have h := l.append_inr_not_mem_withDual_of_withDualInOther l2 i h
  by_cases hs : (l2.getDual? i).isSome
  <;> by_cases ho : (l2.getDualInOther? l i).isSome
  <;> simp_all [hs, ho]

lemma mem_withUniqueDual_append_symm (i : Fin l.length) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual ↔
    appendEquiv (Sum.inr i) ∈ (l2 ++ l).withUniqueDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_isSome_append_inl_iff, true_and, getDual?_isSome_append_inr_iff, and_congr_right_iff]
  intro h
  refine Iff.intro (fun h' j hj => ?_) (fun h' j hj => ?_)
  · obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      have hk' := h' (appendEquiv (Sum.inr k))
      simp only [AreDualInSelf.append_inl_inr] at hk'
      simp only [AreDualInSelf.append_inr_inl] at hj
      refine ((l.getDual?_append_symm_of_withUniqueDual_of_inl l2 _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inl_inr, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, getDual?_isSome_append_inl_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        getDual?_areDualInSelf_get]
    | Sum.inr k =>
      have hk' :=  h' (appendEquiv (Sum.inl k))
      simp only [AreDualInSelf.append_inl_inl] at hk'
      simp only [AreDualInSelf.append_inr_inr] at hj
      refine  ((l.getDual?_append_symm_of_withUniqueDual_of_inl' l2 _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inl_inl, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, getDual?_isSome_append_inl_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        getDual?_areDualInSelf_get]
  · obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      have hk' := h' (appendEquiv (Sum.inr k))
      simp only [AreDualInSelf.append_inr_inr] at hk'
      simp only [AreDualInSelf.append_inl_inl] at hj
      refine ((l2.getDual?_append_symm_of_withUniqueDual_of_inr' l _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inr_inr, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, getDual?_isSome_append_inr_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        getDual?_areDualInSelf_get]
    | Sum.inr k =>
      have hk' :=  h' (appendEquiv (Sum.inl k))
      simp only [AreDualInSelf.append_inr_inl] at hk'
      simp only [AreDualInSelf.append_inl_inr] at hj
      refine  ((l2.getDual?_append_symm_of_withUniqueDual_of_inr l _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inr_inl, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, getDual?_isSome_append_inr_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        getDual?_areDualInSelf_get]

@[simp]
lemma not_mem_withDualInOther_of_inl_mem_withUniqueDual  (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) (hs : i ∈ l.withUniqueDual) :
    ¬ i ∈ l.withUniqueDualInOther l2 := by
  have hn := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  simp_all
  by_contra ho
  have ho' :  (l.getDualInOther? l2 i).isSome := by
    exact mem_withUniqueDualInOther_isSome l l2 i ho
  simp_all [Option.isSome_none, Bool.false_eq_true]

@[simp]
lemma not_mem_withUniqueDual_of_inl_mem_withUnqieuDual (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) (hi : i ∈ l.withUniqueDualInOther l2) :
    ¬ i ∈ l.withUniqueDual  := by
  by_contra hs
  simp_all only [not_mem_withDualInOther_of_inl_mem_withUniqueDual]

@[simp]
lemma mem_withUniqueDual_of_inl (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) (hi : (l.getDual? i).isSome) :
    i ∈ l.withUniqueDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_isSome_append_inl_iff, true_and] at h ⊢
  apply And.intro hi
  intro j hj
  have hj' := h.2 (appendEquiv (Sum.inl j))
  simp at hj'
  have hj'' := hj' hj
  simp [hi] at hj''
  simp_all

@[simp]
lemma mem_withUniqueDualInOther_of_inl_withDualInOther  (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual)
    (hi : (l.getDualInOther? l2 i).isSome) : i ∈ l.withUniqueDualInOther l2 := by
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and]
  have hn := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  simp_all only [mem_withDual_iff_isSome, mem_withInDualOther_iff_isSome, not_true_eq_false,
    iff_false, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none, true_and]
  intro j hj
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_isSome_append_inl_iff, true_and] at h
  have hj' := h.2 (appendEquiv (Sum.inr j))
  simp only [AreDualInSelf.append_inl_inr] at hj'
  have hj'' := hj' hj
  simp only [hn, Option.isNone_none, hi, getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome,
    Option.some.injEq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq] at hj''
  simp_all only [getDualInOther?_areDualInOther_get, Option.isSome_none, Bool.false_eq_true,
    or_true, Option.isNone_none, getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome,
    Option.some.injEq, true_and, AreDualInSelf.append_inl_inr, imp_self, Option.some_get]

lemma withUniqueDual_iff_not_withUniqueDualInOther_of_inl_withUniqueDualInOther
    (i : Fin l.length) (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l.withUniqueDual ↔ ¬ i ∈ l.withUniqueDualInOther l2 := by
  by_cases h' : (l.getDual? i).isSome
  have hn : i ∈ l.withUniqueDual := mem_withUniqueDual_of_inl l l2 i h h'
  simp_all
  have hn := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  simp_all
  simp [withUniqueDual]
  simp_all
  exact mem_withUniqueDualInOther_of_inl_withDualInOther l l2 i h (Option.ne_none_iff_isSome.mp hn)

lemma append_inl_mem_withUniqueDual_of_withUniqueDual (i : Fin l.length)
    (h : i ∈ l.withUniqueDual) (hn : i ∉ l.withDualInOther l2) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_isSome_append_inl_iff, true_and]
  apply And.intro
  simp_all
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k => simp_all
  | Sum.inr k =>
    simp at hj
    refine False.elim (hn ?_)
    exact (l.mem_withInDualOther_iff_exists _).mpr ⟨k, hj⟩

lemma append_inl_mem_of_withUniqueDualInOther (i : Fin l.length)
    (ho : i ∈ l.withUniqueDualInOther l2) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_isSome_append_inl_iff, true_and]
  apply And.intro
  simp_all only [mem_withUniqueDualInOther_isSome, or_true]
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  have hs := l.not_mem_withDual_of_withUniqueDualInOther l2 ⟨i, ho⟩
  match k with
  | Sum.inl k =>
    refine False.elim (hs ?_)
    simp at hj
    exact (l.mem_withDual_iff_exists).mpr ⟨k, hj⟩
  | Sum.inr k =>
    simp_all

@[simp]
lemma append_inl_mem_withUniqueDual_iff (i : Fin l.length) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual ↔
    ((i ∈ l.withUniqueDual ∧ i ∉ l.withDualInOther l2) ↔ ¬ i ∈ l.withUniqueDualInOther l2) := by
  apply Iff.intro
  · intro h
    apply Iff.intro
    · intro hs
      exact (l.withUniqueDual_iff_not_withUniqueDualInOther_of_inl_withUniqueDualInOther l2 i
        h).mp hs.1
    · intro ho
      have hs := ((l.withUniqueDual_iff_not_withUniqueDualInOther_of_inl_withUniqueDualInOther l2 i
        h).mpr ho)
      apply And.intro hs
      refine (l.append_inl_not_mem_withDual_of_withDualInOther l2 i h).mp ?_
      exact (l.mem_withDual_of_withUniqueDual ⟨i, hs⟩)
  · intro h
    by_cases ho : i ∈ l.withUniqueDualInOther l2
    · exact append_inl_mem_of_withUniqueDualInOther l l2 i ho
    · exact append_inl_mem_withUniqueDual_of_withUniqueDual l l2 i (h.mpr ho).1 (h.mpr ho).2

@[simp]
lemma append_inr_mem_withUniqueDual_iff (i : Fin l2.length) :
    appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual ↔
    ((i ∈ l2.withUniqueDual ∧ i ∉ l2.withDualInOther l) ↔ ¬ i ∈ l2.withUniqueDualInOther l) := by
  rw [← mem_withUniqueDual_append_symm]
  exact append_inl_mem_withUniqueDual_iff l2 l i

lemma append_withUniqueDual : (l ++ l2).withUniqueDual =
    Finset.map (l.appendInl l2)
    ((l.withUniqueDual ∩ (l.withDualInOther l2)ᶜ) ∪ l.withUniqueDualInOther l2)
    ∪ Finset.map (l.appendInr l2)
    ((l2.withUniqueDual ∩ (l2.withDualInOther l)ᶜ) ∪ l2.withUniqueDualInOther l) := by
  rw [Finset.ext_iff]
  intro j
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [append_inl_mem_withUniqueDual_iff, Finset.mem_union]
    apply Iff.intro
    · intro h
      apply Or.inl
      simp only [Finset.mem_map, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
        mem_withInDualOther_iff_isSome, Bool.not_eq_true, Option.not_isSome,
        Option.isNone_iff_eq_none]
      use k
      simp only [appendInl, Function.Embedding.coeFn_mk, Function.comp_apply, and_true]
      by_cases hk : k ∈ l.withUniqueDualInOther l2
      exact Or.inr hk
      have hk' := h.mpr hk
      simp_all only [not_false_eq_true, and_self, mem_withInDualOther_iff_isSome, Bool.not_eq_true,
        Option.not_isSome, Option.isNone_iff_eq_none, or_false]
    · intro h
      simp only [Finset.mem_map, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
        mem_withInDualOther_iff_isSome, Bool.not_eq_true, Option.not_isSome,
        Option.isNone_iff_eq_none] at h
      cases' h with h h
      · obtain ⟨j, hj⟩ := h
        have hjk : j = k := by
          simp only [appendInl, Function.Embedding.coeFn_mk, Function.comp_apply,
            EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] at hj
          exact hj.2
        subst hjk
        have hj1 := hj.1
        cases' hj1 with hj1 hj1
        · simp_all only [and_self, true_or, true_and, mem_withInDualOther_iff_isSome,
          Option.isSome_none, Bool.false_eq_true, not_false_eq_true, true_iff]
          by_contra hn
          have h' := l.mem_withDualInOther_of_withUniqueDualInOther l2 ⟨j, hn⟩
          simp_all only [mem_withInDualOther_iff_isSome, Option.isSome_none, Bool.false_eq_true]
        · simp_all only [or_true, true_and, mem_withInDualOther_iff_isSome,
          mem_withUniqueDualInOther_isSome, not_true_eq_false, and_false]
      · obtain ⟨j, hj⟩ := h
        simp only [appendInr, Function.Embedding.coeFn_mk, Function.comp_apply,
          EmbeddingLike.apply_eq_iff_eq, and_false] at hj
  | Sum.inr k =>
    simp only [append_inr_mem_withUniqueDual_iff, Finset.mem_union]
    apply Iff.intro
    · intro h
      apply Or.inr
      simp only [Finset.mem_map, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
        mem_withInDualOther_iff_isSome, Bool.not_eq_true, Option.not_isSome,
        Option.isNone_iff_eq_none]
      use k
      simp [appendInr]
      by_cases hk : k ∈ l2.withUniqueDualInOther l
      exact Or.inr hk
      have hk' := h.mpr hk
      simp_all only [not_false_eq_true, and_self, mem_withInDualOther_iff_isSome, Bool.not_eq_true,
        Option.not_isSome, Option.isNone_iff_eq_none, or_false]
    · intro h
      simp only [Finset.mem_map, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
        mem_withInDualOther_iff_isSome, Bool.not_eq_true, Option.not_isSome,
        Option.isNone_iff_eq_none] at h
      cases' h with h h
      · obtain ⟨j, hj⟩ := h
        simp only [appendInl, Function.Embedding.coeFn_mk, Function.comp_apply,
          EmbeddingLike.apply_eq_iff_eq, and_false] at hj
      · obtain ⟨j, hj⟩ := h
        have hjk : j = k := by
          simp only [appendInr, Function.Embedding.coeFn_mk, Function.comp_apply,
            EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq] at hj
          exact hj.2
        subst hjk
        have hj1 := hj.1
        cases' hj1 with hj1 hj1
        · simp_all only [and_self, true_or, true_and, mem_withInDualOther_iff_isSome,
          Option.isSome_none, Bool.false_eq_true, not_false_eq_true, true_iff]
          by_contra hn
          have h' := l2.mem_withDualInOther_of_withUniqueDualInOther l ⟨j, hn⟩
          simp_all only [mem_withInDualOther_iff_isSome, Option.isSome_none, Bool.false_eq_true]
        · simp_all only [or_true, true_and, mem_withInDualOther_iff_isSome,
          mem_withUniqueDualInOther_isSome, not_true_eq_false, and_false]

lemma append_withUniqueDual_disjSum : (l ++ l2).withUniqueDual =
    Equiv.finsetCongr appendEquiv
    (((l.withUniqueDual ∩ (l.withDualInOther l2)ᶜ) ∪ l.withUniqueDualInOther l2).disjSum
     ((l2.withUniqueDual ∩ (l2.withDualInOther l)ᶜ) ∪ l2.withUniqueDualInOther l)) := by
  rw [← Equiv.symm_apply_eq]
  simp only [Equiv.finsetCongr_symm, append_withUniqueDual, Equiv.finsetCongr_apply]
  rw [Finset.map_union]
  rw [Finset.map_map, Finset.map_map]
  ext1 a
  cases a with
  | inl val => simp
  | inr val_1 => simp

/-!

## Properties of getDualInOther?, withUniqueDualInOther and appendInOther

-/



lemma mem_append_withUniqueDualInOther_symm (i : Fin l.length) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDualInOther l3 ↔
    appendEquiv (Sum.inr i) ∈ (l2 ++ l).withUniqueDualInOther l3 := by
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_eq_none_append_inl_iff, getDualInOther?_append_of_inl, AreDualInOther.append_of_inl,
    true_and, getDual?_eq_none_append_inr_iff, getDualInOther?_append_of_inr,
    AreDualInOther.append_of_inr]

@[simp]
lemma withUniqueDualInOther_append_not_isSome_snd_of_isSome_fst (i : Fin l.length)
    (h1 : i ∈ l.withUniqueDualInOther (l2 ++ l3)) (h2 : (l.getDualInOther? l2 i).isSome) :
    (l.getDualInOther? l3 i) = none := by
  by_contra hn
  simp only [getDualInOther?] at h2 hn
  rw [← @Option.not_isSome_iff_eq_none, not_not] at hn
  rw [Fin.isSome_find_iff] at h2 hn
  obtain ⟨j2, hj2⟩ := h2
  obtain ⟨j3, hj3⟩ := hn
  have h1' : l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inl j2)) :=
    (AreDualInOther.of_append_inl i j2).mpr hj2
  have h2 : l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inr j3)) :=
    (AreDualInOther.of_append_inr i j3).mpr hj3
  have h3 := l.eq_of_areDualInOther_withUniqueDualInOther (l2 ++ l3) ⟨i, h1⟩ h1' h2
  simp only [EmbeddingLike.apply_eq_iff_eq] at h3

@[simp]
lemma withUniqueDualInOther_append_not_isSome_fst_of_isSome_snd (i : Fin l.length)
    (h1 : i ∈ l.withUniqueDualInOther (l2 ++ l3)) (h2 : (l.getDualInOther? l3 i).isSome) :
    (l.getDualInOther? l2 i) = none := by
  by_contra hn
  simp only [getDualInOther?] at h2 hn
  rw [← @Option.not_isSome_iff_eq_none, not_not] at hn
  rw [Fin.isSome_find_iff] at h2 hn
  obtain ⟨j2, hj2⟩ := h2
  obtain ⟨j3, hj3⟩ := hn
  have h1' : l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inr j2)) :=
    (AreDualInOther.of_append_inr i j2).mpr hj2
  have h2 : l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inl j3)) :=
    (AreDualInOther.of_append_inl i j3).mpr hj3
  have h3 := l.eq_of_areDualInOther_withUniqueDualInOther (l2 ++ l3) ⟨i, h1⟩ h1' h2
  simp only [EmbeddingLike.apply_eq_iff_eq] at h3

@[simp]
lemma withUniqueDualInOther_append_isSome_snd_of_not_isSome_fst (i : Fin l.length)
    (h1 : i ∈ l.withUniqueDualInOther (l2 ++ l3)) (h2 : ¬ (l.getDualInOther? l2 i).isSome) :
    (l.getDualInOther? l3 i).isSome := by
  by_contra hn
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, getDualInOther?_isSome_of_append_iff,
    Finset.mem_filter, Finset.mem_univ, true_and] at h1
  simp_all only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none, Option.isSome_none,
    Bool.false_eq_true, or_self, false_and, and_false]

lemma withUniqueDualInOther_append_isSome_fst_iff_not_isSome_snd (i : Fin l.length)
    (h1 : i ∈ l.withUniqueDualInOther (l2 ++ l3)) :
    (l.getDualInOther? l2 i).isSome ↔ (l.getDualInOther? l3 i) = none := by
  by_cases hs : (l.getDualInOther? l2 i).isSome
  simp [hs, h1]
  exact l.withUniqueDualInOther_append_not_isSome_snd_of_isSome_fst l2 l3 i h1 hs
  simp [hs]
  rw [← @Option.not_isSome_iff_eq_none, not_not]
  exact withUniqueDualInOther_append_isSome_snd_of_not_isSome_fst l l2 l3 i h1 hs

lemma getDualInOther?_append_symm_of_withUniqueDual_of_inl (i : Fin l.length)
    (k : Fin l2.length) (h : i ∈ l.withUniqueDualInOther (l2 ++ l3)) :
    l.getDualInOther? (l2 ++ l3) i = some (appendEquiv (Sum.inl k))
    ↔ l.getDualInOther? (l3 ++ l2) i  = some (appendEquiv (Sum.inr k)) := by
  have h := l.withUniqueDualInOther_append_isSome_fst_iff_not_isSome_snd l2 l3 i h
  by_cases hs : (l.getDualInOther? l2 i).isSome
  <;>  by_cases ho : (l.getDualInOther? l3 i).isSome
  <;> simp_all [hs]

lemma getDualInOther?_append_symm_of_withUniqueDual_of_inr (i : Fin l.length)
    (k : Fin l3.length) (h : i ∈ l.withUniqueDualInOther (l2 ++ l3)) :
    l.getDualInOther? (l2 ++ l3) i = some (appendEquiv (Sum.inr k))
    ↔ l.getDualInOther? (l3 ++ l2) i  = some (appendEquiv (Sum.inl k)) := by
  have h := l.withUniqueDualInOther_append_isSome_fst_iff_not_isSome_snd l2 l3 i h
  by_cases hs : (l.getDualInOther? l2 i).isSome
  <;>  by_cases ho : (l.getDualInOther? l3 i).isSome
  <;> simp_all [hs]


lemma mem_withUniqueDualInOther_symm' (i : Fin l.length)
    (h :  i ∈ l.withUniqueDualInOther (l2 ++ l3)):
    i ∈ l.withUniqueDualInOther (l3 ++ l2) := by
  have h' := h
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true,
    Option.not_isSome, Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome,
    getDualInOther?_isSome_of_append_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    implies_true, and_self, eq_getDualInOther?_get_of_withUniqueDualInOther_iff,
    getDualInOther?_areDualInOther_get] at h ⊢
  apply And.intro h.1
  have hc := l.withUniqueDualInOther_append_isSome_fst_iff_not_isSome_snd l2 l3 i h'
  by_cases h1 : (l.getDualInOther? l2 i).isSome <;>
  by_cases h2 : (l.getDualInOther? l3 i).isSome
  · simp only [h1, h2, not_true_eq_false, imp_false] at hc
    rw [← @Option.not_isSome_iff_eq_none]  at hc
    simp [h2] at hc
  · simp only [h1, or_true, true_and]
    intro j
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp only [AreDualInOther.of_append_inl]
      have hk'' := h.2.2 (appendEquiv (Sum.inr k))
      simp at hk''
      exact fun h'' => ((getDualInOther?_append_symm_of_withUniqueDual_of_inr l l2 l3 i k h').mp
        (hk'' h'').symm).symm
    | Sum.inr k =>
      simp only [AreDualInOther.of_append_inr]
      have hk'' := h.2.2 (appendEquiv (Sum.inl k))
      simp at hk''
      exact fun h'' => ((getDualInOther?_append_symm_of_withUniqueDual_of_inl l l2 l3 i k h').mp
        (hk'' h'').symm).symm
  · simp only [h2, true_or, Option.some.injEq, true_and]
    intro j
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp only [AreDualInOther.of_append_inl]
      have hk'' := h.2.2 (appendEquiv (Sum.inr k))
      simp at hk''
      exact fun h'' => ((getDualInOther?_append_symm_of_withUniqueDual_of_inr l l2 l3 i k h').mp
        (hk'' h'').symm).symm
    | Sum.inr k =>
      simp only [AreDualInOther.of_append_inr]
      have hk'' := h.2.2 (appendEquiv (Sum.inl k))
      simp only [AreDualInOther.of_append_inl] at hk''
      exact fun h'' => ((getDualInOther?_append_symm_of_withUniqueDual_of_inl l l2 l3 i k h').mp
        (hk'' h'').symm).symm
  · simp only [h1, Bool.false_eq_true, false_iff] at hc
    simp_all only [Bool.false_eq_true, or_self, eq_getDualInOther?_get_of_withUniqueDualInOther_iff,
      Option.some_get, implies_true, and_true, and_false]

lemma mem_withUniqueDualInOther_symm (i : Fin l.length) :
    i ∈ l.withUniqueDualInOther (l2 ++ l3) ↔ i ∈ l.withUniqueDualInOther (l3 ++ l2) :=
  Iff.intro (l.mem_withUniqueDualInOther_symm' l2 l3 i) (l.mem_withUniqueDualInOther_symm' l3 l2 i)


/-!

## The equivalence defined by getDual?

-/

/-- An equivalence from `l.withUniqueDual` to itself obtained by taking the dual index. -/
def getDualEquiv : l.withUniqueDual ≃ l.withUniqueDual where
  toFun x := ⟨(l.getDual? x).get (l.mem_withUniqueDual_isSome x.1 x.2), by
    simp only [Finset.coe_mem, getDual?_get_of_mem_withUnique_mem]⟩
  invFun x := ⟨(l.getDual? x).get (l.mem_withUniqueDual_isSome x.1 x.2), by simp⟩
  left_inv x := SetCoe.ext (by
    simp only [Finset.coe_mem, getDual?_getDual?_get_of_withUniqueDual, Option.get_some])
  right_inv x := SetCoe.ext (by
    simp only [Finset.coe_mem, getDual?_getDual?_get_of_withUniqueDual, Option.get_some])

@[simp]
lemma getDualEquiv_involutive : Function.Involutive l.getDualEquiv := by
  intro x
  exact (Equiv.apply_eq_iff_eq_symm_apply l.getDualEquiv).mpr rfl

/-!

## Equivalence for withUniqueDualInOther

-/

/-- An equivalence from `l.withUniqueDualInOther l2` to `l2.withUniqueDualInOther l`
  obtained by taking the dual index. -/
def getDualInOtherEquiv : l.withUniqueDualInOther l2 ≃ l2.withUniqueDualInOther l where
  toFun x := ⟨(l.getDualInOther? l2 x).get (l.mem_withUniqueDualInOther_isSome l2 x.1 x.2),
    by simp⟩
  invFun x := ⟨(l2.getDualInOther? l x).get (l2.mem_withUniqueDualInOther_isSome l x.1 x.2),
    by simp⟩
  left_inv x := SetCoe.ext (by simp)
  right_inv x := SetCoe.ext (by simp)

@[simp]
lemma getDualInOtherEquiv_self_refl : l.getDualInOtherEquiv l = Equiv.refl _ := by
  apply Equiv.ext
  intro x
  simp [getDualInOtherEquiv]


end IndexList

end IndexNotation