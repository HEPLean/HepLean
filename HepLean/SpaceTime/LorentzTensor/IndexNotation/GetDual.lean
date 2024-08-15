/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.AreDual
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Sort
/-!

# Get dual index

We define the functions `getDual?` and `getDualInOther?` which return the
  first dual index in an `IndexList`.

-/

namespace IndexNotation


namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 : IndexList X)


/-!

## The getDual? Function

-/

/-- Given an `i`, if a dual exists in the same list,
   outputs the first such dual, otherwise outputs `none`. -/
def getDual? (i : Fin l.length) : Option (Fin l.length) :=
  Fin.find (fun j => l.AreDualInSelf i j)


/-- Given an `i`, if a dual exists in the other list,
   outputs the first such dual, otherwise outputs `none`. -/
def getDualInOther? (i : Fin l.length) : Option (Fin l2.length) :=
  Fin.find (fun j => l.AreDualInOther l2 i j)


/-!

## Basic properties of getDual?

-/

lemma getDual?_isSome_iff_exists (i : Fin l.length) :
    (l.getDual? i).isSome ↔ ∃ j, l.AreDualInSelf i j := by
  rw [getDual?, Fin.isSome_find_iff]

lemma getDual?_of_areDualInSelf (h : l.AreDualInSelf i j) :
    l.getDual? j = i ∨ l.getDual? i = j ∨ l.getDual? j = l.getDual? i := by
  have h3 : (l.getDual? i).isSome := by
    simpa [getDual?, Fin.isSome_find_iff] using ⟨j, h⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h3
  rw [hk]
  rw [getDual?, Fin.find_eq_some_iff] at hk
  by_cases hik : i < k
  · apply Or.inl
    rw [getDual?, Fin.find_eq_some_iff]
    apply And.intro h.symm
    intro k' hk'
    by_cases hik' : i = k'
    · exact Fin.ge_of_eq (id (Eq.symm hik'))
    · have hik'' :  l.AreDualInSelf i k' := by
        simp [AreDualInSelf, hik']
        simp_all [AreDualInSelf]
      have hk'' := hk.2 k' hik''
      exact (lt_of_lt_of_le hik hk'').le
  · by_cases hjk : j ≤ k
    · apply Or.inr
      apply Or.inl
      have hj := hk.2 j h
      simp only [Option.some.injEq]
      exact Fin.le_antisymm hj hjk
    · apply Or.inr
      apply Or.inr
      rw [getDual?, Fin.find_eq_some_iff]
      apply And.intro
      · simp_all [AreDualInSelf]
        exact Fin.ne_of_gt hjk
      intro k' hk'
      by_cases hik' : i = k'
      subst hik'
      exact Lean.Omega.Fin.le_of_not_lt hik
      have hik'' :  l.AreDualInSelf i k' := by
        simp [AreDualInSelf, hik']
        simp_all [AreDualInSelf]
      exact hk.2 k' hik''

@[simp]
lemma getDual?_neq_self (i : Fin l.length) : ¬ l.getDual? i = some i := by
  intro h
  simp [getDual?] at h
  rw [Fin.find_eq_some_iff] at h
  simp [AreDualInSelf] at h

@[simp]
lemma getDual?_get_neq_self (i : Fin l.length) (h : (l.getDual? i).isSome) :
    ¬ (l.getDual? i).get h = i := by
  have h1 := l.getDual?_neq_self i
  by_contra hn
  have h' : l.getDual? i = some i := by
    nth_rewrite 2 [← hn]
    exact Option.eq_some_of_isSome h
  exact h1 h'

@[simp]
lemma getDual?_get_id (i : Fin l.length) (h : (l.getDual? i).isSome) :
    l.idMap ((l.getDual? i).get h) = l.idMap i := by
  have h1 : l.getDual? i = some ((l.getDual? i).get h) := Option.eq_some_of_isSome h
  nth_rewrite 1 [getDual?] at h1
  rw [Fin.find_eq_some_iff] at h1
  simp [AreDualInSelf] at h1
  exact h1.1.2.symm

@[simp]
lemma getDual?_get_areDualInSelf (i : Fin l.length) (h : (l.getDual? i).isSome) :
    l.AreDualInSelf ((l.getDual? i).get h) i := by
  simp [AreDualInSelf]

@[simp]
lemma getDual?_areDualInSelf_get (i : Fin l.length) (h : (l.getDual? i).isSome) :
    l.AreDualInSelf i ((l.getDual? i).get h):=
  AreDualInSelf.symm (getDual?_get_areDualInSelf l i h)

@[simp]
lemma getDual?_getDual?_get_isSome (i : Fin l.length) (h : (l.getDual? i).isSome) :
    (l.getDual? ((l.getDual? i).get h)).isSome := by
  rw [getDual?, Fin.isSome_find_iff]
  exact ⟨i, getDual?_get_areDualInSelf l i h⟩

/-!

## Basic properties of getDualInOther?

-/

lemma getDualInOther?_isSome_iff_exists (i : Fin l.length) :
    (l.getDualInOther? l2 i).isSome ↔ ∃ j, l.AreDualInOther l2 i j := by
  rw [getDualInOther?, Fin.isSome_find_iff]

@[simp]
lemma getDualInOther?_id (i : Fin l.length) (h : (l.getDualInOther? l2 i).isSome) :
    l2.idMap ((l.getDualInOther? l2 i).get h) = l.idMap i := by
  have h1 : l.getDualInOther? l2 i = some ((l.getDualInOther? l2 i).get h) :=
    Option.eq_some_of_isSome h
  nth_rewrite 1 [getDualInOther?] at h1
  rw [Fin.find_eq_some_iff] at h1
  simp [AreDualInOther] at h1
  exact h1.1.symm

@[simp]
lemma getDualInOther?_get_areDualInOther (i : Fin l.length) (h : (l.getDualInOther? l2 i).isSome) :
    l2.AreDualInOther l ((l.getDualInOther? l2 i).get h) i := by
  simp [AreDualInOther]

@[simp]
lemma getDualInOther?_areDualInOther_get (i : Fin l.length) (h : (l.getDualInOther? l2 i).isSome) :
    l.AreDualInOther l2 i ((l.getDualInOther? l2 i).get h) :=
  AreDualInOther.symm (getDualInOther?_get_areDualInOther l l2 i h)

@[simp]
lemma getDualInOther?_getDualInOther?_get_isSome (i : Fin l.length)
    (h : (l.getDualInOther? l2 i).isSome) :
    (l2.getDualInOther? l ((l.getDualInOther? l2 i).get h)).isSome := by
  rw [getDualInOther?, Fin.isSome_find_iff]
  exact ⟨i, getDualInOther?_get_areDualInOther l l2 i h⟩

@[simp]
lemma getDualInOther?_self_isSome (i : Fin l.length) :
    (l.getDualInOther? l i).isSome := by
  simp [getDualInOther?]
  rw [@Fin.isSome_find_iff]
  exact ⟨i, rfl⟩

/-!

## Append properties of getDual?

-/

@[simp]
lemma getDual?_isSome_append_inl_iff (i : Fin l.length) :
    ((l ++ l2).getDual? (appendEquiv (Sum.inl i))).isSome ↔
    (l.getDual? i).isSome ∨ (l.getDualInOther? l2 i).isSome := by
  rw [getDual?_isSome_iff_exists, getDual?_isSome_iff_exists, getDualInOther?_isSome_iff_exists]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨j, hj⟩ := h
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      exact Or.inl ⟨k, AreDualInSelf.append_inl_inl.mp hj⟩
    | Sum.inr k =>
      exact Or.inr ⟨k, by simpa only [AreDualInSelf.append_inl_inr] using hj⟩
  · cases' h with h h <;>
      obtain ⟨j, hj⟩ := h
    · exact ⟨appendEquiv (Sum.inl j), AreDualInSelf.append_inl_inl.mpr hj⟩
    · use appendEquiv (Sum.inr j)
      simpa only [AreDualInSelf.append_inl_inr] using hj

@[simp]
lemma getDual?_isSome_append_inr_iff (i : Fin l2.length) :
    ((l ++ l2).getDual? (appendEquiv (Sum.inr i))).isSome ↔
    (l2.getDual? i).isSome ∨ (l2.getDualInOther? l i).isSome  := by
  rw [getDual?_isSome_iff_exists, getDual?_isSome_iff_exists, getDualInOther?_isSome_iff_exists]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨j, hj⟩ := h
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      exact Or.inr ⟨k, by simpa using hj⟩
    | Sum.inr k =>
      exact Or.inl ⟨k, (AreDualInSelf.append_inr_inr l l2 i k).mp hj⟩
  · cases' h with h h <;>
      obtain ⟨j, hj⟩ := h
    · exact ⟨appendEquiv (Sum.inr j), (AreDualInSelf.append_inr_inr l l2 i j).mpr hj⟩
    · use appendEquiv (Sum.inl j)
      simpa only [AreDualInSelf.append_inr_inl] using hj

lemma getDual?_isSome_append_symm (i : Fin l.length) :
    ((l ++ l2).getDual? (appendEquiv (Sum.inl i))).isSome ↔
    ((l2 ++ l).getDual? (appendEquiv (Sum.inr i))).isSome := by
  simp

@[simp]
lemma getDual?_eq_none_append_inl_iff (i : Fin l.length) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = none ↔
    l.getDual? i = none ∧ l.getDualInOther? l2 i = none := by
  apply Iff.intro
  · intro h
    have h1 := (l.getDual?_isSome_append_inl_iff l2 i).mpr.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h
  · intro h
    have h1 := (l.getDual?_isSome_append_inl_iff l2 i).mp.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h

@[simp]
lemma getDual?_eq_none_append_inr_iff  (i : Fin l2.length) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = none ↔
    (l2.getDual? i = none ∧ l2.getDualInOther? l i = none) := by
  apply Iff.intro
  · intro h
    have h1 := (l.getDual?_isSome_append_inr_iff l2 i).mpr.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h
  · intro h
    have h1 := (l.getDual?_isSome_append_inr_iff l2 i).mp.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h

@[simp]
lemma getDual?_append_inl_of_getDual?_isSome (i : Fin l.length) (h : (l.getDual? i).isSome) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) =
    some (appendEquiv (Sum.inl ((l.getDual? i).get h))) := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inl_inl]
  apply And.intro (getDual?_get_areDualInSelf l i h).symm
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, ge_iff_le]
    rw [Fin.le_def]
    have h2 : l.getDual? i = some (((l.getDual? i).get h)) := Option.eq_some_of_isSome h
    nth_rewrite 1 [getDual?] at h2
    rw [Fin.find_eq_some_iff] at h2
    exact h2.2 k (AreDualInSelf.append_inl_inl.mp hj)
  | Sum.inr k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, finSumFinEquiv_apply_right, ge_iff_le]
    rw [Fin.le_def]
    simp only [length, append_val, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd]
    omega

@[simp]
lemma getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome (i : Fin l.length)
    (hi : (l.getDual? i).isNone) (h : (l.getDualInOther? l2 i).isSome) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = some
    (appendEquiv (Sum.inr ((l.getDualInOther? l2 i).get h)))  := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inl_inr]
  apply And.intro (getDualInOther?_areDualInOther_get l l2 i h)
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    rw [AreDualInSelf.append_inl_inl] at hj
    simp only [getDual?, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true,
      Option.not_isSome, Option.isNone_iff_eq_none, Fin.find_eq_none_iff] at hi
    exact False.elim (hi k hj)
  | Sum.inr k =>
    simp [appendEquiv]
    rw [Fin.le_def]
    have h1 : l.getDualInOther? l2 i = some (((l.getDualInOther? l2 i).get h)) :=
      Option.eq_some_of_isSome h
    nth_rewrite 1 [getDualInOther?] at h1
    rw [Fin.find_eq_some_iff] at h1
    simp only [length, append_val, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
      Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le, ge_iff_le]
    refine h1.2 k (by simpa using hj)

lemma getDual?_append_inl (i : Fin l.length) : (l ++ l2).getDual? (appendEquiv (Sum.inl i)) =
    Option.or (Option.map (appendEquiv ∘ Sum.inl) (l.getDual? i))
    (Option.map (appendEquiv ∘ Sum.inr) (l.getDualInOther? l2 i)) := by
  by_cases h : (l.getDual? i).isSome
  · simp_all
    rw [congrArg (Option.map (appendEquiv ∘ Sum.inl)) (Option.eq_some_of_isSome h)]
    rfl
  by_cases ho : (l.getDualInOther? l2 i).isSome
  · simp_all
    rw [congrArg (Option.map (appendEquiv ∘ Sum.inr)) (Option.eq_some_of_isSome ho)]
    rfl
  simp_all

@[simp]
lemma getDual?_append_inr_getDualInOther?_isSome (i : Fin l2.length)
    (h : (l2.getDualInOther? l i).isSome) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) =
    some (appendEquiv (Sum.inl ((l2.getDualInOther? l i).get h))) := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inr_inl]
  apply And.intro
  exact getDualInOther?_areDualInOther_get l2 l i h
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, ge_iff_le]
    rw [Fin.le_def]
    have h1 : l2.getDualInOther? l i = some (((l2.getDualInOther? l i).get h)) :=
      Option.eq_some_of_isSome h
    nth_rewrite 1 [getDualInOther?] at h1
    rw [Fin.find_eq_some_iff] at h1
    simp only [Fin.coe_cast, Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le, ge_iff_le]
    refine h1.2 k (by simpa using hj)
  | Sum.inr k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, finSumFinEquiv_apply_right, ge_iff_le]
    rw [Fin.le_def]
    simp only [length, append_val, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd]
    omega

@[simp]
lemma getDual?_inr_getDualInOther?_isNone_getDual?_isSome (i : Fin l2.length)
    (h : (l2.getDualInOther? l i).isNone) (hi : (l2.getDual? i).isSome) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = some
    (appendEquiv (Sum.inr ((l2.getDual? i).get hi))) := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inr_inr]
  apply And.intro
  exact getDual?_areDualInSelf_get l2 i hi
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp at hj
    simp only [getDualInOther?, Option.isNone_iff_eq_none, Fin.find_eq_none_iff] at h
    exact False.elim (h k hj)
  | Sum.inr k =>
    simp [appendEquiv, IndexList.length]
    rw [Fin.le_def]
    simp only [Fin.coe_cast, Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le]
    have h2 : l2.getDual? i = some ((l2.getDual? i).get hi) := Option.eq_some_of_isSome hi
    nth_rewrite 1 [getDual?] at h2
    rw [Fin.find_eq_some_iff] at h2
    simp only [AreDualInSelf.append_inr_inr] at hj
    exact h2.2 k hj

lemma getDual?_append_inr (i : Fin l2.length) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) =
    Option.or (Option.map (appendEquiv ∘ Sum.inl) (l2.getDualInOther? l i))
    (Option.map (appendEquiv ∘ Sum.inr) (l2.getDual? i)) := by
  by_cases h : (l2.getDualInOther? l i).isSome
  · simp_all
    rw [congrArg (Option.map (appendEquiv ∘ Sum.inl)) (Option.eq_some_of_isSome h)]
    rfl
  by_cases ho : (l2.getDual? i).isSome
  · simp_all
    rw [congrArg (Option.map (appendEquiv ∘ Sum.inr)) (Option.eq_some_of_isSome ho)]
    rfl
  simp_all

/-!

## Properties of getDualInOther? and append

-/
variable (l3 : IndexList X)

@[simp]
lemma getDualInOther?_append_of_inl (i : Fin l.length) :
    (l ++ l2).getDualInOther? l3 (appendEquiv (Sum.inl i)) = l.getDualInOther? l3 i := by
  simp [getDualInOther?]

@[simp]
lemma getDualInOther?_append_of_inr (i : Fin l2.length) :
    (l ++ l2).getDualInOther? l3 (appendEquiv (Sum.inr i)) = l2.getDualInOther? l3 i := by
  simp [getDualInOther?]

@[simp]
lemma getDualInOther?_isSome_of_append_iff (i : Fin l.length) :
    (l.getDualInOther? (l2 ++ l3) i).isSome ↔
    (l.getDualInOther? l2 i).isSome ∨ (l.getDualInOther? l3 i).isSome := by
  rw [getDualInOther?_isSome_iff_exists, getDualInOther?_isSome_iff_exists,
    getDualInOther?_isSome_iff_exists]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨j, hj⟩ := h
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      exact Or.inl ⟨k, by simpa using hj⟩
    | Sum.inr k =>
      exact Or.inr ⟨k, (AreDualInOther.of_append_inr i k).mp hj⟩
  · cases' h with h h <;>
      obtain ⟨j, hj⟩ := h
    · use appendEquiv (Sum.inl j)
      exact (AreDualInOther.of_append_inl i j).mpr hj
    · use appendEquiv (Sum.inr j)
      exact (AreDualInOther.of_append_inr i j).mpr hj

@[simp]
lemma getDualInOther?_eq_none_of_append_iff (i : Fin l.length) :
    (l.getDualInOther? (l2 ++ l3) i) = none ↔
    (l.getDualInOther? l2 i) = none ∧ (l.getDualInOther? l3 i) = none := by
  apply Iff.intro
  · intro h
    have h1 := (l.getDualInOther?_isSome_of_append_iff l2 l3 i).mpr.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h
  · intro h
    have h1 := (l.getDualInOther?_isSome_of_append_iff l2 l3 i).mp.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h

@[simp]
lemma getDualInOther?_of_append_of_isSome (i : Fin l.length)
    (hi : (l.getDualInOther? l2 i).isSome) : l.getDualInOther? (l2 ++ l3) i =
    some (appendEquiv (Sum.inl ((l.getDualInOther? l2 i).get hi))) := by
  rw [getDualInOther?, Fin.find_eq_some_iff, AreDualInOther.of_append_inl]
  apply And.intro
  exact getDualInOther?_areDualInOther_get l l2 i hi
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, ge_iff_le]
    rw [Fin.le_def]
    have h1 : l.getDualInOther? l2 i = some (((l.getDualInOther? l2 i).get hi)) :=
      Option.eq_some_of_isSome hi
    nth_rewrite 1 [getDualInOther?] at h1
    rw [Fin.find_eq_some_iff] at h1
    simp only [Fin.coe_cast, Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le, ge_iff_le]
    refine h1.2 k ((AreDualInOther.of_append_inl i k).mp hj)
  | Sum.inr k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, finSumFinEquiv_apply_right, ge_iff_le]
    rw [Fin.le_def]
    simp only [length, append_val, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd]
    omega

@[simp]
lemma getDualInOther?_of_append_of_isNone_isSome (i : Fin l.length)
    (hi : (l.getDualInOther? l2 i) = none) (h2 : (l.getDualInOther? l3 i).isSome) :
    l.getDualInOther? (l2 ++ l3) i =
    some (appendEquiv (Sum.inr ((l.getDualInOther? l3 i).get h2))) := by
  rw [getDualInOther?, Fin.find_eq_some_iff, AreDualInOther.of_append_inr]
  apply And.intro
  exact getDualInOther?_areDualInOther_get l l3 i h2
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp at hj
    simp only [getDualInOther?, Option.isNone_iff_eq_none, Fin.find_eq_none_iff] at hi
    exact False.elim (hi k hj)
  | Sum.inr k =>
    simp [appendEquiv, IndexList.length]
    rw [Fin.le_def]
    simp only [Fin.coe_cast, Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le]
    have h1 : l.getDualInOther? l3 i = some ((l.getDualInOther? l3 i).get h2) :=
      Option.eq_some_of_isSome h2
    nth_rewrite 1 [getDualInOther?] at h1
    rw [Fin.find_eq_some_iff] at h1
    simp only [AreDualInOther.of_append_inr] at hj
    exact h1.2 k hj

end IndexList

end IndexNotation
