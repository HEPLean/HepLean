/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.CountId
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
/-!

# Equivalences between finsets.

-/

namespace IndexNotation

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

/-!

## withoutDualEquiv
-/

/-- An equivalence from `Fin l.withoutDual.card` to `l.withoutDual` determined by
  the order on `l.withoutDual` inherted from `Fin`. -/
def withoutDualEquiv : Fin l.withoutDual.card ≃ l.withoutDual :=
  (Finset.orderIsoOfFin l.withoutDual (by rfl)).toEquiv

lemma list_ofFn_withoutDualEquiv_eq_sort :
    List.ofFn (Subtype.val ∘ l.withoutDualEquiv) = l.withoutDual.sort (fun i j => i ≤ j) := by
  rw [@List.ext_get_iff]
  refine And.intro ?_ (fun n h1 h2 => ?_)
  · simp only [List.length_ofFn, Finset.length_sort]
  · simp only [List.get_eq_getElem, List.getElem_ofFn, Function.comp_apply]
    rfl

/-- An equivalence splitting the indices of an index list `l` into those indices
  which have a dual in `l` and those which do not have a dual in `l`. -/
def dualEquiv : l.withDual ⊕ Fin l.withoutDual.card ≃ Fin l.length :=
  (Equiv.sumCongr (Equiv.refl _) l.withoutDualEquiv).trans <|
  (Equiv.Finset.union _ _ l.withDual_disjoint_withoutDual).trans <|
  Equiv.subtypeUnivEquiv (by simp [withDual_union_withoutDual])

/-!

## getDualEquiv

-/

/-- An equivalence from `l.withUniqueDual` to itself obtained by taking the dual index. -/
def getDualEquiv : l.withUniqueDual ≃ l.withUniqueDual where
  toFun x := ⟨(l.getDual? x).get (l.mem_withUniqueDual_isSome x.1 x.2), by
    rw [mem_withUniqueDual_iff_countId_eq_two]
    simpa using l.countId_eq_two_of_mem_withUniqueDual x.1 x.2⟩
  invFun x := ⟨(l.getDual? x).get (l.mem_withUniqueDual_isSome x.1 x.2), by
    rw [mem_withUniqueDual_iff_countId_eq_two]
    simpa using l.countId_eq_two_of_mem_withUniqueDual x.1 x.2⟩
  left_inv x := SetCoe.ext <| by
    let d := (l.getDual? x).get (l.mem_withUniqueDual_isSome x.1 x.2)
    have h1 : l.countId (l.val.get d) = 2 := by
      simpa [d] using l.countId_eq_two_of_mem_withUniqueDual x.1 x.2
    have h2 : ((List.finRange l.length).filter (fun j => l.AreDualInSelf d j)).length = 1 := by
      rw [countId_get, List.countP_eq_length_filter] at h1
      omega
    obtain ⟨a, ha⟩ := List.length_eq_one.mp h2
    trans a
    · rw [← List.mem_singleton, ← ha]
      simp [d]
    · symm
      rw [← List.mem_singleton, ← ha]
      simp [d]
  right_inv x := SetCoe.ext <| by
    let d := (l.getDual? x).get (l.mem_withUniqueDual_isSome x.1 x.2)
    have h1 : l.countId (l.val.get d) = 2 := by
      simpa [d] using l.countId_eq_two_of_mem_withUniqueDual x.1 x.2
    have h2 : ((List.finRange l.length).filter (fun j => l.AreDualInSelf d j)).length = 1 := by
      rw [countId_get, List.countP_eq_length_filter] at h1
      omega
    obtain ⟨a, ha⟩ := List.length_eq_one.mp h2
    trans a
    · rw [← List.mem_singleton, ← ha]
      simp [d]
    · symm
      rw [← List.mem_singleton, ← ha]
      simp [d]

@[simp]
lemma getDual?_getDualEquiv (i : l.withUniqueDual) : l.getDual? (l.getDualEquiv i) = i := by
  have h1 := (Equiv.apply_symm_apply l.getDualEquiv i).symm
  nth_rewrite 2 [h1]
  nth_rewrite 2 [getDualEquiv]
  simp
  rfl

/-- An equivalence from `l.withUniqueDualInOther l2 ` to
  `l2.withUniqueDualInOther l` obtained by taking the dual index. -/
def getDualInOtherEquiv : l.withUniqueDualInOther l2 ≃ l2.withUniqueDualInOther l where
  toFun x := ⟨(l.getDualInOther? l2 x).get (l.mem_withUniqueDualInOther_isSome l2 x.1 x.2), by
    rw [mem_withUniqueDualInOther_iff_countId_eq_one]
    simpa using And.comm.mpr (l.countId_eq_one_of_mem_withUniqueDualInOther l2 x.1 x.2)⟩
  invFun x := ⟨(l2.getDualInOther? l x).get (l2.mem_withUniqueDualInOther_isSome l x.1 x.2), by
    rw [mem_withUniqueDualInOther_iff_countId_eq_one]
    simpa using And.comm.mpr (l2.countId_eq_one_of_mem_withUniqueDualInOther l x.1 x.2)⟩
  left_inv x := SetCoe.ext <| by
    let d := (l.getDualInOther? l2 x).get (l.mem_withUniqueDualInOther_isSome l2 x.1 x.2)
    have h1 : l.countId (l2.val.get d) = 1 := by
      simpa [d] using (l.countId_eq_one_of_mem_withUniqueDualInOther l2 x.1 x.2).1
    have h2 : ((List.finRange l.length).filter (fun j => l2.AreDualInOther l d j)).length = 1 := by
      rw [countId_get_other, List.countP_eq_length_filter] at h1
      omega
    obtain ⟨a, ha⟩ := List.length_eq_one.mp h2
    trans a
    · rw [← List.mem_singleton, ← ha]
      simp [d]
    · symm
      rw [← List.mem_singleton, ← ha]
      simp [d]
  right_inv x := SetCoe.ext <| by
    let d := (l2.getDualInOther? l x).get (l2.mem_withUniqueDualInOther_isSome l x.1 x.2)
    have h1 : l2.countId (l.val.get d) = 1 := by
      simpa [d] using (l2.countId_eq_one_of_mem_withUniqueDualInOther l x.1 x.2).1
    have h2 : ((List.finRange l2.length).filter (fun j => l.AreDualInOther l2 d j)).length = 1 := by
      rw [countId_get_other, List.countP_eq_length_filter] at h1
      omega
    obtain ⟨a, ha⟩ := List.length_eq_one.mp h2
    trans a
    · rw [← List.mem_singleton, ← ha]
      simp [d]
    · symm
      rw [← List.mem_singleton, ← ha]
      simp [d]

@[simp]
lemma getDualInOtherEquiv_self_refl : l.getDualInOtherEquiv l = Equiv.refl _ := by
  apply Equiv.ext
  intro x
  simp [getDualInOtherEquiv]
  apply Subtype.eq
  simp only
  have hx2 := x.2
  simp [withUniqueDualInOther] at hx2
  apply Option.some_injective
  rw [hx2.2 x.1 (by simp [AreDualInOther])]
  simp

@[simp]
lemma getDualInOtherEquiv_symm : (l.getDualInOtherEquiv l2).symm = l2.getDualInOtherEquiv l := by
  rfl

/-- An equivalence casting `withUniqueDualInOther` based on an equality of the left index list. -/
def withUniqueDualCastLeft (h : l = l3) :
    l.withUniqueDualInOther l2 ≃ l3.withUniqueDualInOther l2 where
  toFun x := ⟨Fin.cast (by rw [h]) x.1, by subst h; exact x.prop⟩
  invFun x := ⟨Fin.cast (by rw [h]) x.1, by subst h; exact x.prop⟩
  left_inv x := SetCoe.ext rfl
  right_inv x := SetCoe.ext rfl

/-- An equivalence casting `withUniqueDualInOther` based on an equality of the right index list. -/
def withUniqueDualCastRight (h : l2 = l3) :
    l.withUniqueDualInOther l2 ≃ l.withUniqueDualInOther l3 where
  toFun x := ⟨x.1, by subst h; exact x.prop⟩
  invFun x := ⟨x.1, by subst h; exact x.prop⟩
  left_inv x := SetCoe.ext rfl
  right_inv x := SetCoe.ext rfl

/-- An equivalence casting `withUniqueDualInOther` based on an equality of both index lists. -/
def withUniqueDualCast {l1 l2 l1' l2' : IndexList X} (h : l1 = l1') (h2 : l2 = l2') :
    l1.withUniqueDualInOther l2 ≃ l1'.withUniqueDualInOther l2' where
  toFun x := ⟨Fin.cast (by rw [h]) x.1, by subst h h2; exact x.prop⟩
  invFun x := ⟨Fin.cast (by rw [h]) x.1, by subst h h2; exact x.prop⟩
  left_inv x := SetCoe.ext rfl
  right_inv x := SetCoe.ext rfl

lemma getDualInOtherEquiv_cast_left (h : l = l3) :
    l.getDualInOtherEquiv l2 = ((withUniqueDualCastLeft l l2 l3 h).trans
    (l3.getDualInOtherEquiv l2)).trans (withUniqueDualCastRight l2 l l3 h).symm := by
  subst h
  rfl

lemma getDualInOtherEquiv_cast_right (h : l2 = l3) :
    l.getDualInOtherEquiv l2 = ((withUniqueDualCastRight l l2 l3 h).trans
    (l.getDualInOtherEquiv l3)).trans (withUniqueDualCastLeft l2 l l3 h).symm := by
  subst h
  rfl

lemma getDualInOtherEquiv_cast {l1 l2 l1' l2' : IndexList X} (h : l1 = l1') (h2 : l2 = l2') :
    l1.getDualInOtherEquiv l2 = ((withUniqueDualCast h h2).trans
    (l1'.getDualInOtherEquiv l2')).trans (withUniqueDualCast h2 h).symm := by
  subst h h2
  rfl

/-!

## Equivalences involving `withUniqueDualLT` and `withUniqueDualGT`.

-/

/-! TODO: Replace with a mathlib lemma. -/
lemma option_not_lt (i j : Option (Fin l.length)) : i < j → i ≠ j → ¬ j < i := by
  match i, j with
  | none, none =>
    exact fun a _ _ => a
  | none, some k =>
    exact fun _ _ a => a
  | some i, none =>
    exact fun h _ _ => h
  | some i, some j =>
    intro h h'
    simp_all
    change i < j at h
    change ¬ j < i
    exact Fin.lt_asymm h

/-! TODO: Replace with a mathlib lemma. -/
lemma lt_option_of_not (i j : Option (Fin l.length)) : ¬ j < i → i ≠ j → i < j := by
  match i, j with
  | none, none =>
    exact fun a b => a (a (a (b rfl)))
  | none, some k =>
    exact fun _ _ => trivial
  | some i, none =>
    exact fun a _ => a trivial
  | some i, some j =>
    intro h h'
    simp_all
    change ¬ j < i at h
    change i < j
    omega

/-- The equivalence between `l.withUniqueDualLT` and `l.withUniqueDualGT` obtained by
  taking an index to its dual. -/
def withUniqueDualLTEquivGT : l.withUniqueDualLT ≃ l.withUniqueDualGT where
  toFun i := ⟨l.getDualEquiv ⟨i, l.mem_withUniqueDual_of_mem_withUniqueDualLt i i.2⟩, by
    have hi := i.2
    simp only [withUniqueDualGT, Finset.mem_filter, Finset.coe_mem, true_and]
    simp only [withUniqueDualLT, Finset.mem_filter] at hi
    apply option_not_lt
    · rw [getDual?_getDualEquiv]
      simpa only [getDualEquiv, Equiv.coe_fn_mk, Option.some_get] using hi.2
    · exact getDual?_neq_self l _⟩
  invFun i := ⟨l.getDualEquiv.symm ⟨i, l.mem_withUniqueDual_of_mem_withUniqueDualGt i i.2⟩, by
    have hi := i.2
    simp only [withUniqueDualLT, Finset.mem_filter, Finset.coe_mem, true_and, gt_iff_lt]
    simp only [withUniqueDualGT, Finset.mem_filter] at hi
    apply lt_option_of_not
    · erw [getDual?_getDualEquiv]
      simpa [getDualEquiv] using hi.2
    · symm
      exact getDual?_neq_self l _⟩
  left_inv x := SetCoe.ext <| by
    simp
  right_inv x := SetCoe.ext <| by
    simp

/-- An equivalence from `l.withUniqueDualLT ⊕ l.withUniqueDualLT` to `l.withUniqueDual`.
  The first `l.withUniqueDualLT` are taken to themselves, whilst the second copy are
  taken to their dual. -/
def withUniqueLTGTEquiv : l.withUniqueDualLT ⊕ l.withUniqueDualLT ≃ l.withUniqueDual := by
  apply (Equiv.sumCongr (Equiv.refl _) l.withUniqueDualLTEquivGT).trans
  apply (Equiv.Finset.union _ _ l.withUniqueDualLT_disjoint_withUniqueDualGT).trans
  apply (Equiv.subtypeEquivRight (by simp only [l.withUniqueDualLT_union_withUniqueDualGT,
    implies_true]))

end IndexList

end IndexNotation
