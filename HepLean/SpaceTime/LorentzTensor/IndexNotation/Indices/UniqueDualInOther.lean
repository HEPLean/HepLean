/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.DualInOther
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.Dual
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Unique Dual indices

-/

namespace IndexNotation


namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 : IndexList X)


/-!

## Has single in other.

-/

def withUniqueDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => i ∉ l.withDual ∧ i ∈ l.withDualInOther l2
     ∧ (∀ j, l.AreDualInOther l2 i j → j = l.getDualInOther? l2 i)) Finset.univ

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

def fromWithUniqueDualInOther (i : l.withUniqueDualInOther l2) : l.withDualInOther l2 :=
  ⟨i.1, l.mem_withDualInOther_of_withUniqueDualInOther l2 i⟩

instance : Coe (l.withUniqueDualInOther l2) (l.withDualInOther l2) where
  coe i := ⟨i.1, l.mem_withDualInOther_of_withUniqueDualInOther l2 i⟩

lemma all_dual_eq_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    ∀ j, l.AreDualInOther l2 i j → j = l.getDualInOther! l2 i := by
  have hi := i.2
  simp only [withUniqueDualInOther, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
    true_and] at hi
  intro j hj
  refine (Option.get_of_mem _ (hi.2.2.2 j hj).symm).symm

lemma eq_getDualInOther_of_withUniqueDual_iff (i : l.withUniqueDualInOther l2) (j : Fin l2.length) :
    l.AreDualInOther l2 i j ↔ j = l.getDualInOther! l2 i := by
  apply Iff.intro
  intro h
  exact l.all_dual_eq_of_withUniqueDualInOther l2 i j h
  intro h
  subst h
  exact areDualInOther_getDualInOther! l l2 i

@[simp]
lemma getDualInOther!_getDualInOther_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    l2.getDualInOther! l (l.getDualInOther l2 i) = i := by
  by_contra hn
  refine (l.not_mem_withDual_of_withUniqueDualInOther l2 i)
    (l.mem_withDual_iff_exists.mpr ⟨(l2.getDualInOther! l (l.getDualInOther l2 i)), ?_⟩ )
  simp [AreDualInSelf, hn]
  exact (fun a => hn (id (Eq.symm a)))

@[simp]
lemma getDualInOther_getDualInOther_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    l2.getDualInOther l (l.getDualInOther l2 i) = i :=
  SetCoe.ext (getDualInOther!_getDualInOther_of_withUniqueDualInOther l l2 i)

@[simp]
lemma getDualInOther?_getDualInOther!_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    l2.getDualInOther? l (l.getDualInOther! l2 i) = some i := by
  change l2.getDualInOther? l (l.getDualInOther l2 i) = some i
  rw [getDualInOther?_eq_some_getDualInOther!]
  simp

lemma getDualInOther_of_withUniqueDualInOther_not_mem_of_withDual (i : l.withUniqueDualInOther l2) :
    (l.getDualInOther l2 i).1 ∉ l2.withDual  := by
  rw [mem_withDual_iff_exists]
  simp
  intro j
  simp [AreDualInSelf]
  intro hj
  by_contra hn
  have hn' : l.AreDualInOther l2 i j  := by
    simp [AreDualInOther, hn, hj]
  rw [eq_getDualInOther_of_withUniqueDual_iff] at hn'
  simp_all
  simp only [getDualInOther_coe, not_true_eq_false] at hj

lemma getDualInOther_of_withUniqueDualInOther_mem (i : l.withUniqueDualInOther l2) :
    (l.getDualInOther l2 i).1 ∈ l2.withUniqueDualInOther l := by
  simp only [withUniqueDualInOther, Finset.mem_filter, Finset.mem_univ, true_and]
  apply And.intro (l.getDualInOther_of_withUniqueDualInOther_not_mem_of_withDual l2 i)
  apply And.intro
  exact Finset.coe_mem
    (l.getDualInOther l2 ⟨↑i, mem_withDualInOther_of_withUniqueDualInOther l l2 i⟩)
  intro j hj
  by_contra hn
  have h' : l.AreDualInSelf i j := by
    simp [AreDualInSelf, hn]
    simp_all [AreDualInOther, getDual]
    simp [getDualInOther_coe] at hn
    exact fun a => hn (id (Eq.symm a))
  have hi := l.not_mem_withDual_of_withUniqueDualInOther l2 i
  rw [mem_withDual_iff_exists] at hi
  simp_all

def getDualInOtherEquiv : l.withUniqueDualInOther l2 ≃ l2.withUniqueDualInOther l where
  toFun x := ⟨l.getDualInOther l2 x, l.getDualInOther_of_withUniqueDualInOther_mem l2 x⟩
  invFun x := ⟨l2.getDualInOther l x, l2.getDualInOther_of_withUniqueDualInOther_mem l x⟩
  left_inv x := SetCoe.ext (by simp)
  right_inv x := SetCoe.ext (by simp)


end IndexList

end IndexNotation
