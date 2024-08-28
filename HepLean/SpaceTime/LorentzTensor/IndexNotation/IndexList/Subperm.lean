/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.CountId
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.Contraction
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
/-!

# Subperm for index lists.

-/

namespace IndexNotation

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

/-- We say a IndexList `l` is a subpermutation of `l2` there are no duals in `l`, and
  every element of `l` has a unique dual in `l2`. -/
def Subperm : Prop := l.withUniqueDualInOther l2 = Finset.univ

namespace Subperm

variable {l l2 l3 : IndexList X}

lemma iff_countId_fin : l.Subperm l2 ↔
    ∀ i, l.countId (l.val.get i) = 1 ∧ l2.countId (l.val.get i) = 1 := by
  refine Iff.intro (fun h i => ?_) (fun h => ?_)
  · have hi : i ∈ l.withUniqueDualInOther l2 := by
      rw [h]
      exact Finset.mem_univ i
    exact countId_eq_one_of_mem_withUniqueDualInOther l l2 i hi
  · rw [Subperm, Finset.eq_univ_iff_forall]
    exact fun x => mem_withUniqueDualInOther_of_countId_eq_one l l2 x (h x)

lemma iff_countId : l.Subperm l2 ↔
    ∀ I, l.countId I ≤ 1 ∧ (l.countId I = 1 → l2.countId I = 1) := by
  rw [iff_countId_fin]
  refine Iff.intro (fun h I => ?_) (fun h i => ?_)
  · by_cases h' : l.countId I = 0
    · simp_all
    · obtain ⟨I', hI'1, hI'2⟩ := l.countId_neq_zero_mem I h'
      rw [countId_congr _ hI'2, countId_congr _ hI'2]
      have hi' : l.val.indexOf I' < l.val.length := List.indexOf_lt_length.mpr hI'1
      have hIi' : I' = l.val.get ⟨l.val.indexOf I', hi'⟩ := (List.indexOf_get (hi')).symm
      have hi' := h ⟨l.val.indexOf I', hi'⟩
      rw [← hIi'] at hi'
      rw [hi'.1, hi'.2]
      simp
  · have hi := h (l.val.get i)
    have h1 : l.countId (l.val.get i) ≠ 0 := countId_index_neq_zero l i
    omega

lemma trans (h1 : l.Subperm l2) (h2 : l2.Subperm l3) : l.Subperm l3 := by
  rw [iff_countId] at *
  intro I
  have h1 := h1 I
  have h2 := h2 I
  omega

lemma fst_eq_contrIndexList (h : l.Subperm l2) : l.contrIndexList = l := by
  rw [iff_countId] at *
  apply ext
  simp [contrIndexList]
  intro I hI
  have h' : l.countId I ≠ 0 := by exact countId_mem l I hI
  have hI' := h I
  omega

lemma symm (h : l.Subperm l2) (hl : l.length = l2.length) : l2.Subperm l := by
  refine (Finset.card_eq_iff_eq_univ (l2.withUniqueDualInOther l)).mp ?_
  trans (Finset.map ⟨Subtype.val, Subtype.val_injective⟩ (Equiv.finsetCongr
    (l.getDualInOtherEquiv l2) Finset.univ)).card
  · apply congrArg
    simp [Finset.ext_iff]
  · trans l2.length
    · simp only [Finset.univ_eq_attach, Equiv.finsetCongr_apply, Finset.card_map,
        Finset.card_attach]
      rw [h, ← hl]
      exact Finset.card_fin l.length
    · exact Eq.symm (Finset.card_fin l2.length)

lemma contr_refl : l.contrIndexList.Subperm l.contrIndexList := by
  rw [iff_countId]
  intro I
  simp only [imp_self, and_true]
  exact countId_contrIndexList_le_one l I

end Subperm

end IndexList

end IndexNotation
