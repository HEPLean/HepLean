/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.WithUniqueDual
import Mathlib.Algebra.Order.Ring.Nat
/-!

# withDuals equal to withUniqueDuals

-/

namespace IndexNotation

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)


/-!

## withDual equal to withUniqueDual

-/

lemma withUnqiueDual_eq_withDual_iff_unique_forall :
    l.withUniqueDual = l.withDual ↔
    ∀ (i : l.withDual) j, l.AreDualInSelf i j → j = l.getDual? i := by
  apply Iff.intro
  · intro h i j hj
    rw [@Finset.ext_iff] at h
    simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
      true_and, and_iff_left_iff_imp] at h
    refine h i ?_ j hj
    exact withDual_isSome l i
  · intro h
    apply Finset.ext
    intro i
    apply Iff.intro
    · exact fun hi => mem_withDual_of_mem_withUniqueDual l i hi
    · intro hi
      simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
        true_and]
      apply And.intro
      exact (mem_withDual_iff_isSome l i).mp hi
      intro j hj
      exact h ⟨i, hi⟩ j hj

lemma withUnqiueDual_eq_withDual_iff :
    l.withUniqueDual = l.withDual ↔
    ∀ i, (l.getDual? i).bind l.getDual? = Option.guard (fun i => i ∈ l.withDual) i := by
  apply Iff.intro
  · intro h i
    by_cases hi : i ∈ l.withDual
    · have hii : i ∈ l.withUniqueDual := by
        simp_all only
      change (l.getDual? i).bind l.getDual?  = _
      simp [hii]
      symm
      rw [Option.guard_eq_some]
      exact ⟨rfl, mem_withUniqueDual_isSome l i hii⟩
    · simp at hi
      simp [Option.guard, hi]
  · intro h
    rw [withUnqiueDual_eq_withDual_iff_unique_forall]
    intro i j hj
    rcases l.getDual?_of_areDualInSelf hj with hi | hi | hi
    · have hj' := h j
      rw [hi] at hj'
      simp at hj'
      rw [hj']
      symm
      rw [Option.guard_eq_some, hi]
      exact ⟨rfl, rfl⟩
    · exact hi.symm
    · have hj' := h j
      rw [hi] at hj'
      rw [h i] at hj'
      have hi : Option.guard (fun i => i ∈ l.withDual) ↑i = some i := by
         apply Option.guard_eq_some.mpr
         simp
      rw [hi] at hj'
      simp at hj'
      have hj'' := Option.guard_eq_some.mp hj'.symm
      have hj''' := hj''.1
      rw [hj'''] at hj
      simp at hj

lemma withUnqiueDual_eq_withDual_iff_list_apply :
    l.withUniqueDual = l.withDual ↔
    (Fin.list l.length).map (fun i => (l.getDual? i).bind l.getDual?) =
    (Fin.list l.length).map (fun i => Option.guard (fun i => i ∈ l.withDual) i) := by
  rw [withUnqiueDual_eq_withDual_iff]
  apply Iff.intro
  exact fun h => List.map_eq_map_iff.mpr fun a _ => h a
  intro h
  intro i
  simp only [List.map_inj_left] at h
  have h1 {n : ℕ} (m : Fin n) : m ∈ Fin.list n := by
      have h1' : (Fin.list n)[m] = m := Fin.getElem_list _ _
      exact h1' ▸ List.getElem_mem _ _ _
  exact h i (h1 i)

/-- A boolean which is true for an index list `l` if for every index in `l` with a dual,
  that dual is unique. -/
def withUnqiueDualEqWithDualBool : Bool :=
  if (Fin.list l.length).map (fun i => (l.getDual? i).bind l.getDual?) =
    (Fin.list l.length).map (fun i => Option.guard (fun i => i ∈ l.withDual) i) then
    true
  else
    false

lemma withUnqiueDual_eq_withDual_iff_list_apply_bool :
    l.withUniqueDual = l.withDual ↔ l.withUnqiueDualEqWithDualBool := by
  rw [withUnqiueDual_eq_withDual_iff_list_apply]
  apply Iff.intro
  intro h
  simp only [withUnqiueDualEqWithDualBool, h, mem_withDual_iff_isSome, ↓reduceIte]
  intro h
  simpa only [mem_withDual_iff_isSome, List.map_inj_left, withUnqiueDualEqWithDualBool,
    Bool.if_false_right, Bool.and_true, decide_eq_true_eq] using h

@[simp]
lemma withUnqiueDual_eq_withDual_of_empty (h : l.withDual = ∅) :
    l.withUniqueDual = l.withDual := by
  rw [h, Finset.eq_empty_iff_forall_not_mem]
  intro x
  by_contra hx
  have x' : l.withDual := ⟨x, l.mem_withDual_of_withUniqueDual ⟨x, hx⟩⟩
  have hx'  := x'.2
  simp [h] at hx'

/-!

## withUniqueDualInOther equal to withDualInOther append conditions

-/

lemma withUniqueDualInOther_eq_withDualInOther_append_of_symm'
    (h : (l ++ l2).withUniqueDualInOther l3 = (l ++ l2).withDualInOther l3) :
    (l2 ++ l).withUniqueDualInOther l3 = (l2 ++ l).withDualInOther l3  := by
  rw [Finset.ext_iff] at h ⊢
  intro j
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    rw [mem_append_withUniqueDualInOther_symm]
    simpa only [mem_withInDualOther_iff_isSome, getDualInOther?_append_of_inl,
      getDualInOther?_append_of_inr] using h (appendEquiv (Sum.inr k))
  | Sum.inr k =>
    rw [← mem_append_withUniqueDualInOther_symm]
    simpa only [mem_withInDualOther_iff_isSome, getDualInOther?_append_of_inr,
      getDualInOther?_append_of_inl] using h (appendEquiv (Sum.inl k))

lemma withUniqueDualInOther_eq_withDualInOther_append_of_symm :
    (l ++ l2).withUniqueDualInOther l3 = (l ++ l2).withDualInOther l3 ↔
    (l2 ++ l).withUniqueDualInOther l3 = (l2 ++ l).withDualInOther l3 := by
  apply Iff.intro
  exact l.withUniqueDualInOther_eq_withDualInOther_append_of_symm' l2 l3
  exact l2.withUniqueDualInOther_eq_withDualInOther_append_of_symm' l l3

lemma withUniqueDualInOther_eq_withDualInOther_of_append_symm'
    (h : l.withUniqueDualInOther (l2 ++ l3) = l.withDualInOther (l2 ++ l3)) :
    l.withUniqueDualInOther (l3 ++ l2) = l.withDualInOther (l3 ++ l2) := by
  rw [Finset.ext_iff] at h ⊢
  intro j
  rw [mem_withUniqueDualInOther_symm]
  rw [h j]
  simp only [mem_withInDualOther_iff_isSome, getDualInOther?_isSome_of_append_iff]
  exact Or.comm

lemma withUniqueDualInOther_eq_withDualInOther_of_append_symm :
    l.withUniqueDualInOther (l2 ++ l3) = l.withDualInOther (l2 ++ l3) ↔
    l.withUniqueDualInOther (l3 ++ l2) = l.withDualInOther (l3 ++ l2) := by
  apply Iff.intro
  exact l.withUniqueDualInOther_eq_withDualInOther_of_append_symm' l2 l3
  exact l.withUniqueDualInOther_eq_withDualInOther_of_append_symm' l3 l2


/-!

## withDual equal to withUniqueDual append conditions

-/


lemma append_withDual_eq_withUniqueDual_iff :
    (l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    ((l.withUniqueDual ∩ (l.withDualInOther l2)ᶜ) ∪ l.withUniqueDualInOther l2)
    = l.withDual ∪ l.withDualInOther l2
    ∧ (l2.withUniqueDual ∩ (l2.withDualInOther l)ᶜ) ∪ l2.withUniqueDualInOther l
    =  l2.withDual ∪ l2.withDualInOther l := by
  rw [append_withUniqueDual_disjSum, withDual_append_eq_disjSum]
  simp only [Equiv.finsetCongr_apply, Finset.map_inj]
  have h (s s' : Finset (Fin l.length)) (t t' : Finset (Fin l2.length)) :
      s.disjSum t = s'.disjSum t' ↔ s = s' ∧ t = t' := by
    simp [Finset.ext_iff]
  exact h _ _ _ _

lemma append_withDual_eq_withUniqueDual_symm :
    (l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    (l2 ++ l).withUniqueDual = (l2 ++ l).withDual := by
  rw [append_withDual_eq_withUniqueDual_iff, append_withDual_eq_withUniqueDual_iff]
  exact And.comm

@[simp]
lemma append_withDual_eq_withUniqueDual_inl (h : (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
    l.withUniqueDual = l.withDual := by
  rw [Finset.ext_iff]
  intro i
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  · exact mem_withDual_of_mem_withUniqueDual l i h'
  · have hn : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
      rw [h]
      simp_all
    refine l.mem_withUniqueDual_of_inl l2 i hn ?_
    exact (mem_withDual_iff_isSome l i).mp h'

@[simp]
lemma append_withDual_eq_withUniqueDual_inr (h : (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
    l2.withUniqueDual = l2.withDual := by
  rw [append_withDual_eq_withUniqueDual_symm] at h
  exact append_withDual_eq_withUniqueDual_inl l2 l h

@[simp]
lemma append_withDual_eq_withUniqueDual_withUniqueDualInOther_inl
    (h :  (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
    l.withUniqueDualInOther l2 = l.withDualInOther l2 := by
  rw [Finset.ext_iff]
  intro i
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  · simp only [mem_withInDualOther_iff_isSome, h', mem_withUniqueDualInOther_isSome]
  · have hn : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
      rw [h]
      simp_all only [mem_withInDualOther_iff_isSome, mem_withDual_iff_isSome,
        getDual?_isSome_append_inl_iff, or_true, mem_withUniqueDual_isSome]
    refine l.mem_withUniqueDualInOther_of_inl_withDualInOther l2 i hn ?_
    exact (mem_withInDualOther_iff_isSome l l2 i).mp h'

@[simp]
lemma append_withDual_eq_withUniqueDual_withUniqueDualInOther_inr
    (h :  (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
    l2.withUniqueDualInOther l = l2.withDualInOther l := by
  rw [append_withDual_eq_withUniqueDual_symm] at h
  exact append_withDual_eq_withUniqueDual_withUniqueDualInOther_inl l2 l h

lemma append_withDual_eq_withUniqueDual_iff' :
    (l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    l.withUniqueDual = l.withDual ∧ l2.withUniqueDual = l2.withDual
    ∧ l.withUniqueDualInOther l2 = l.withDualInOther l2 ∧
    l2.withUniqueDualInOther l = l2.withDualInOther l := by
  apply Iff.intro
  intro h
  exact ⟨append_withDual_eq_withUniqueDual_inl l l2 h, append_withDual_eq_withUniqueDual_inr l l2 h,
    append_withDual_eq_withUniqueDual_withUniqueDualInOther_inl l l2 h,
    append_withDual_eq_withUniqueDual_withUniqueDualInOther_inr l l2 h⟩
  intro h
  rw [append_withDual_eq_withUniqueDual_iff]
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  have h1 : l.withDual ∩ (l.withDualInOther l2)ᶜ = l.withDual := by
    rw [Finset.inter_eq_left]
    rw [Finset.subset_iff]
    rw [← h.1, ← h.2.2.1]
    intro i hi
    simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.compl_filter, not_and,
      not_forall, Classical.not_imp, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hn
    simp_all
  have h2 : l2.withDual ∩ (l2.withDualInOther l)ᶜ = l2.withDual := by
    rw [Finset.inter_eq_left]
    rw [Finset.subset_iff]
    rw [← h.2.1, ← h.2.2.2]
    intro i hi
    simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.compl_filter, not_and,
      not_forall, Classical.not_imp, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hn
    simp_all
  exact ⟨congrFun (congrArg Union.union h1) (l.withDualInOther l2),
    congrFun (congrArg Union.union h2) (l2.withDualInOther l)⟩

lemma append_withDual_eq_withUniqueDual_swap :
    (l ++ l2 ++ l3).withUniqueDual = (l ++ l2 ++ l3).withDual
    ↔ (l2 ++ l ++ l3).withUniqueDual = (l2 ++ l ++ l3).withDual := by
  rw [append_withDual_eq_withUniqueDual_iff']
  rw [append_withDual_eq_withUniqueDual_iff' (l2 ++ l) l3]
  rw [append_withDual_eq_withUniqueDual_symm]
  rw [withUniqueDualInOther_eq_withDualInOther_of_append_symm]
  rw [withUniqueDualInOther_eq_withDualInOther_append_of_symm]


end IndexList

end IndexNotation
