/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Contraction
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Sort
/-!

# withDuals equal to withUniqueDuals

In a permissible list of indices every index which has a dual has a unique dual.
This corresponds to the condition that `l.withDual = l.withUniqueDual`.

We prove lemmas relating to this condition.

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
  refine Iff.intro (fun h i j hj => ?_) (fun h => ?_)
  · rw [@Finset.ext_iff] at h
    simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
      true_and, and_iff_left_iff_imp] at h
    refine h i ?_ j hj
    exact withDual_isSome l i
  · refine Finset.ext (fun i => ?_)
    refine Iff.intro (fun hi => mem_withDual_of_mem_withUniqueDual l i hi) (fun hi => ?_)
    · simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact And.intro ((mem_withDual_iff_isSome l i).mp hi) (fun j hj => h ⟨i, hi⟩ j hj)

lemma withUnqiueDual_eq_withDual_iff :
    l.withUniqueDual = l.withDual ↔
    ∀ i, (l.getDual? i).bind l.getDual? = Option.guard (fun i => i ∈ l.withDual) i := by
  apply Iff.intro
  · intro h i
    by_cases hi : i ∈ l.withDual
    · have hii : i ∈ l.withUniqueDual := by
        simp_all only
      change (l.getDual? i).bind l.getDual? = _
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
  refine Iff.intro (fun h => List.map_eq_map_iff.mpr fun a _ => h a) (fun h i => ?_)
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
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · simp only [withUnqiueDualEqWithDualBool, h, mem_withDual_iff_isSome, ↓reduceIte]
  · simpa only [mem_withDual_iff_isSome, List.map_inj_left, withUnqiueDualEqWithDualBool,
      Bool.if_false_right, Bool.and_true, decide_eq_true_eq] using h

@[simp]
lemma withUnqiueDual_eq_withDual_of_empty (h : l.withDual = ∅) :
    l.withUniqueDual = l.withDual := by
  rw [h, Finset.eq_empty_iff_forall_not_mem]
  intro x
  by_contra hx
  have x' : l.withDual := ⟨x, l.mem_withDual_of_withUniqueDual ⟨x, hx⟩⟩
  have hx' := x'.2
  simp [h] at hx'

lemma withUniqueDual_eq_withDual_iff_sort_eq :
    l.withUniqueDual = l.withDual ↔
    l.withUniqueDual.sort (fun i j => i ≤ j) = l.withDual.sort (fun i j => i ≤ j) := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [h]
  · have h1 := congrArg Multiset.ofList h
    rw [Finset.sort_eq, Finset.sort_eq] at h1
    exact Eq.symm ((fun {α} {s t} => Finset.val_inj.mp) (id (Eq.symm h1)))

/-!

# withUniqueDual equal to withDual and count conditions.

-/

lemma withUniqueDual_eq_withDual_iff_countId_leq_two :
    l.withUniqueDual = l.withDual ↔ ∀ i, l.countId (l.val.get i) ≤ 2 := by
  refine Iff.intro (fun h i => ?_) (fun h => ?_)
  · by_cases hi : i ∈ l.withDual
    · rw [← h] at hi
      rw [mem_withUniqueDual_iff_countId_eq_two] at hi
      rw [hi]
    · rw [mem_withDual_iff_countId_gt_one] at hi
      simp at hi
      exact Nat.le_succ_of_le hi
  · refine Finset.ext (fun i => ?_)
    rw [mem_withUniqueDual_iff_countId_eq_two, mem_withDual_iff_countId_gt_one]
    have hi := h i
    omega

lemma withUniqueDual_eq_withDual_iff_countId_leq_two' :
    l.withUniqueDual = l.withDual ↔ ∀ I, l.countId I ≤ 2 := by
  rw [withUniqueDual_eq_withDual_iff_countId_leq_two]
  refine Iff.intro (fun h I => ?_) (fun h i => h (l.val.get i))
  by_cases hI : l.countId I = 0
  · rw [hI]
    exact Nat.zero_le 2
  · obtain ⟨I', hI1', hI2'⟩ := countId_neq_zero_mem l I hI
    rw [countId_congr _ hI2']
    have hi : List.indexOf I' l.val < l.length := List.indexOf_lt_length.mpr hI1'
    have hI' : I' = l.val.get ⟨List.indexOf I' l.val, hi⟩ := (List.indexOf_get hi).symm
    rw [hI']
    exact h ⟨List.indexOf I' l.val, hi⟩


lemma withUniqueDual_eq_withDual_countId_cases (h : l.withUniqueDual = l.withDual)
    (i : Fin l.length) : l.countId (l.val.get i) = 0 ∨
    l.countId (l.val.get i) = 1 ∨ l.countId (l.val.get i) = 2 := by
  by_cases h0 : l.countId (l.val.get i)= 0
  · exact Or.inl h0
  · by_cases h1 : l.countId (l.val.get i) = 1
    · exact Or.inr (Or.inl h1)
    · have h2 : l.countId (l.val.get i) ≤ 2 := by
        rw [withUniqueDual_eq_withDual_iff_countId_leq_two] at h
        exact h i
      omega

section filterID

/-! TODO: Move this section. -/
lemma filter_id_of_countId_eq_zero {i : Fin l.length} (h1 : l.countId (l.val.get i) = 0) :
    l.val.filter (fun J => (l.val.get i).id = J.id) = [] := by
  rw [countId_eq_length_filter, List.length_eq_zero] at h1
  exact h1

lemma filter_id_of_countId_eq_zero' {I : Index X} (h1 : l.countId I = 0) :
    l.val.filter (fun J => I.id = J.id) = [] := by
  rw [countId_eq_length_filter, List.length_eq_zero] at h1
  exact h1

lemma filter_id_of_countId_eq_one {i : Fin l.length} (h1 : l.countId (l.val.get i) = 1) :
    l.val.filter (fun J => (l.val.get i).id = J.id) = [l.val.get i] := by
  rw [countId_eq_length_filter, List.length_eq_one] at h1
  obtain ⟨J, hJ⟩ := h1
  have hme : (l.val.get i) ∈ List.filter (fun J => decide ((l.val.get i).id = J.id)) l.val := by
    simp only [List.get_eq_getElem, List.mem_filter, decide_True, and_true]
    exact List.getElem_mem l.val (↑i) i.isLt
  rw [hJ] at hme
  simp only [List.get_eq_getElem, List.mem_singleton] at hme
  erw [hJ]
  simp only [List.get_eq_getElem, List.cons.injEq, and_true]
  exact id (Eq.symm hme)

lemma filter_id_of_countId_eq_one_mem {I : Index X} (hI : I ∈ l.val) (h : l.countId I = 1) :
    l.val.filter (fun J => I.id = J.id) = [I] := by
  rw [countId_eq_length_filter, List.length_eq_one] at h
  obtain ⟨J, hJ⟩ := h
  have hme : I ∈ List.filter (fun J => decide (I.id = J.id)) l.val := by
    simp only [List.mem_filter, decide_True, and_true]
    exact hI
  rw [hJ] at hme
  simp only [List.mem_singleton] at hme
  erw [hJ]
  simp only [List.cons.injEq, and_true]
  exact id (Eq.symm hme)

lemma filter_id_of_countId_eq_two {i : Fin l.length}
    (h : l.countId (l.val.get i) = 2) :
    l.val.filter (fun J => (l.val.get i).id = J.id) =
    [l.val.get i, l.val.get ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))] ∨
    l.val.filter (fun J => (l.val.get i).id = J.id) =
    [l.val.get ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)), l.val.get i] := by
  have hc := l.countId_eq_two_of_mem_withUniqueDual i
    ((mem_withUniqueDual_iff_countId_eq_two l i).mpr h)
  rw [countId_eq_length_filter] at hc
  by_cases hi : i < ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))
  · apply Or.inl
    symm
    apply List.Sublist.eq_of_length
    · have h1 : [l.val.get i, l.val.get
          ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))].filter
            (fun J => (l.val.get i).id = J.id) = [l.val.get i, l.val.get
          ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))] := by
        simp only [List.get_eq_getElem, decide_True, List.filter_cons_of_pos, List.cons.injEq,
          List.filter_eq_self, List.mem_singleton, decide_eq_true_eq, forall_eq, true_and]
        change l.idMap i = l.idMap ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))
        simp
      rw [← h1]
      refine List.Sublist.filter (fun (J : Index X) => ((l.val.get i).id = J.id)) ?_
      rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
      refine ⟨⟨⟨![i, (l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)], ?_⟩, ?_⟩, ?_⟩
      · refine List.nodup_ofFn.mp ?_
        simpa using Fin.ne_of_lt hi
      · intro a b
        fin_cases a, b
          <;> simp [hi]
        exact Fin.le_of_lt hi
      · intro a
        fin_cases a <;> rfl
    · rw [hc]
      simp
  · have hi' : ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)) < i := by
      have h1 := l.getDual?_get_areDualInSelf i (getDual?_isSome_of_countId_eq_two l h)
      simp only [AreDualInSelf] at h1
      have h2 := h1.1
      omega
    apply Or.inr
    symm
    apply List.Sublist.eq_of_length
    · have h1 : [l.val.get ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)),
        l.val.get i].filter (fun J => (l.val.get i).id = J.id) = [l.val.get
        ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)), l.val.get i,] := by
        simp only [List.get_eq_getElem, List.filter_eq_self, List.mem_cons, List.mem_singleton,
          decide_eq_true_eq, forall_eq_or_imp, forall_eq, and_true]
        apply And.intro
        · change l.idMap i = l.idMap ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))
          simp
        · simp only [List.not_mem_nil, false_implies, implies_true, and_self]
      rw [← h1]
      refine List.Sublist.filter (fun (J : Index X) => ((l.val.get i).id = J.id)) ?_
      rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
      refine ⟨⟨⟨![(l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h), i], ?_⟩, ?_⟩, ?_⟩
      · refine List.nodup_ofFn.mp ?_
        simp only [List.get_eq_getElem, List.length_singleton, Nat.succ_eq_add_one, Nat.reduceAdd,
          List.length_nil, List.ofFn_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
          Matrix.cons_val_fin_one, List.ofFn_zero, List.nodup_cons, List.mem_singleton,
          List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, and_true]
        exact Fin.ne_of_lt hi'
      · intro a b
        fin_cases a, b
          <;> simp [hi']
        exact Fin.le_of_lt hi'
      · intro a
        fin_cases a <;> rfl
    · rw [hc]
      simp

/-- Given an index `I` such that there is one index in `l` with the same `id` as `I`.
  This is that index. -/
def consDual {I : Index X} (hI : l.countId I = 1) : Index X :=
  (l.cons I).val.get (((l.cons I).getDual? ⟨0, by simp⟩).get
    ((l.cons I).getDual?_isSome_of_countId_eq_two (by simpa [countId] using hI)))

/-! TODO: Relate `consDual` to `getDualInOther?`. -/

@[simp]
lemma consDual_id {I : Index X} (hI : l.countId I = 1) :
    (l.consDual hI).id = I.id := by
  change (l.cons I).idMap ((((l.cons I).getDual? ⟨0, by simp⟩).get
      ((l.cons I).getDual?_isSome_of_countId_eq_two (by simpa [countId] using hI)))) = _
  simp only [cons, Fin.zero_eta, getDual?_get_id]
  simp only [idMap, List.get_eq_getElem, List.length_cons, Fin.val_zero, List.getElem_cons_zero]

@[simp]
lemma consDual_mem {I : Index X} (hI : l.countId I = 1) :
    l.consDual hI ∈ l.val := by
  let Di := (((l.cons I).getDual? ⟨0, by simp⟩).get (by
      rw [← zero_mem_withUniqueDual_of_cons_iff_countId_one] at hI; exact
        mem_withUniqueDual_isSome (l.cons I) ⟨0, _⟩ hI))
  have hDiz : Di ≠ ⟨0, by simp⟩ := by
    have hd : (l.cons I).AreDualInSelf ⟨0, by simp⟩ Di := by
      simp [Di]
      symm
      exact (l.cons I).getDual?_get_areDualInSelf ⟨0, by simp⟩ (by
        rw [← zero_mem_withUniqueDual_of_cons_iff_countId_one] at hI;
        exact mem_withUniqueDual_isSome (l.cons I) ⟨0, _⟩ hI)
    simp [AreDualInSelf] at hd
    have hd2 := hd.1
    exact fun a => hd2 (id (Eq.symm a))
  have Dim1 : (Di.1-1) + 1 = Di.1 := by
    have : Di.1 ≠ 0 := by
      rw [Fin.ne_iff_vne] at hDiz
      exact hDiz
    omega
  change (l.cons I).val.get Di ∈ l.val
  simp only [cons_val, List.get_eq_getElem, List.length_cons]
  have h1 : (I :: l.val).get ⟨Di.1, Di.isLt⟩ = (I :: l.val).get
      ⟨(Di.1-1) + 1, by rw [Dim1]; exact Di.isLt⟩ := by
    apply congrArg
    rw [Fin.ext_iff]
    exact id (Eq.symm Dim1)
  simp only [List.length_cons, cons_length, Fin.eta, List.get_eq_getElem,
    List.getElem_cons_succ] at h1
  rw [h1]
  exact List.getElem_mem l.val _ _

lemma consDual_filter {I : Index X} (hI : l.countId I = 1) :
    l.val.filter (fun J => I.id = J.id) = [l.consDual hI] := by
  have h1 : (l.val.filter (fun J => I.id = J.id)).length = 1 := by
    rw [← List.countP_eq_length_filter]
    exact hI
  rw [List.length_eq_one] at h1
  obtain ⟨a, ha⟩ := h1
  rw [ha]
  simp only [List.cons.injEq, and_true]
  have haI : l.consDual hI ∈ l.val.filter (fun J => I.id = J.id) := by
    simp
  rw [ha] at haI
  simp at haI
  exact haI.symm

lemma consDual_iff {I : Index X} (hI : l.countId I = 1)
    (I' : Index X) : I' = l.consDual hI ↔ I' ∈ l.val ∧ I'.id = I.id := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · subst h
    simp only [consDual_mem, consDual_id, and_self]
  · have hI' : I' ∈ l.val.filter (fun J => I.id = J.id) := by
      simp only [List.mem_filter, h, decide_True, and_self]
    rw [l.consDual_filter hI] at hI'
    simpa using hI'

lemma filter_of_constDual {I : Index X} (hI : l.countId I = 1) :
    (l.cons I).val.filter (fun J => (l.consDual hI).id = J.id) = [I, l.consDual hI] := by
  simp only [consDual_id, cons_val, decide_True, List.filter_cons_of_pos, List.cons.injEq, true_and]
  exact consDual_filter l hI

end filterID

lemma withUniqueDual_eq_withDual_iff_countId_mem_le_two :
    l.withUniqueDual = l.withDual ↔
    ∀ I (_ : I ∈ l.val), l.countId I ≤ 2 := by
  rw [withUniqueDual_eq_withDual_iff_countId_leq_two]
  refine Iff.intro (fun h I hI => ?_) (fun h i => ?_)
  · let i := l.val.indexOf I
    have hi : i < l.length := List.indexOf_lt_length.mpr hI
    have hIi : I = l.val.get ⟨i, hi⟩ := (List.indexOf_get hi).symm
    rw [hIi]
    exact h ⟨i, hi⟩
  · exact h (l.val.get i) (List.getElem_mem l.val (↑i) i.isLt)

lemma withUniqueDual_eq_withDual_iff_all_countId_le_two :
    l.withUniqueDual = l.withDual ↔
    l.val.all (fun I => l.countId I ≤ 2) := by
  rw [withUniqueDual_eq_withDual_iff_countId_mem_le_two]
  simp only [List.all_eq_true, decide_eq_true_eq]

/-!

## Relationship with cons

-/

lemma withUniqueDual_eq_withDual_cons_iff (I : Index X) (hl : l.withUniqueDual = l.withDual) :
    (l.cons I).withUniqueDual = (l.cons I).withDual ↔ l.countId I ≤ 1 := by
  rw [withUniqueDual_eq_withDual_iff_all_countId_le_two]
  simp only [cons_val, countId, List.all_cons, decide_True, List.countP_cons_of_pos,
    Nat.reduceLeDiff, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_iff_left_iff_imp]
  intro h I' hI'
  by_cases hII' : I'.id = I.id
  · rw [List.countP_cons_of_pos]
    · rw [hII']
      omega
    · simpa using hII'
  · rw [List.countP_cons_of_neg]
    · rw [withUniqueDual_eq_withDual_iff_countId_mem_le_two] at hl
      exact hl I' hI'
    · simpa using hII'

lemma withUniqueDual_eq_withDual_of_cons {I : Index X}
    (hl : (l.cons I).withUniqueDual = (l.cons I).withDual) :
    l.withUniqueDual = l.withDual := by
  rw [withUniqueDual_eq_withDual_iff_countId_mem_le_two] at hl ⊢
  intro I' hI'
  have hImem : I' ∈ (l.cons I).val := by
    simp [hI']
  have h1 : List.countP (fun J => decide (I'.id = J.id)) l.val ≤
      List.countP (fun J => decide (I'.id = J.id)) (I :: l.val) := by
    by_cases hII' : I'.id = I.id
    · rw [List.countP_cons_of_pos _ l.val]
      · simp
      · simpa using hII'
    · rw [List.countP_cons_of_neg _ l.val]
      simpa using hII'
  exact Nat.le_trans h1 (hl I' hImem)

lemma withUniqueDual_eq_withDual_cons_iff' (I : Index X) :
    (l.cons I).withUniqueDual = (l.cons I).withDual ↔
    l.withUniqueDual = l.withDual ∧ l.countId I ≤ 1 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · have h1 : l.withUniqueDual = l.withDual := by
      exact withUniqueDual_eq_withDual_of_cons l h
    apply And.intro h1 ((withUniqueDual_eq_withDual_cons_iff l I h1).mp h)
  · rw [withUniqueDual_eq_withDual_cons_iff]
    · exact h.2
    · exact h.1

/-!

## withUniqueDualInOther equal to withDualInOther append conditions

-/

lemma withUniqueDualInOther_eq_withDualInOther_append_of_symm'
    (h : (l ++ l2).withUniqueDualInOther l3 = (l ++ l2).withDualInOther l3) :
    (l2 ++ l).withUniqueDualInOther l3 = (l2 ++ l).withDualInOther l3 := by
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
    (l2 ++ l).withUniqueDualInOther l3 = (l2 ++ l).withDualInOther l3 :=
  Iff.intro
    (l.withUniqueDualInOther_eq_withDualInOther_append_of_symm' l2 l3)
    (l2.withUniqueDualInOther_eq_withDualInOther_append_of_symm' l l3)

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
    l.withUniqueDualInOther (l3 ++ l2) = l.withDualInOther (l3 ++ l2) :=
  Iff.intro
    (l.withUniqueDualInOther_eq_withDualInOther_of_append_symm' l2 l3)
    (l.withUniqueDualInOther_eq_withDualInOther_of_append_symm' l3 l2)

/-!

## withDual equal to withUniqueDual append conditions

-/

lemma append_withDual_eq_withUniqueDual_iff :
    (l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    ((l.withUniqueDual ∩ (l.withDualInOther l2)ᶜ) ∪ l.withUniqueDualInOther l2)
    = l.withDual ∪ l.withDualInOther l2
    ∧ (l2.withUniqueDual ∩ (l2.withDualInOther l)ᶜ) ∪ l2.withUniqueDualInOther l
    = l2.withDual ∪ l2.withDualInOther l := by
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
    (h : (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
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
    (h : (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
    l2.withUniqueDualInOther l = l2.withDualInOther l := by
  rw [append_withDual_eq_withUniqueDual_symm] at h
  exact append_withDual_eq_withUniqueDual_withUniqueDualInOther_inl l2 l h

lemma append_withDual_eq_withUniqueDual_iff' :
    (l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    l.withUniqueDual = l.withDual ∧ l2.withUniqueDual = l2.withDual
    ∧ l.withUniqueDualInOther l2 = l.withDualInOther l2 ∧
    l2.withUniqueDualInOther l = l2.withDualInOther l := by
  apply Iff.intro
  · intro h
    exact ⟨append_withDual_eq_withUniqueDual_inl l l2 h,
      append_withDual_eq_withUniqueDual_inr l l2 h,
      append_withDual_eq_withUniqueDual_withUniqueDualInOther_inl l l2 h,
      append_withDual_eq_withUniqueDual_withUniqueDualInOther_inr l l2 h⟩
  · intro h
    rw [append_withDual_eq_withUniqueDual_iff]
    rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
    have h1 : l.withDual ∩ (l.withDualInOther l2)ᶜ = l.withDual := by
      rw [Finset.inter_eq_left, Finset.subset_iff, ← h.1, ← h.2.2.1]
      intro i hi
      simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true,
        Option.not_isSome, Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome,
        Finset.compl_filter, not_and, not_forall, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hn
      simp_all
    have h2 : l2.withDual ∩ (l2.withDualInOther l)ᶜ = l2.withDual := by
      rw [Finset.inter_eq_left, Finset.subset_iff, ← h.2.1, ← h.2.2.2]
      intro i hi
      simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true,
        Option.not_isSome, Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome,
        Finset.compl_filter, not_and, not_forall, Finset.mem_filter, Finset.mem_univ, true_and]
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

lemma append_withDual_eq_withUniqueDual_contr_left
    (h1 : (l ++ l2).withUniqueDual = (l ++ l2).withDual):
      (l.contrIndexList ++ l2).withUniqueDual = (l.contrIndexList ++ l2).withDual := by
    rw [withUniqueDual_eq_withDual_iff_all_countId_le_two] at h1 ⊢
    simp only [append_val, countId_append, List.all_append, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq]
    simp at h1
    apply And.intro
    · intro I hI
      have hIl := h1.1 I (List.mem_of_mem_filter hI)
      have ht : l.contrIndexList.countId I ≤ l.countId I :=
        countId_contrIndexList_le_countId l I
      omega
    · intro I hI
      have hIl2 := h1.2 I hI
      have ht : l.contrIndexList.countId I ≤ l.countId I :=
        countId_contrIndexList_le_countId l I
      omega

end IndexList

end IndexNotation
