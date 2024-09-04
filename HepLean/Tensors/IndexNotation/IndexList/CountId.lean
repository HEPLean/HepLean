/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.IndexNotation.IndexList.Duals
/-!

# Counting ids

-/

namespace IndexNotation

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

/-!

## countId

-/

/-- The number of times the id of an index `I` appears in a list of indices `l`. -/
def countId (I : Index X) : ℕ :=
  l.val.countP (fun J => I.id = J.id)

/-!

## Basic properties

-/
omit [IndexNotation X] [Fintype X] [DecidableEq X] in
@[simp]
lemma countId_append (I : Index X) : (l ++ l2).countId I = l.countId I + l2.countId I := by
  simp [countId]

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_eq_length_filter (I : Index X) :
    l.countId I = (l.val.filter (fun J => I.id = J.id)).length := by
  rw [countId, List.countP_eq_length_filter]

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_index_neq_zero (i : Fin l.length) : l.countId (l.val.get i) ≠ 0 := by
  by_contra hn
  rw [countId_eq_length_filter, List.length_eq_zero] at hn
  refine (List.mem_nil_iff (l.val.get i)).mp ?_
  simpa [← hn] using List.getElem_mem l.val i.1 i.isLt

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_append_symm (I : Index X) : (l ++ l2).countId I = (l2 ++ l).countId I := by
  simp only [countId_append]
  exact Nat.add_comm (l.countId I) (l2.countId I)

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_eq_one_append_mem_right_self_eq_one {I : Index X} (hI : I ∈ l2.val)
    (h : (l ++ l2).countId I = 1) : l2.countId I = 1 := by
  simp only [countId_append] at h
  have hmem : I ∈ l2.val.filter (fun J => I.id = J.id) := by
    simp [List.mem_filter, decide_True, and_true, hI]
  have h1 : l2.countId I ≠ 0 := by
    rw [countId_eq_length_filter]
    by_contra hn
    rw [@List.length_eq_zero] at hn
    rw [hn] at hmem
    exact (List.mem_nil_iff I).mp hmem
  omega

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_eq_one_append_mem_right_other_eq_zero {I : Index X} (hI : I ∈ l2.val)
    (h : (l ++ l2).countId I = 1) : l.countId I = 0 := by
  simp only [countId_append] at h
  have hmem : I ∈ l2.val.filter (fun J => I.id = J.id) := by
    simp [List.mem_filter, decide_True, and_true, hI]
  have h1 : l2.countId I ≠ 0 := by
    rw [countId_eq_length_filter]
    by_contra hn
    rw [@List.length_eq_zero] at hn
    rw [hn] at hmem
    exact (List.mem_nil_iff I).mp hmem
  omega

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
@[simp]
lemma countId_cons_eq_two {I : Index X} :
    (l.cons I).countId I = 2 ↔ l.countId I = 1 := by
  simp [countId]

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_congr {I J : Index X} (h : I.id = J.id) : l.countId I = l.countId J := by
  simp [countId, h]

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_neq_zero_mem (I : Index X) (h : l.countId I ≠ 0) :
    ∃ I', I' ∈ l.val ∧ I.id = I'.id := by
  rw [countId_eq_length_filter] at h
  have h' := List.isEmpty_iff_length_eq_zero.mp.mt h
  simp only at h'
  have h'' := eq_false_of_ne_true h'
  rw [List.isEmpty_false_iff_exists_mem] at h''
  obtain ⟨I', hI'⟩ := h''
  simp only [List.mem_filter, decide_eq_true_eq] at hI'
  exact ⟨I', hI'⟩

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_mem (I : Index X) (hI : I ∈ l.val) : l.countId I ≠ 0 := by
  rw [countId_eq_length_filter]
  by_contra hn
  rw [List.length_eq_zero] at hn
  have hIme : I ∈ List.filter (fun J => decide (I.id = J.id)) l.val := by
    simp [hI]
  rw [hn] at hIme
  exact (List.mem_nil_iff I).mp hIme

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_get_other (i : Fin l.length) : l2.countId (l.val.get i) =
    (List.finRange l2.length).countP (fun j => l.AreDualInOther l2 i j) := by
  rw [countId_eq_length_filter]
  rw [List.countP_eq_length_filter]
  have hl2 : l2.val = List.map l2.val.get (List.finRange l2.length) := by
    simp only [length, List.finRange_map_get]
  nth_rewrite 1 [hl2]
  rw [List.filter_map, List.length_map]
  rfl

/-! TODO: Replace with mathlib lemma. -/
omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma filter_finRange (i : Fin l.length) :
    List.filter (fun j => i = j) (List.finRange l.length) = [i] := by
  have h3 : (List.filter (fun j => i = j) (List.finRange l.length)).length = 1 := by
    rw [← List.countP_eq_length_filter]
    trans List.count i (List.finRange l.length)
    · rw [List.count]
      apply List.countP_congr (fun j _ => ?_)
      simp only [decide_eq_true_eq, beq_iff_eq]
      exact eq_comm
    · exact List.nodup_iff_count_eq_one.mp (List.nodup_finRange l.length) _ (List.mem_finRange i)
  have h4 : i ∈ List.filter (fun j => i = j) (List.finRange l.length) := by
    simp
  rw [@List.length_eq_one] at h3
  obtain ⟨a, ha⟩ := h3
  rw [ha] at h4
  simp only [List.mem_singleton] at h4
  subst h4
  exact ha

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_get (i : Fin l.length) : l.countId (l.val.get i) =
    (List.finRange l.length).countP (fun j => l.AreDualInSelf i j) + 1 := by
  rw [countId_get_other l l]
  have h1 : (List.finRange l.length).countP (fun j => l.AreDualInSelf i j)
      = ((List.finRange l.length).filter (fun j => l.AreDualInOther l i j)).countP
      (fun j => ¬ i = j) := by
    rw [List.countP_filter]
    refine List.countP_congr ?_
    intro j _
    simp [AreDualInSelf, AreDualInOther]
  rw [h1]
  have h1 := List.length_eq_countP_add_countP (fun j => i = j)
    ((List.finRange l.length).filter (fun j => l.AreDualInOther l i j))
  have h2 : List.countP (fun j => i = j)
      (List.filter (fun j => l.AreDualInOther l i j) (List.finRange l.length)) =
      List.countP (fun j => l.AreDualInOther l i j)
      (List.filter (fun j => i = j) (List.finRange l.length)) := by
    rw [List.countP_filter, List.countP_filter]
    refine List.countP_congr (fun j _ => ?_)
    simpa using And.comm
  have ha := l.filter_finRange
  rw [ha] at h2
  rw [h2] at h1
  rw [List.countP_eq_length_filter, h1, add_comm]
  simp only [decide_eq_true_eq, decide_not, add_right_inj]
  simp [List.countP, List.countP.go, AreDualInOther]

/-!

## Duals and countId

-/
omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_gt_zero_of_mem_withDual (i : Fin l.length) (h : i ∈ l.withDual) :
    1 < l.countId (l.val.get i) := by
  rw [countId_get]
  by_contra hn
  simp only [Nat.lt_add_left_iff_pos, not_lt, Nat.le_zero_eq] at hn
  rw [List.countP_eq_length_filter, List.length_eq_zero] at hn
  rw [mem_withDual_iff_exists] at h
  obtain ⟨j, hj⟩ := h
  have hjmem : j ∈ (List.finRange l.length).filter (fun j => decide (l.AreDualInSelf i j)) := by
    simpa using hj
  rw [hn] at hjmem
  exact (List.mem_nil_iff j).mp hjmem

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_of_not_mem_withDual (i : Fin l.length)(h : i ∉ l.withDual) :
    l.countId (l.val.get i) = 1 := by
  rw [countId_get]
  simp only [add_left_eq_self]
  rw [List.countP_eq_length_filter]
  simp only [List.length_eq_zero]
  rw [List.filter_eq_nil]
  simp only [List.mem_finRange, decide_eq_true_eq, true_implies]
  rw [mem_withDual_iff_exists] at h
  simpa using h

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma mem_withDual_iff_countId_gt_one (i : Fin l.length) :
    i ∈ l.withDual ↔ 1 < l.countId (l.val.get i) := by
  refine Iff.intro (fun h => countId_gt_zero_of_mem_withDual l i h) (fun h => ?_)
  by_contra hn
  have hn' := countId_of_not_mem_withDual l i hn
  omega

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_neq_zero_of_mem_withDualInOther (i : Fin l.length) (h : i ∈ l.withDualInOther l2) :
    l2.countId (l.val.get i) ≠ 0 := by
  rw [mem_withInDualOther_iff_exists] at h
  rw [countId_eq_length_filter]
  by_contra hn
  rw [List.length_eq_zero] at hn
  obtain ⟨j, hj⟩ := h
  have hjmem : l2.val.get j ∈ List.filter (fun J => decide ((l.val.get i).id = J.id)) l2.val := by
    simp only [List.get_eq_getElem, List.mem_filter, decide_eq_true_eq]
    apply And.intro
    · exact List.getElem_mem l2.val (↑j) j.isLt
    · simpa [AreDualInOther] using hj
  rw [hn] at hjmem
  exact (List.mem_nil_iff (l2.val.get j)).mp hjmem

omit [IndexNotation X] [Fintype X] in
lemma countId_of_not_mem_withDualInOther (i : Fin l.length) (h : i ∉ l.withDualInOther l2) :
    l2.countId (l.val.get i) = 0 := by
  by_contra hn
  rw [countId_eq_length_filter] at hn
  rw [← List.isEmpty_iff_length_eq_zero] at hn
  have hx := eq_false_of_ne_true hn
  rw [List.isEmpty_false_iff_exists_mem] at hx
  obtain ⟨j, hj⟩ := hx
  have hjmem : j ∈ l2.val := List.mem_of_mem_filter hj
  have hj' : l2.val.indexOf j < l2.length := List.indexOf_lt_length.mpr hjmem
  rw [mem_withInDualOther_iff_exists] at h
  simp only [not_exists] at h
  have hj' := h ⟨l2.val.indexOf j, hj'⟩
  simp only [AreDualInOther, idMap, List.get_eq_getElem, List.getElem_indexOf] at hj'
  simp only [List.get_eq_getElem, List.mem_filter, decide_eq_true_eq] at hj
  simp_all only [List.get_eq_getElem, List.isEmpty_eq_true, List.getElem_indexOf, not_true_eq_false]

omit [IndexNotation X] [Fintype X] in
lemma mem_withDualInOther_iff_countId_neq_zero (i : Fin l.length) :
    i ∈ l.withDualInOther l2 ↔ l2.countId (l.val.get i) ≠ 0 := by
  refine Iff.intro (fun h => countId_neq_zero_of_mem_withDualInOther l l2 i h)
    (fun h => ?_)
  by_contra hn
  have hn' := countId_of_not_mem_withDualInOther l l2 i hn
  exact h hn'

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma mem_withoutDual_iff_countId_eq_one (i : Fin l.length) :
    i ∈ l.withoutDual ↔ l.countId (l.val.get i) = 1 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · exact countId_of_not_mem_withDual l i (l.not_mem_withDual_of_mem_withoutDual i h)
  · by_contra hn
    have h : i ∈ l.withDual := by
      simp only [withoutDual, Option.isNone_iff_eq_none, Finset.mem_filter, Finset.mem_univ,
        true_and] at hn
      simpa using Option.ne_none_iff_isSome.mp hn
    rw [mem_withDual_iff_countId_gt_one] at h
    omega

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_eq_two_of_mem_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    l.countId (l.val.get i) = 2 := by
  rw [countId_get]
  simp only [Nat.reduceEqDiff]
  let i' := (l.getDual? i).get (mem_withUniqueDual_isSome l i h)
  have h1 : [i'] = (List.finRange l.length).filter (fun j => (l.AreDualInSelf i j)) := by
    trans List.filter (fun j => (l.AreDualInSelf i j)) [i']
    · simp [List.filter, i']
    trans List.filter (fun j => (l.AreDualInSelf i j))
      ((List.finRange l.length).filter (fun j => j = i'))
    · apply congrArg
      rw [← filter_finRange l i']
      apply List.filter_congr (fun j _ => ?_)
      simpa using eq_comm
    trans List.filter (fun j => j = i')
      ((List.finRange l.length).filter fun j => l.AreDualInSelf i j)
    · exact List.filter_comm (fun j => l.AreDualInSelf i j) (fun j => j = i')
        (List.finRange l.length)
    · simp only [List.filter_filter, decide_eq_true_eq, Bool.decide_and]
      refine List.filter_congr (fun j _ => ?_)
      simp only [Bool.and_iff_right_iff_imp, decide_eq_true_eq]
      simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      intro hj
      have hj' := h.2 j hj
      apply Option.some_injective
      rw [hj']
      simp [i']
  rw [List.countP_eq_length_filter, ← h1]
  rfl

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma mem_withUniqueDual_of_countId_eq_two (i : Fin l.length)
    (h : l.countId (l.val.get i) = 2) : i ∈ l.withUniqueDual := by
  have hw : i ∈ l.withDual := by
    rw [mem_withDual_iff_countId_gt_one, h]
    exact Nat.one_lt_two
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, true_and]
  apply And.intro ((mem_withDual_iff_isSome l i).mp hw)
  intro j hj
  rw [@countId_get] at h
  simp only [List.countP_eq_length_filter, Nat.reduceEqDiff] at h
  rw [List.length_eq_one] at h
  obtain ⟨a, ha⟩ := h
  have hj : j ∈ List.filter (fun j => decide (l.AreDualInSelf i j)) (List.finRange l.length) := by
    simpa using hj
  rw [ha] at hj
  simp only [List.mem_singleton] at hj
  subst hj
  have ht : (l.getDual? i).get ((mem_withDual_iff_isSome l i).mp hw) ∈
    (List.finRange l.length).filter (fun j => decide (l.AreDualInSelf i j)) := by
      simp
  rw [ha] at ht
  simp only [List.mem_singleton] at ht
  subst ht
  simp

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma mem_withUniqueDual_iff_countId_eq_two (i : Fin l.length) :
    i ∈ l.withUniqueDual ↔ l.countId (l.val.get i) = 2 :=
  Iff.intro (fun h => l.countId_eq_two_of_mem_withUniqueDual i h)
    (fun h => l.mem_withUniqueDual_of_countId_eq_two i h)

omit [IndexNotation X] [Fintype X] [DecidableEq X] in
lemma countId_eq_one_of_mem_withUniqueDualInOther (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    l.countId (l.val.get i) = 1 ∧ l2.countId (l.val.get i) = 1 := by
  let i' := (l.getDualInOther? l2 i).get (mem_withUniqueDualInOther_isSome l l2 i h)
  have h1 : [i'] = (List.finRange l2.length).filter (fun j => (l.AreDualInOther l2 i j)) := by
    trans List.filter (fun j => (l.AreDualInOther l2 i j)) [i']
    · simp [List.filter, i']
    trans List.filter (fun j => (l.AreDualInOther l2 i j))
      ((List.finRange l2.length).filter (fun j => j = i'))
    · apply congrArg
      rw [← filter_finRange l2 i']
      apply List.filter_congr (fun j _ => ?_)
      simpa using eq_comm
    trans List.filter (fun j => j = i')
      ((List.finRange l2.length).filter (fun j => (l.AreDualInOther l2 i j)))
    · simp only [List.filter_filter, decide_eq_true_eq, Bool.decide_and]
      apply List.filter_congr (fun j _ => ?_)
      exact Bool.and_comm (decide (l.AreDualInOther l2 i j)) (decide (j = i'))
    · simp only [List.filter_filter, decide_eq_true_eq, Bool.decide_and]
      refine List.filter_congr (fun j _ => ?_)
      simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true,
        Option.not_isSome, Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome,
        Finset.mem_filter, Finset.mem_univ, true_and] at h
      simp only [Bool.and_iff_right_iff_imp, decide_eq_true_eq]
      intro hj
      have hj' := h.2.2 j hj
      apply Option.some_injective
      rw [hj']
      simp [i']
  apply And.intro
  · simp only [withUniqueDualInOther, Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [mem_withDual_iff_countId_gt_one] at h
    have h2 := countId_index_neq_zero l i
    omega
  · rw [countId_get_other, List.countP_eq_length_filter, ← h1]
    rfl

omit [IndexNotation X] [Fintype X] in
lemma mem_withUniqueDualInOther_of_countId_eq_one (i : Fin l.length)
    (h : l.countId (l.val.get i) = 1 ∧ l2.countId (l.val.get i) = 1) :
    i ∈ l.withUniqueDualInOther l2 := by
  have hw : i ∈ l.withDualInOther l2 := by
    rw [mem_withDualInOther_iff_countId_neq_zero, h.2]
    exact Nat.one_ne_zero
  simp only [withUniqueDualInOther, Finset.mem_filter, Finset.mem_univ, true_and]
  apply And.intro
  · rw [mem_withDual_iff_countId_gt_one]
    omega
  · apply And.intro
    · rw [mem_withDualInOther_iff_countId_neq_zero]
      exact countId_neq_zero_of_mem_withDualInOther l l2 i hw
    · intro j hj
      have h2 := h.2
      rw [countId_get_other l l2, List.countP_eq_length_filter, List.length_eq_one] at h2
      obtain ⟨a, ha⟩ := h2
      have hj : j ∈ List.filter (fun j => decide (l.AreDualInOther l2 i j))
          (List.finRange l2.length) := by
        simpa using hj
      rw [ha] at hj
      simp only [List.mem_singleton] at hj
      subst hj
      have ht : (l.getDualInOther? l2 i).get ((mem_withInDualOther_iff_isSome l l2 i).mp hw) ∈
        (List.finRange l2.length).filter (fun j => decide (l.AreDualInOther l2 i j)) := by
          simp
      rw [ha] at ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact Option.some_get ((mem_withInDualOther_iff_isSome l l2 i).mp hw)

omit [IndexNotation X] [Fintype X] in
lemma mem_withUniqueDualInOther_iff_countId_eq_one (i : Fin l.length) :
    i ∈ l.withUniqueDualInOther l2 ↔ l.countId (l.val.get i) = 1 ∧ l2.countId (l.val.get i) = 1 :=
  Iff.intro (fun h => l.countId_eq_one_of_mem_withUniqueDualInOther l2 i h)
    (fun h => l.mem_withUniqueDualInOther_of_countId_eq_one l2 i h)

/-!

## getDual? and countId

-/

omit [IndexNotation X] [Fintype X] [DecidableEq X]

@[simp]
lemma getDual?_countId (i : Fin l.length) (h : (l.getDual? i).isSome) :
    l.countId (l.val[Fin.val ((l.getDual? i).get h)]) = l.countId (l.val.get i) := by
  apply countId_congr
  change l.idMap ((l.getDual? i).get h) = _
  simp only [getDual?_get_id, List.get_eq_getElem]
  rfl

@[simp]
lemma getDualInOther?_countId_right (i : Fin l.length) (h : (l.getDualInOther? l2 i).isSome) :
    l2.countId (l2.val[Fin.val ((l.getDualInOther? l2 i).get h)]) = l2.countId (l.val.get i) := by
  apply countId_congr
  change l2.idMap ((l.getDualInOther? l2 i).get h) = _
  simp only [getDualInOther?_id, List.get_eq_getElem]
  rfl

@[simp]
lemma getDualInOther?_countId_left (i : Fin l.length) (h : (l.getDualInOther? l2 i).isSome) :
    l.countId (l2.val[Fin.val ((l.getDualInOther? l2 i).get h)]) = l.countId (l.val.get i) := by
  apply countId_congr
  change l2.idMap ((l.getDualInOther? l2 i).get h) = _
  simp only [getDualInOther?_id, List.get_eq_getElem]
  rfl

lemma getDual?_isSome_of_countId_eq_two {i : Fin l.length}
    (h : l.countId (l.val.get i) = 2) : (l.getDual? i).isSome := by
  rw [← l.mem_withUniqueDual_iff_countId_eq_two] at h
  exact mem_withUniqueDual_isSome l i h

/-!

## Filters

-/

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
  exact congrFun (congrArg List.cons (id (Eq.symm hme))) []

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
  exact congrFun (congrArg List.cons (id (Eq.symm hme))) []

lemma filter_id_of_countId_eq_two {i : Fin l.length}
    (h : l.countId (l.val.get i) = 2) :
    l.val.filter (fun J => (l.val.get i).id = J.id) =
    [l.val.get i, l.val.get ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))] ∨
    l.val.filter (fun J => (l.val.get i).id = J.id) =
    [l.val.get ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)), l.val.get i] := by
  have hc := h
  rw [countId_eq_length_filter] at hc
  by_cases hi : i < ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))
  · refine Or.inl (List.Sublist.eq_of_length ?_ ?_).symm
    · have h1 : [l.val.get i, l.val.get
          ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))].filter
            (fun J => (l.val.get i).id = J.id) = [l.val.get i, l.val.get
          ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))] := by
        simp only [List.get_eq_getElem, decide_True, List.filter_cons_of_pos, List.cons.injEq,
          List.filter_eq_self, List.mem_singleton, decide_eq_true_eq, forall_eq, true_and]
        change l.idMap i = l.idMap ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))
        exact Eq.symm (getDual?_get_id l i (getDual?_isSome_of_countId_eq_two l h))
      rw [← h1]
      refine List.Sublist.filter (fun (J : Index X) => ((l.val.get i).id = J.id)) ?_
      rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
      refine ⟨⟨⟨![i, (l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)],
          List.nodup_ofFn.mp ?_⟩, ?_⟩, ?_⟩
      · simpa using Fin.ne_of_lt hi
      · intro a b
        fin_cases a, b
          <;> simp [hi]
        exact Fin.le_of_lt hi
      · intro a
        fin_cases a <;> rfl
    · rw [hc]
      rfl
  · have hi' : ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)) < i := by
      have h1 := l.getDual?_get_areDualInSelf i (getDual?_isSome_of_countId_eq_two l h)
      simp only [AreDualInSelf] at h1
      have h2 := h1.1
      omega
    refine Or.inr (List.Sublist.eq_of_length ?_ ?_).symm
    · have h1 : [l.val.get ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)),
        l.val.get i].filter (fun J => (l.val.get i).id = J.id) = [l.val.get
        ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h)), l.val.get i,] := by
        simp only [List.get_eq_getElem, List.filter_eq_self, List.mem_cons, List.mem_singleton,
          decide_eq_true_eq, forall_eq_or_imp, forall_eq, and_true]
        apply And.intro
        · change l.idMap i = l.idMap ((l.getDual? i).get (l.getDual?_isSome_of_countId_eq_two h))
          exact Eq.symm (getDual?_get_id l i (getDual?_isSome_of_countId_eq_two l h))
        · exact And.symm (if_false_right.mp trivial)
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
        · simp [hi']
        · simp only [List.get_eq_getElem, List.length_cons, List.length_singleton, Nat.reduceAdd,
          List.length_nil, Fin.zero_eta, Fin.isValue, Function.Embedding.coeFn_mk,
          Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons, Fin.zero_le,
          iff_true]
          exact Fin.le_of_lt hi'
        · simp [hi']
        · simp [hi']
      · intro a
        fin_cases a <;> rfl
    · rw [hc]
      rfl

end IndexList

end IndexNotation
