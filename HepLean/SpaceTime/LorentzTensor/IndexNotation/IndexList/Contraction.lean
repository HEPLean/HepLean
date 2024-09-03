/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.Equivs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
/-!

# Contraction of an index list.

In this file we define the contraction of an index list `l` to be the index list formed by
by the subset of indices of `l` which do not have a dual in `l`.

For example, the contraction of the index list `['ᵘ¹', 'ᵘ²', 'ᵤ₁', 'ᵘ¹']` is the index list
`['ᵘ²']`.

We also define the following finite sets
- `l.withoutDual` the finite set of indices of `l` which do not have a dual in `l`.
- `l.withUniqueDualLT` the finite set of those indices of `l` which have a unique dual, and
  for which that dual is greater-then (determined by the ordering on `Fin`) then the index itself.
- `l.withUniqueDualGT` the finite set of those indices of `l` which have a unique dual, and
  for which that dual is less-then (determined by the ordering on `Fin`) then the index itself.

We define an equivalence `l.withUniqueDualLT ⊕ l.withUniqueDualLT ≃ l.withUniqueDual`.

We prove properties related to when `l.withUniqueDualInOther l2 = Finset.univ` for two
index lists `l` and `l2`.

-/

namespace IndexNotation

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

/-- The index list formed from `l` by selecting only those indices in `l` which
  do not have a dual. -/
def contrIndexList : IndexList X where
  val := l.val.filter (fun I => l.countId I = 1)

@[simp]
lemma contrIndexList_empty : (⟨[]⟩ : IndexList X).contrIndexList = { val := [] } := by
  rfl

lemma contrIndexList_val : l.contrIndexList.val =
    l.val.filter (fun I => l.countId I = 1) := by
  rfl

/-- An alternative form of the contracted index list. -/
@[simp]
def contrIndexList' : IndexList X where
  val := List.ofFn (l.val.get ∘ Subtype.val ∘ l.withoutDualEquiv)

lemma withoutDual_sort_eq_filter : l.withoutDual.sort (fun i j => i ≤ j) =
    (List.finRange l.length).filter (fun i => i ∈ l.withoutDual) := by
  rw [withoutDual]
  rw [← filter_sort_comm]
  simp only [Option.isNone_iff_eq_none, Finset.mem_filter, Finset.mem_univ, true_and]
  apply congrArg
  exact Fin.sort_univ l.length

lemma contrIndexList_eq_contrIndexList' : l.contrIndexList = l.contrIndexList' := by
  apply ext
  simp only [contrIndexList']
  trans List.map l.val.get (List.ofFn (Subtype.val ∘ ⇑l.withoutDualEquiv))
  · rw [list_ofFn_withoutDualEquiv_eq_sort, withoutDual_sort_eq_filter]
    simp only [contrIndexList]
    let f1 : Index X → Bool := fun (I : Index X) => l.countId I = 1
    let f2 : (Fin l.length) → Bool := fun i => i ∈ l.withoutDual
    change List.filter f1 l.val = List.map l.val.get (List.filter f2 (List.finRange l.length))
    have hf : f2 = f1 ∘ l.val.get := by
      funext i
      simp only [mem_withoutDual_iff_countId_eq_one l, List.get_eq_getElem, Function.comp_apply, f2,
        f1]
    rw [hf, ← List.filter_map]
    apply congrArg
    simp [length]
  · exact List.map_ofFn (Subtype.val ∘ ⇑l.withoutDualEquiv) l.val.get

@[simp]
lemma contrIndexList_length : l.contrIndexList.length = l.withoutDual.card := by
  simp [contrIndexList_eq_contrIndexList', withoutDual, length]

@[simp]
lemma contrIndexList_idMap (i : Fin l.contrIndexList.length) : l.contrIndexList.idMap i
    = l.idMap (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)).1 := by
  simp [contrIndexList_eq_contrIndexList', idMap]
  rfl

@[simp]
lemma contrIndexList_colorMap (i : Fin l.contrIndexList.length) : l.contrIndexList.colorMap i
    = l.colorMap (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)).1 := by
  simp [contrIndexList_eq_contrIndexList', colorMap]
  rfl

lemma contrIndexList_areDualInSelf (i j : Fin l.contrIndexList.length) :
    l.contrIndexList.AreDualInSelf i j ↔
    l.AreDualInSelf (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)).1
      (l.withoutDualEquiv (Fin.cast l.contrIndexList_length j)).1 := by
  simp [AreDualInSelf]
  intro _
  trans ¬ (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)) =
    (l.withoutDualEquiv (Fin.cast l.contrIndexList_length j))
  · rw [l.withoutDualEquiv.apply_eq_iff_eq]
    simp [Fin.ext_iff]
  · exact Iff.symm Subtype.coe_ne_coe

@[simp]
lemma contrIndexList_getDual? (i : Fin l.contrIndexList.length) :
    l.contrIndexList.getDual? i = none := by
  rw [← Option.not_isSome_iff_eq_none, ← mem_withDual_iff_isSome, mem_withDual_iff_exists]
  simp only [contrIndexList_areDualInSelf, not_exists]
  have h1 := (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)).2
  have h1' := Finset.disjoint_right.mp l.withDual_disjoint_withoutDual h1
  rw [mem_withDual_iff_exists] at h1'
  exact fun x => forall_not_of_not_exists h1'
    ↑(l.withoutDualEquiv (Fin.cast (contrIndexList_length l) x))

@[simp]
lemma contrIndexList_withDual : l.contrIndexList.withDual = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro x
  simp [withDual]

@[simp]
lemma contrIndexList_withUniqueDual : l.contrIndexList.withUniqueDual = ∅ := by
  rw [withUniqueDual]
  simp

@[simp]
lemma contrIndexList_areDualInSelf_false (i j : Fin l.contrIndexList.length) :
    l.contrIndexList.AreDualInSelf i j ↔ False := by
  refine Iff.intro (fun h => ?_) (fun h => False.elim h)
  have h1 : i ∈ l.contrIndexList.withDual := by
    rw [@mem_withDual_iff_exists]
    exact Exists.intro j h
  simp_all

@[simp]
lemma contrIndexList_of_withDual_empty (h : l.withDual = ∅) : l.contrIndexList = l := by
  have h1 := l.withDual_union_withoutDual
  rw [h, Finset.empty_union] at h1
  apply ext
  rw [@List.ext_get_iff]
  change l.contrIndexList.length = l.length ∧ _
  rw [contrIndexList_length, h1]
  simp only [Finset.card_univ, Fintype.card_fin, List.get_eq_getElem, true_and]
  intro n h1' h2
  simp [contrIndexList_eq_contrIndexList']
  congr
  simp [withoutDualEquiv]
  simp [h1]
  rw [(Finset.orderEmbOfFin_unique' _
    (fun x => Finset.mem_univ ((Fin.castOrderIso _).toOrderEmbedding x))).symm]
  · exact Eq.symm (Nat.add_zero n)
  · rw [h1]
    exact Finset.card_fin l.length

lemma contrIndexList_contrIndexList : l.contrIndexList.contrIndexList = l.contrIndexList := by
  simp

@[simp]
lemma contrIndexList_getDualInOther?_self (i : Fin l.contrIndexList.length) :
    l.contrIndexList.getDualInOther? l.contrIndexList i = some i := by
  simp [getDualInOther?]
  rw [@Fin.find_eq_some_iff]
  simp [AreDualInOther]
  intro j hj
  have h1 : i = j := by
    by_contra hn
    have h : l.contrIndexList.AreDualInSelf i j := by
      simp only [AreDualInSelf]
      simp [hj]
      exact hn
    exact (contrIndexList_areDualInSelf_false l i j).mp h
  exact Fin.ge_of_eq (id (Eq.symm h1))

lemma cons_contrIndexList_of_countId_eq_zero {I : Index X}
    (h : l.countId I = 0) :
    (l.cons I).contrIndexList = l.contrIndexList.cons I := by
  apply ext
  simp [contrIndexList, countId]
  rw [List.filter_cons_of_pos]
  · apply congrArg
    apply List.filter_congr
    intro J hJ
    simp only [decide_eq_decide]
    rw [countId, List.countP_eq_zero] at h
    simp only [decide_eq_true_eq] at h
    rw [List.countP_cons_of_neg]
    simp only [decide_eq_true_eq]
    exact fun a => h J hJ (id (Eq.symm a))
  · simp only [decide_True, List.countP_cons_of_pos, add_left_eq_self, decide_eq_true_eq]
    exact h

lemma cons_contrIndexList_of_countId_neq_zero {I : Index X} (h : l.countId I ≠ 0) :
    (l.cons I).contrIndexList.val = l.contrIndexList.val.filter (fun J => ¬ I.id = J.id) := by
  simp only [contrIndexList, countId, cons_val, decide_not, List.filter_filter, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, Bool.decide_and]
  rw [List.filter_cons_of_neg]
  · apply List.filter_congr
    intro J hJ
    by_cases hI : I.id = J.id
    · simp only [hI, decide_True, List.countP_cons_of_pos, add_left_eq_self, Bool.not_true,
      Bool.false_and, decide_eq_false_iff_not, countId]
      rw [countId, hI] at h
      exact h
    · simp only [hI, decide_False, Bool.not_false, Bool.true_and, decide_eq_decide]
      rw [List.countP_cons_of_neg]
      simp only [decide_eq_true_eq]
      exact fun a => hI (id (Eq.symm a))
  · simp only [decide_True, List.countP_cons_of_pos, add_left_eq_self, decide_eq_true_eq]
    exact h

lemma mem_contrIndexList_countId {I : Index X} (h : I ∈ l.contrIndexList.val) :
    l.countId I = 1 := by
  simp only [contrIndexList, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

lemma mem_contrIndexList_filter {I : Index X} (h : I ∈ l.contrIndexList.val) :
    l.val.filter (fun J => I.id = J.id) = [I] := by
  have h1 : (l.val.filter (fun J => I.id = J.id)).length = 1 := by
    rw [← List.countP_eq_length_filter]
    exact l.mem_contrIndexList_countId h
  have h2 : I ∈ l.val.filter (fun J => I.id = J.id) := by
    simp only [List.mem_filter, decide_True, and_true]
    exact List.mem_of_mem_filter h
  rw [List.length_eq_one] at h1
  obtain ⟨J, hJ⟩ := h1
  rw [hJ] at h2
  simp at h2
  subst h2
  exact hJ

lemma mem_contrIndexList_countId_contrIndexList {I : Index X} (h : I ∈ l.contrIndexList.val) :
    l.contrIndexList.countId I = 1 := by
  trans (l.val.filter (fun J => I.id = J.id)).countP
    (fun i => l.val.countP (fun j => i.id = j.id) = 1)
  · rw [contrIndexList]
    simp only [countId]
    rw [List.countP_filter, List.countP_filter]
    simp only [decide_eq_true_eq, Bool.decide_and]
    congr
    funext a
    rw [Bool.and_comm]
  · rw [l.mem_contrIndexList_filter h, List.countP_cons_of_pos]
    · rfl
    · simp only [decide_eq_true_eq]
      exact mem_contrIndexList_countId l h

lemma countId_contrIndexList_zero_of_countId (I : Index X)
    (h : l.countId I = 0) : l.contrIndexList.countId I = 0 := by
  trans (l.val.filter (fun J => I.id = J.id)).countP
    (fun i => l.val.countP (fun j => i.id = j.id) = 1)
  · rw [contrIndexList]
    simp only [countId]
    rw [List.countP_filter, List.countP_filter]
    simp only [decide_eq_true_eq, Bool.decide_and]
    congr
    funext a
    rw [Bool.and_comm]
  · rw [countId_eq_length_filter, List.length_eq_zero] at h
    rw [h]
    rfl

lemma countId_contrIndexList_le_one (I : Index X) :
    l.contrIndexList.countId I ≤ 1 := by
  by_cases h : l.contrIndexList.countId I = 0
  · exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a => a) h 1
  · obtain ⟨I', hI1, hI2⟩ := countId_neq_zero_mem l.contrIndexList I h
    rw [countId_congr l.contrIndexList hI2, mem_contrIndexList_countId_contrIndexList l hI1]

lemma countId_contrIndexList_eq_one_iff_countId_eq_one (I : Index X) :
    l.contrIndexList.countId I = 1 ↔ l.countId I = 1 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨I', hI1, hI2⟩ := countId_neq_zero_mem l.contrIndexList I (ne_zero_of_eq_one h)
    simp [contrIndexList] at hI1
    rw [countId_congr l hI2]
    exact hI1.2
  · obtain ⟨I', hI1, hI2⟩ := countId_neq_zero_mem l I (ne_zero_of_eq_one h)
    rw [countId_congr l hI2] at h
    rw [countId_congr _ hI2]
    refine mem_contrIndexList_countId_contrIndexList l ?_
    simp [contrIndexList]
    exact ⟨hI1, h⟩

lemma countId_contrIndexList_le_countId (I : Index X) :
    l.contrIndexList.countId I ≤ l.countId I := by
  by_cases h : l.contrIndexList.countId I = 0
  · exact StrictMono.minimal_preimage_bot (fun ⦃a b⦄ a => a) h (l.countId I)
  · have ho : l.contrIndexList.countId I = 1 := by
      have h1 := l.countId_contrIndexList_le_one I
      omega
    rw [ho]
    rw [countId_contrIndexList_eq_one_iff_countId_eq_one] at ho
    rw [ho]

@[simp]
lemma countId_contrIndexList_get (i : Fin l.contrIndexList.length) :
    l.contrIndexList.countId l.contrIndexList.val[Fin.val i] = 1 := by
  refine mem_contrIndexList_countId_contrIndexList l ?_
  exact List.getElem_mem l.contrIndexList.val (↑i) _

lemma filter_id_contrIndexList_eq_of_countId_contrIndexList (I : Index X)
    (h : l.contrIndexList.countId I = l.countId I) :
    l.contrIndexList.val.filter (fun J => I.id = J.id) =
    l.val.filter (fun J => I.id = J.id) := by
  apply List.Sublist.eq_of_length
  · rw [contrIndexList, List.filter_comm]
    exact List.filter_sublist (List.filter (fun J => decide (I.id = J.id)) l.val)
  · rw [← countId_eq_length_filter, h, countId_eq_length_filter]

lemma contrIndexList_append_eq_filter : (l ++ l2).contrIndexList.val =
    l.contrIndexList.val.filter (fun I => l2.countId I = 0) ++
    l2.contrIndexList.val.filter (fun I => l.countId I = 0) := by
  simp [contrIndexList]
  congr 1
  · apply List.filter_congr
    intro I hI
    have hIz : l.countId I ≠ 0 := countId_mem l I hI
    have hx : l.countId I + l2.countId I = 1 ↔ (l2.countId I = 0 ∧ l.countId I = 1) := by
      omega
    simp only [hx, Bool.decide_and]
  · apply List.filter_congr
    intro I hI
    have hIz : l2.countId I ≠ 0 := countId_mem l2 I hI
    have hx : l.countId I + l2.countId I = 1 ↔ (l2.countId I = 1 ∧ l.countId I = 0) := by
      omega
    simp only [hx, Bool.decide_and]
    exact Bool.and_comm (decide (l2.countId I = 1)) (decide (l.countId I = 0))

end IndexList

end IndexNotation
