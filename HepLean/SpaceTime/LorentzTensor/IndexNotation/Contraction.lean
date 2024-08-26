/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.WithUniqueDual
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

/-!

## Indices which do not have duals.

-/

/-- The finite set of indices of an index list which do not have a dual. -/
def withoutDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isNone) Finset.univ

lemma withDual_disjoint_withoutDual : Disjoint l.withDual l.withoutDual := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  by_contra hn
  subst hn
  simp_all only [withDual, Finset.mem_filter, Finset.mem_univ, true_and, withoutDual,
    Option.isNone_iff_eq_none, Option.isSome_none, Bool.false_eq_true]

lemma not_mem_withDual_of_mem_withoutDual (i : Fin l.length) (h : i ∈ l.withoutDual) :
    i ∉ l.withDual := by
  have h1 := l.withDual_disjoint_withoutDual
  exact Finset.disjoint_right.mp h1 h

lemma withDual_union_withoutDual : l.withDual ∪ l.withoutDual = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  by_cases h : (l.getDual? i).isSome
  · simp [withDual, Finset.mem_filter, Finset.mem_univ, h]
  · simp at h
    simp [withoutDual, Finset.mem_filter, Finset.mem_univ, h]

lemma mem_withoutDual_iff_countId_eq_one (i : Fin l.length) :
    i ∈ l.withoutDual ↔ l.countId (l.val.get i) = 1 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · exact countId_of_not_mem_withDual l i (l.not_mem_withDual_of_mem_withoutDual i h)
  · by_contra hn
    have h : i ∈ l.withDual := by
      simp [withoutDual] at hn
      simpa using Option.ne_none_iff_isSome.mp hn
    rw [mem_withDual_iff_countId_gt_one] at h
    omega

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

lemma withoutDual_sort_eq_filter : l.withoutDual.sort (fun i j => i ≤ j) =
    (List.finRange l.length).filter (fun i => i ∈ l.withoutDual) := by
  rw [withoutDual]
  rw [← filter_sort_comm]
  simp only [Option.isNone_iff_eq_none, Finset.mem_filter, Finset.mem_univ, true_and]
  apply congrArg
  exact Fin.sort_univ l.length

/-- An equivalence splitting the indices of an index list `l` into those indices
  which have a dual in `l` and those which do not have a dual in `l`. -/
def dualEquiv : l.withDual ⊕ Fin l.withoutDual.card ≃ Fin l.length :=
  (Equiv.sumCongr (Equiv.refl _) l.withoutDualEquiv).trans <|
  (Equiv.Finset.union _ _ l.withDual_disjoint_withoutDual).trans <|
  Equiv.subtypeUnivEquiv (by simp [withDual_union_withoutDual])

/-!

## The contraction list

-/

/-- The index list formed from `l` by selecting only those indices in `l` which
  do not have a dual. -/
def contrIndexList : IndexList X where
  val := l.val.filter (fun I => l.countId I = 1)

@[simp]
lemma contrIndexList_empty : (⟨[]⟩ : IndexList X).contrIndexList = { val := [] } := by
  apply ext
  simp [contrIndexList]

lemma contrIndexList_val : l.contrIndexList.val =
    l.val.filter (fun I => l.countId I = 1) := by
  rfl

/-- An alternative form of the contracted index list. -/
@[simp]
def contrIndexList' : IndexList X where
  val := List.ofFn (l.val.get ∘ Subtype.val ∘ l.withoutDualEquiv)

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
  · simp only [List.map_ofFn]

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
    simp only [contrIndexList, List.mem_filter, decide_eq_true_eq] at h
    exact h.1
  rw [List.length_eq_one] at h1
  obtain ⟨J, hJ⟩ := h1
  rw [hJ] at h2
  simp at h2
  subst h2
  exact hJ

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
      simp only [h, not_false_eq_true]
    · simp only [hI, decide_False, Bool.not_false, Bool.true_and, decide_eq_decide]
      rw [List.countP_cons_of_neg]
      simp only [decide_eq_true_eq]
      exact fun a => hI (id (Eq.symm a))
  · simp only [decide_True, List.countP_cons_of_pos, add_left_eq_self, decide_eq_true_eq]
    exact h

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
    simp only [List.countP_nil]

lemma countId_contrIndexList_le_one (I : Index X) :
    l.contrIndexList.countId I ≤ 1 := by
  by_cases h : l.contrIndexList.countId I = 0
  · simp [h]
  · obtain ⟨I', hI1, hI2⟩ := countId_neq_zero_mem l.contrIndexList I h
    rw [countId_congr l.contrIndexList hI2, mem_contrIndexList_countId_contrIndexList l hI1]

lemma countId_contrIndexList_eq_one_iff_countId_eq_one (I : Index X) :
    l.contrIndexList.countId I = 1 ↔ l.countId I = 1 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨I', hI1, hI2⟩ := countId_neq_zero_mem l.contrIndexList I (by omega)
    simp [contrIndexList] at hI1
    rw [countId_congr l hI2]
    exact hI1.2
  · obtain ⟨I', hI1, hI2⟩ := countId_neq_zero_mem l I (by omega)
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

/-!

## Splitting withUniqueDual

-/

instance (i j : Option (Fin l.length)) : Decidable (i < j) :=
  match i, j with
  | none, none => isFalse (fun a => a)
  | none, some _ => isTrue (by trivial)
  | some _, none => isFalse (fun a => a)
  | some i, some j => Fin.decLt i j

/-- The finite set of those indices of `l` which have a unique dual, and for which
  that dual is greater-then (determined by the ordering on `Fin`) then the index itself. -/
def withUniqueDualLT : Finset (Fin l.length) :=
  Finset.filter (fun i => i < l.getDual? i) l.withUniqueDual

/-- The casting of an element of `withUniqueDualLT` to an element of `withUniqueDual`. -/
def withUniqueDualLTToWithUniqueDual (i : l.withUniqueDualLT) : l.withUniqueDual :=
  ⟨i.1, Finset.mem_of_mem_filter i.1 i.2⟩

instance : Coe l.withUniqueDualLT l.withUniqueDual where
  coe := l.withUniqueDualLTToWithUniqueDual

/-- The finite set of those indices of `l` which have a unique dual, and for which
  that dual is less-then (determined by the ordering on `Fin`) then the index itself. -/
def withUniqueDualGT : Finset (Fin l.length) :=
  Finset.filter (fun i => ¬ i < l.getDual? i) l.withUniqueDual

/-- The casting of an element in `withUniqueDualGT` to an element of `withUniqueDual`. -/
def withUniqueDualGTToWithUniqueDual (i : l.withUniqueDualGT) : l.withUniqueDual :=
  ⟨i.1, Finset.mem_of_mem_filter _ i.2⟩

instance : Coe l.withUniqueDualGT l.withUniqueDual where
  coe := l.withUniqueDualGTToWithUniqueDual

lemma withUniqueDualLT_disjoint_withUniqueDualGT :
    Disjoint l.withUniqueDualLT l.withUniqueDualGT := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact @Finset.filter_inter_filter_neg_eq (Fin l.length) _ _ _ _ _

lemma withUniqueDualLT_union_withUniqueDualGT :
    l.withUniqueDualLT ∪ l.withUniqueDualGT = l.withUniqueDual :=
  Finset.filter_union_filter_neg_eq _ _

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
  toFun i := ⟨l.getDualEquiv i, by
    have hi := i.2
    simp only [withUniqueDualGT, Finset.mem_filter, Finset.coe_mem, true_and]
    simp only [getDualEquiv, Equiv.coe_fn_mk, Option.some_get, Finset.coe_mem,
      getDual?_getDual?_get_of_withUniqueDual]
    simp only [withUniqueDualLT, Finset.mem_filter] at hi
    apply option_not_lt
    · simpa [withUniqueDualLTToWithUniqueDual] using hi.2
    · exact Ne.symm (getDual?_neq_self l i)⟩
  invFun i := ⟨l.getDualEquiv.symm i, by
    have hi := i.2
    simp only [withUniqueDualLT, Finset.mem_filter, Finset.coe_mem, true_and, gt_iff_lt]
    simp only [getDualEquiv, Equiv.coe_fn_symm_mk, Option.some_get, Finset.coe_mem,
      getDual?_getDual?_get_of_withUniqueDual]
    simp only [withUniqueDualGT, Finset.mem_filter] at hi
    apply lt_option_of_not
    · simpa [withUniqueDualLTToWithUniqueDual] using hi.2
    · exact (getDual?_neq_self l i)⟩
  left_inv x := SetCoe.ext (by simp [withUniqueDualGTToWithUniqueDual,
    withUniqueDualLTToWithUniqueDual])
  right_inv x := SetCoe.ext (by simp [withUniqueDualGTToWithUniqueDual,
    withUniqueDualLTToWithUniqueDual])

/-- An equivalence from `l.withUniqueDualLT ⊕ l.withUniqueDualLT` to `l.withUniqueDual`.
  The first `l.withUniqueDualLT` are taken to themselves, whilst the second copy are
  taken to their dual. -/
def withUniqueLTGTEquiv : l.withUniqueDualLT ⊕ l.withUniqueDualLT ≃ l.withUniqueDual := by
  apply (Equiv.sumCongr (Equiv.refl _) l.withUniqueDualLTEquivGT).trans
  apply (Equiv.Finset.union _ _ l.withUniqueDualLT_disjoint_withUniqueDualGT).trans
  apply (Equiv.subtypeEquivRight (by simp only [l.withUniqueDualLT_union_withUniqueDualGT,
    implies_true]))

/-!

## withUniqueDualInOther equal univ

-/

/-! TODO: There is probably a better place for this section. -/

lemma withUniqueDualInOther_eq_univ_fst_withDual_empty
    (h : l.withUniqueDualInOther l2 = Finset.univ) : l.withDual = ∅ := by
  rw [@Finset.eq_empty_iff_forall_not_mem]
  intro x
  have hx : x ∈ l.withUniqueDualInOther l2 := by
    rw [h]
    exact Finset.mem_univ x
  rw [withUniqueDualInOther] at hx
  simp only [mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx
  simpa using hx.1

lemma withUniqueDualInOther_eq_univ_fst_eq_contrIndexList
    (h : l.withUniqueDualInOther l2 = Finset.univ) :
    l = l.contrIndexList := by
  refine Eq.symm (contrIndexList_of_withDual_empty l ?h)
  exact withUniqueDualInOther_eq_univ_fst_withDual_empty l l2 h

lemma withUniqueDualInOther_eq_univ_symm (hl : l.length = l2.length)
    (h : l.withUniqueDualInOther l2 = Finset.univ) :
    l2.withUniqueDualInOther l = Finset.univ := by
  let S' : Finset (Fin l2.length) :=
      Finset.map ⟨Subtype.val, Subtype.val_injective⟩
      (Equiv.finsetCongr
      (l.getDualInOtherEquiv l2) Finset.univ)
  have hSCard : S'.card = l2.length := by
    rw [Finset.card_map]
    simp only [Finset.univ_eq_attach, Equiv.finsetCongr_apply, Finset.card_map, Finset.card_attach]
    rw [h, ← hl]
    exact Finset.card_fin l.length
  have hsCardUn : S'.card = (@Finset.univ (Fin l2.length)).card := by
    rw [hSCard]
    exact Eq.symm (Finset.card_fin l2.length)
  have hS'Eq : S' = (l2.withUniqueDualInOther l) := by
    rw [@Finset.ext_iff]
    intro a
    simp only [S']
    simp
  rw [hS'Eq] at hsCardUn
  exact (Finset.card_eq_iff_eq_univ (l2.withUniqueDualInOther l)).mp hsCardUn

lemma withUniqueDualInOther_eq_univ_contr_refl :
    l.contrIndexList.withUniqueDualInOther l.contrIndexList = Finset.univ := by
  rw [@Finset.eq_univ_iff_forall]
  intro x
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome,
    Option.isSome_none, Bool.false_eq_true, not_false_eq_true, mem_withInDualOther_iff_isSome,
    getDualInOther?_self_isSome, true_and, Finset.mem_filter, Finset.mem_univ]
  simp only [contrIndexList_getDual?, Option.isSome_none, Bool.false_eq_true, not_false_eq_true,
    contrIndexList_getDualInOther?_self, Option.some.injEq, true_and]
  intro j hj
  have h1 : j = x := by
    by_contra hn
    have hj : l.contrIndexList.AreDualInSelf x j := by
      simp [AreDualInOther] at hj
      simp only [AreDualInSelf, ne_eq, contrIndexList_idMap, hj, and_true]
      exact fun a => hn (id (Eq.symm a))
    exact (contrIndexList_areDualInSelf_false l x j).mp hj
  exact h1

lemma withUniqueDualInOther_eq_univ_trans (h : l.withUniqueDualInOther l2 = Finset.univ)
    (h' : l2.withUniqueDualInOther l3 = Finset.univ) :
    l.withUniqueDualInOther l3 = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and]
  have hi : i ∈ l.withUniqueDualInOther l2 := by
    rw [h]
    exact Finset.mem_univ i
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi
  have hi2 : ((l.getDualInOther? l2 i).get hi.2.1) ∈ l2.withUniqueDualInOther l3 := by
    rw [h']
    exact Finset.mem_univ ((l.getDualInOther? l2 i).get hi.right.left)
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi2
  apply And.intro hi.1
  apply And.intro
  · rw [@getDualInOther?_isSome_iff_exists]
    use (l2.getDualInOther? l3 ((l.getDualInOther? l2 i).get hi.2.1)).get hi2.2.1
    simp only [AreDualInOther, getDualInOther?_id]
  intro j hj
  have hj' : j = (l2.getDualInOther? l3 ((l.getDualInOther? l2 i).get hi.2.1)).get hi2.2.1 := by
    rw [← eq_getDualInOther?_get_of_withUniqueDualInOther_iff]
    simpa only [AreDualInOther, getDualInOther?_id] using hj
    rw [h']
    exact Finset.mem_univ ((l.getDualInOther? l2 i).get hi.right.left)
  have hs : (l.getDualInOther? l3 i).isSome := by
    rw [@getDualInOther?_isSome_iff_exists]
    exact Exists.intro j hj
  have hs' : (l.getDualInOther? l3 i).get hs = (l2.getDualInOther? l3
      ((l.getDualInOther? l2 i).get hi.2.1)).get hi2.2.1 := by
    rw [← eq_getDualInOther?_get_of_withUniqueDualInOther_iff]
    simp only [AreDualInOther, getDualInOther?_id]
    rw [h']
    exact Finset.mem_univ ((l.getDualInOther? l2 i).get hi.right.left)
  rw [← hj'] at hs'
  rw [← hs']
  exact Eq.symm (Option.eq_some_of_isSome hs)

lemma withUniqueDualInOther_eq_univ_iff_forall :
    l.withUniqueDualInOther l2 = Finset.univ ↔
    ∀ (x : Fin l.length), l.getDual? x = none ∧ (l.getDualInOther? l2 x).isSome = true ∧
    ∀ (j : Fin l2.length), l.AreDualInOther l2 x j → some j = l.getDualInOther? l2 x := by
  rw [Finset.eq_univ_iff_forall]
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and]

end IndexList

end IndexNotation
