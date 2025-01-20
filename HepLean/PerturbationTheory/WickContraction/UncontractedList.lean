/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.ExtractEquiv
/-!

# List of uncontracted elements

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open HepLean.Fin

/-!

## Some properties of lists of fin

-/

lemma fin_list_sorted_monotone_sorted {n m : ℕ} (l: List (Fin n)) (hl : l.Sorted (· ≤ ·))
    (f : Fin n → Fin m) (hf : StrictMono f) : ((List.map f l)).Sorted (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sorted_cons, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    apply And.intro
    · simp only [List.sorted_cons] at hl
      intro b hb
      have hl1 := hl.1 b hb
      exact (StrictMono.le_iff_le hf).mpr hl1
    · simp only [List.sorted_cons] at hl
      exact ih hl.2

lemma fin_list_sorted_succAboveEmb_sorted (l: List (Fin n)) (hl : l.Sorted (· ≤ ·))
    (i : Fin n.succ) : ((List.map i.succAboveEmb l)).Sorted (· ≤ ·) := by
  apply fin_list_sorted_monotone_sorted
  exact hl
  simp only [Fin.coe_succAboveEmb]
  exact Fin.strictMono_succAbove i

lemma fin_list_sorted_split :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : ℕ) →
    l = l.filter (fun x => x.1 < i) ++ l.filter (fun x => i ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp only [List.sorted_cons] at hl
    by_cases ha : a < i
    · conv_lhs => rw [fin_list_sorted_split l hl.2 i]
      rw [← List.cons_append]
      rw [List.filter_cons_of_pos, List.filter_cons_of_neg]
      simp only [decide_eq_true_eq, not_le, ha]
      simp [ha]
    · have hx : List.filter (fun x => decide (x.1 < i)) (a :: l) = [] := by
        simp only [ha, decide_false, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg,
          List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp only [hx, List.nil_append]
      rw [List.filter_cons_of_pos]
      simp only [List.cons.injEq, true_and]
      have hl' := fin_list_sorted_split l hl.2 i
      have hx : List.filter (fun x => decide (x.1 < i)) (l) = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp only [hx, List.nil_append] at hl'
      conv_lhs => rw [hl']
      simp only [decide_eq_true_eq]
      omega

lemma fin_list_sorted_indexOf_filter_le_mem :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : Fin n) →
    (hl : i ∈ l) →
    List.indexOf i (List.filter (fun x => decide (↑i ≤ ↑x)) l) = 0
  | [], _, _, _ => by simp
  | a :: l, hl, i, hi => by
    simp only [List.sorted_cons] at hl
    by_cases ha : i ≤ a
    · simp only [ha, decide_true, List.filter_cons_of_pos]
      have ha : a = i := by
        simp only [List.mem_cons] at hi
        rcases hi with hi | hi
        · subst hi
          rfl
        · have hl' := hl.1 i hi
          exact Fin.le_antisymm hl' ha
      subst ha
      simp
    · simp only [not_le] at ha
      rw [List.filter_cons_of_neg (by simpa using ha)]
      rw [fin_list_sorted_indexOf_filter_le_mem l hl.2]
      simp only [List.mem_cons] at hi
      rcases hi with hi | hi
      · omega
      · exact hi

lemma fin_list_sorted_indexOf_mem :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : Fin n) →
    (hi : i ∈ l) →
    l.indexOf i = (l.filter (fun x => x.1 < i.1)).length := by
  intro l hl i hi
  conv_lhs => rw [fin_list_sorted_split l hl i]
  rw [List.indexOf_append_of_not_mem]
  erw [fin_list_sorted_indexOf_filter_le_mem l hl i hi]
  · simp
  · simp

lemma orderedInsert_of_fin_list_sorted :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·)) → (i : Fin n) →
    List.orderedInsert (· ≤ ·) i l = l.filter (fun x => x.1 < i.1) ++
    i :: l.filter (fun x => i.1 ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp only [List.sorted_cons] at hl
    by_cases ha : i ≤ a
    · simp only [List.orderedInsert, ha, ↓reduceIte, Fin.val_fin_lt, decide_eq_true_eq, not_lt,
      List.filter_cons_of_neg, Fin.val_fin_le, decide_true, List.filter_cons_of_pos]
      have h1 : List.filter (fun x => decide (↑x < ↑i)) l = [] := by
        simp only [List.filter_eq_nil_iff, decide_eq_true_eq, not_lt]
        intro a ha
        have ha' := hl.1 a ha
        omega
      have hl : l = List.filter (fun x => decide (i ≤ x)) l := by
        conv_lhs => rw [fin_list_sorted_split l hl.2 i]
        simp [h1]
      simp [← hl, h1]
    · simp only [List.orderedInsert, ha, ↓reduceIte, Fin.val_fin_lt, Fin.val_fin_le, decide_false,
      Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
      rw [List.filter_cons_of_pos]
      rw [orderedInsert_of_fin_list_sorted l hl.2 i]
      simp only [Fin.val_fin_lt, Fin.val_fin_le, List.cons_append]
      simp only [decide_eq_true_eq]
      omega

lemma orderedInsert_eq_insertIdx_of_fin_list_sorted (l : List (Fin n)) (hl : l.Sorted (· ≤ ·))
    (i : Fin n) :
    List.orderedInsert (· ≤ ·) i l = l.insertIdx (l.filter (fun x => x.1 < i.1)).length i := by
  let n : Fin l.length.succ := ⟨(List.filter (fun x => decide (x < i)) l).length, by
    have h1 := l.length_filter_le (fun x => x.1 < i.1)
    simp only [Fin.val_fin_lt] at h1
    omega⟩
  simp only [Fin.val_fin_lt]
  conv_rhs => rw [insertIdx_eq_take_drop _ _ n]
  rw [orderedInsert_of_fin_list_sorted]
  congr
  · conv_rhs =>
      rhs
      rw [fin_list_sorted_split l hl i]
    simp [n]
  · conv_rhs =>
      rhs
      rw [fin_list_sorted_split l hl i]
    simp [n]
  exact hl

/-!

## Uncontracted List

-/

def uncontractedList : List (Fin n) := List.filter (fun x => x ∈ c.uncontracted) (List.finRange n)

lemma uncontractedList_mem_iff (i : Fin n) :
    i ∈ c.uncontractedList ↔ i ∈ c.uncontracted := by
  simp [uncontractedList]

@[simp]
lemma nil_zero_uncontractedList : (nil (n := 0)).uncontractedList = [] := by
  simp [nil, uncontractedList]

lemma congr_uncontractedList {n m : ℕ} (h : n = m) (c : WickContraction n) :
    ((congr h) c).uncontractedList = List.map (finCongr h) c.uncontractedList := by
  subst h
  simp [congr]

lemma uncontractedList_get_mem_uncontracted (i : Fin c.uncontractedList.length) :
    c.uncontractedList.get i ∈ c.uncontracted := by
  rw [← uncontractedList_mem_iff]
  simp

lemma uncontractedList_sorted : List.Sorted (· ≤ ·) c.uncontractedList := by
  rw [uncontractedList]
  apply List.Sorted.filter
  rw [← List.ofFn_id]
  exact Monotone.ofFn_sorted fun ⦃a b⦄ a => a

lemma uncontractedList_nodup : c.uncontractedList.Nodup := by
  rw [uncontractedList]
  refine List.Nodup.filter (fun x => decide (x ∈ c.uncontracted)) ?_
  exact List.nodup_finRange n

lemma uncontractedList_toFinset (c : WickContraction n) :
    c.uncontractedList.toFinset = c.uncontracted := by
  simp [uncontractedList]

lemma uncontractedList_eq_sort (c : WickContraction n) :
    c.uncontractedList = c.uncontracted.sort (· ≤ ·) := by
  symm
  rw [← uncontractedList_toFinset]
  refine (List.toFinset_sort (α := Fin n) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_nodup c
  · exact uncontractedList_sorted c

lemma uncontractedList_length_eq_card (c : WickContraction n) :
    c.uncontractedList.length = c.uncontracted.card := by
  rw [uncontractedList_eq_sort]
  exact Finset.length_sort fun x1 x2 => x1 ≤ x2

lemma uncontractedList_succAboveEmb_sorted (c : WickContraction n) (i : Fin n.succ) :
    ((List.map i.succAboveEmb c.uncontractedList)).Sorted (· ≤ ·) := by
  apply fin_list_sorted_succAboveEmb_sorted
  exact uncontractedList_sorted c

lemma uncontractedList_succAboveEmb_nodup (c : WickContraction n) (i : Fin n.succ) :
    ((List.map i.succAboveEmb c.uncontractedList)).Nodup := by
  refine List.Nodup.map ?_ ?_
  · exact Function.Embedding.injective i.succAboveEmb
  · exact uncontractedList_nodup c

lemma uncontractedList_succAboveEmb_toFinset (c : WickContraction n) (i : Fin n.succ) :
    (List.map i.succAboveEmb c.uncontractedList).toFinset =
    (Finset.map i.succAboveEmb c.uncontracted) := by
  ext a
  simp only [Fin.coe_succAboveEmb, List.mem_toFinset, List.mem_map, Finset.mem_map,
    Fin.succAboveEmb_apply]
  rw [← c.uncontractedList_toFinset]
  simp

lemma uncontractedList_succAboveEmb_eq_sort(c : WickContraction n) (i : Fin n.succ) :
    (List.map i.succAboveEmb c.uncontractedList) =
    (c.uncontracted.map i.succAboveEmb).sort (· ≤ ·) := by
  rw [← uncontractedList_succAboveEmb_toFinset]
  symm
  refine (List.toFinset_sort (α := Fin n.succ) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_succAboveEmb_nodup c i
  · exact uncontractedList_succAboveEmb_sorted c i

lemma uncontractedList_succAboveEmb_eraseIdx_sorted (c : WickContraction n) (i : Fin n.succ)
    (k: ℕ) : ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).Sorted (· ≤ ·) := by
  apply HepLean.List.eraseIdx_sorted
  exact uncontractedList_succAboveEmb_sorted c i

lemma uncontractedList_succAboveEmb_eraseIdx_nodup (c : WickContraction n) (i : Fin n.succ) (k: ℕ) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).Nodup := by
  refine List.Nodup.eraseIdx k ?_
  exact uncontractedList_succAboveEmb_nodup c i

lemma uncontractedList_succAboveEmb_eraseIdx_toFinset (c : WickContraction n) (i : Fin n.succ)
    (k : ℕ) (hk : k < c.uncontractedList.length) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).toFinset =
    (c.uncontracted.map i.succAboveEmb).erase (i.succAboveEmb c.uncontractedList[k]) := by
  ext a
  simp only [Fin.coe_succAboveEmb, List.mem_toFinset, Fin.succAboveEmb_apply, Finset.mem_erase,
    ne_eq, Finset.mem_map]
  rw [mem_eraseIdx_nodup _ _ _ (by simpa using hk)]
  simp_all only [List.mem_map, List.getElem_map, ne_eq]
  apply Iff.intro
  · intro a_1
    simp_all only [not_false_eq_true, true_and]
    obtain ⟨left, right⟩ := a_1
    obtain ⟨w, h⟩ := left
    obtain ⟨left, right_1⟩ := h
    subst right_1
    use w
    simp_all [uncontractedList]
  · intro a_1
    simp_all only [not_false_eq_true, and_true]
    obtain ⟨left, right⟩ := a_1
    obtain ⟨w, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    subst right
    use w
    simp_all [uncontractedList]
  exact uncontractedList_succAboveEmb_nodup c i

lemma uncontractedList_succAboveEmb_eraseIdx_eq_sort (c : WickContraction n) (i : Fin n.succ)
    (k : ℕ) (hk : k < c.uncontractedList.length) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k) =
    ((c.uncontracted.map i.succAboveEmb).erase
    (i.succAboveEmb c.uncontractedList[k])).sort (· ≤ ·) := by
  rw [← uncontractedList_succAboveEmb_eraseIdx_toFinset]
  symm
  refine (List.toFinset_sort (α := Fin n.succ) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_succAboveEmb_eraseIdx_nodup c i k
  · exact uncontractedList_succAboveEmb_eraseIdx_sorted c i k

lemma uncontractedList_succAbove_orderedInsert_sorted (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i
      (List.map i.succAboveEmb c.uncontractedList)).Sorted (· ≤ ·) := by
  refine List.Sorted.orderedInsert i (List.map (⇑i.succAboveEmb) c.uncontractedList) ?_
  exact uncontractedList_succAboveEmb_sorted c i

lemma uncontractedList_succAbove_orderedInsert_nodup (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).Nodup := by
  have h1 : (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).Perm
    (i :: List.map i.succAboveEmb c.uncontractedList) := by
    exact List.perm_orderedInsert (fun x1 x2 => x1 ≤ x2) i _
  apply List.Perm.nodup h1.symm
  simp only [Nat.succ_eq_add_one, List.nodup_cons, List.mem_map, not_exists,
    not_and]
  apply And.intro
  · intro x _
    exact Fin.succAbove_ne i x
  · exact uncontractedList_succAboveEmb_nodup c i

lemma uncontractedList_succAbove_orderedInsert_toFinset (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).toFinset =
    (Insert.insert i (Finset.map i.succAboveEmb c.uncontracted)) := by
  ext a
  simp only [Nat.succ_eq_add_one, Fin.coe_succAboveEmb, List.mem_toFinset, List.mem_orderedInsert,
    List.mem_map, Finset.mem_insert, Finset.mem_map, Fin.succAboveEmb_apply]
  rw [← uncontractedList_toFinset]
  simp

lemma uncontractedList_succAbove_orderedInsert_eq_sort (c : WickContraction n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)) =
    (Insert.insert i (Finset.map i.succAboveEmb c.uncontracted)).sort (· ≤ ·) := by
  rw [← uncontractedList_succAbove_orderedInsert_toFinset]
  symm
  refine (List.toFinset_sort (α := Fin n.succ) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_succAbove_orderedInsert_nodup c i
  · exact uncontractedList_succAbove_orderedInsert_sorted c i

lemma uncontractedList_extractEquiv_symm_none (c : WickContraction n) (i : Fin n.succ) :
    ((extractEquiv i).symm ⟨c, none⟩).uncontractedList =
    List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList) := by
  rw [uncontractedList_eq_sort, extractEquiv_symm_none_uncontracted]
  rw [uncontractedList_succAbove_orderedInsert_eq_sort]

def uncontractedListOrderPos (c : WickContraction n) (i : Fin n.succ) : ℕ :=
  (List.filter (fun x => x.1 < i.1) c.uncontractedList).length

@[simp]
lemma uncontractedListOrderPos_lt_length_add_one (c : WickContraction n) (i : Fin n.succ) :
    c.uncontractedListOrderPos i < c.uncontractedList.length + 1 := by
  simp only [uncontractedListOrderPos, Nat.succ_eq_add_one]
  have h1 := c.uncontractedList.length_filter_le (fun x => x.1 < i.1)
  omega

lemma take_uncontractedListOrderPos_eq_filter (c : WickContraction n) (i : Fin n.succ) :
    (c.uncontractedList.take (c.uncontractedListOrderPos i)) =
    c.uncontractedList.filter (fun x => x.1 < i.1) := by
  nth_rewrite 1 [fin_list_sorted_split c.uncontractedList _ i]
  simp only [uncontractedListOrderPos, Nat.succ_eq_add_one, List.take_left']
  exact uncontractedList_sorted c

lemma take_uncontractedListOrderPos_eq_filter_sort (c : WickContraction n) (i : Fin n.succ) :
    (c.uncontractedList.take (c.uncontractedListOrderPos i)) =
    (c.uncontracted.filter (fun x => x.1 < i.1)).sort (· ≤ ·) := by
  rw [take_uncontractedListOrderPos_eq_filter]
  have h1 : (c.uncontractedList.filter (fun x => x.1 < i.1)).Sorted (· ≤ ·) := by
    apply List.Sorted.filter
    exact uncontractedList_sorted c
  have h2 : (c.uncontractedList.filter (fun x => x.1 < i.1)).Nodup := by
    refine List.Nodup.filter _ ?_
    exact uncontractedList_nodup c
  have h3 : (c.uncontractedList.filter (fun x => x.1 < i.1)).toFinset =
    (c.uncontracted.filter (fun x => x.1 < i.1)) := by
    rw [uncontractedList_eq_sort]
    simp
  rw [← h3]
  exact ((List.toFinset_sort (α := Fin n) (· ≤ ·) h2).mpr h1).symm

lemma orderedInsert_succAboveEmb_uncontractedList_eq_insertIdx (c : WickContraction n)
    (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)) =
    (List.map i.succAboveEmb c.uncontractedList).insertIdx (uncontractedListOrderPos c i) i := by
  rw [orderedInsert_eq_insertIdx_of_fin_list_sorted]
  swap
  exact uncontractedList_succAboveEmb_sorted c i
  congr 1
  simp only [Nat.succ_eq_add_one, Fin.val_fin_lt, Fin.coe_succAboveEmb, uncontractedListOrderPos]
  rw [List.filter_map]
  simp only [List.length_map]
  congr
  funext x
  simp only [Function.comp_apply, Fin.succAbove, decide_eq_decide]
  split
  simp only [Fin.lt_def, Fin.coe_castSucc]
  rename_i h
  simp_all only [Fin.lt_def, Fin.coe_castSucc, not_lt, Fin.val_succ]
  omega

def uncontractedFinEquiv (c : WickContraction n) :
    Fin (c.uncontractedList).length ≃ c.uncontracted where
  toFun i := ⟨c.uncontractedList.get i, c.uncontractedList_get_mem_uncontracted i⟩
  invFun i := ⟨List.indexOf i.1 c.uncontractedList,
    List.indexOf_lt_length.mpr ((c.uncontractedList_mem_iff i.1).mpr i.2)⟩
  left_inv i := by
    ext
    exact List.get_indexOf (uncontractedList_nodup c) _
  right_inv i := by
    ext
    simp

@[simp]
lemma uncontractedList_getElem_uncontractedFinEquiv_symm (k : c.uncontracted) :
    c.uncontractedList[(c.uncontractedFinEquiv.symm k).val] = k := by
  simp [uncontractedFinEquiv]

lemma uncontractedFinEquiv_symm_eq_filter_length (k : c.uncontracted) :
    (c.uncontractedFinEquiv.symm k).val =
    (List.filter (fun i => i < k.val) c.uncontractedList).length := by
  simp only [uncontractedFinEquiv, List.get_eq_getElem, Equiv.coe_fn_symm_mk]
  rw [fin_list_sorted_indexOf_mem]
  · simp
  · exact uncontractedList_sorted c
  · rw [uncontractedList_mem_iff]
    exact k.2

lemma take_uncontractedFinEquiv_symm (k : c.uncontracted) :
    c.uncontractedList.take (c.uncontractedFinEquiv.symm k).val =
    c.uncontractedList.filter (fun i => i < k.val) := by
  have hl := fin_list_sorted_split c.uncontractedList (uncontractedList_sorted c) k.val
  conv_lhs =>
    rhs
    rw [hl]
  rw [uncontractedFinEquiv_symm_eq_filter_length]
  simp

def uncontractedStatesEquiv (φs : List 𝓕.States) (c : WickContraction φs.length) :
    Option c.uncontracted ≃ Option (Fin (c.uncontractedList.map φs.get).length) :=
  Equiv.optionCongr (c.uncontractedFinEquiv.symm.trans (finCongr (by simp)))

@[simp]
lemma uncontractedStatesEquiv_none (φs : List 𝓕.States) (c : WickContraction φs.length) :
    (uncontractedStatesEquiv φs c).toFun none = none := by
  simp [uncontractedStatesEquiv]

lemma uncontractedStatesEquiv_list_sum [AddCommMonoid α] (φs : List 𝓕.States)
  (c : WickContraction φs.length) (f : Option (Fin (c.uncontractedList.map φs.get).length) → α) :
    ∑ (i : Option (Fin (c.uncontractedList.map φs.get).length)), f i =
    ∑ (i : Option c.uncontracted), f (c.uncontractedStatesEquiv φs i) := by
  rw [(c.uncontractedStatesEquiv φs).sum_comp]

lemma uncontractedList_extractEquiv_symm_some (c : WickContraction n) (i : Fin n.succ)
    (k : c.uncontracted) : ((extractEquiv i).symm ⟨c, some k⟩).uncontractedList =
    ((c.uncontractedList).map i.succAboveEmb).eraseIdx (c.uncontractedFinEquiv.symm k) := by
  rw [uncontractedList_eq_sort]
  rw [uncontractedList_succAboveEmb_eraseIdx_eq_sort]
  swap
  simp only [Fin.is_lt]
  congr
  simp only [Nat.succ_eq_add_one, extractEquiv, Equiv.coe_fn_symm_mk,
    uncontractedList_getElem_uncontractedFinEquiv_symm, Fin.succAboveEmb_apply]
  rw [insert_some_uncontracted]
  ext a
  simp

lemma filter_uncontractedList (c : WickContraction n) (p : Fin n → Prop) [DecidablePred p] :
    (c.uncontractedList.filter p) = (c.uncontracted.filter p).sort (· ≤ ·) := by
  have h1 : (c.uncontractedList.filter p).Sorted (· ≤ ·) := by
    apply List.Sorted.filter
    exact uncontractedList_sorted c
  have h2 : (c.uncontractedList.filter p).Nodup := by
    refine List.Nodup.filter _ ?_
    exact uncontractedList_nodup c
  have h3 : (c.uncontractedList.filter p).toFinset = (c.uncontracted.filter p) := by
    ext a
    simp only [List.toFinset_filter, decide_eq_true_eq, Finset.mem_filter, List.mem_toFinset,
      and_congr_left_iff]
    rw [uncontractedList_mem_iff]
    simp
  have hx := (List.toFinset_sort (· ≤ ·) h2).mpr h1
  rw [← hx, h3]

end WickContraction

end FieldStruct
