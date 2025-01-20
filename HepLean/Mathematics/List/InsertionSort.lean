/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Mathematics.List.InsertIdx
/-!
# List lemmas

-/
namespace HepLean.List

open Fin
open HepLean
variable {n : Nat}

lemma insertionSortMin_lt_length_succ {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (i : α) (l : List α) :
    insertionSortMinPos r i l < (insertionSortDropMinPos r i l).length.succ := by
  rw [insertionSortMinPos]
  simp only [List.length_cons, List.insertionSort.eq_2, insertionSortDropMinPos,
    Nat.succ_eq_add_one]
  rw [eraseIdx_length']
  simp

def insertionSortMinPosFin {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (i : α) (l : List α) :
    Fin (insertionSortDropMinPos r i l).length.succ :=
  ⟨insertionSortMinPos r i l, insertionSortMin_lt_length_succ r i l⟩

lemma insertionSortMin_lt_mem_insertionSortDropMinPos {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l : List α)
    (i : Fin (insertionSortDropMinPos r a l).length) :
    r (insertionSortMin r a l) ((insertionSortDropMinPos r a l)[i]) := by
  let l1 := List.insertionSort r (a :: l)
  have hl1 : l1.Sorted r := by exact List.sorted_insertionSort r (a :: l)
  simp only [l1] at hl1
  rw [insertionSort_eq_insertionSortMin_cons r a l] at hl1
  simp only [List.sorted_cons, List.mem_insertionSort] at hl1
  apply hl1.1 ((insertionSortDropMinPos r a l)[i])
  simp

@[simp]
lemma insertionSortMinPos_insertionSortEquiv {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l : List α) :
    insertionSortEquiv r (a ::l) (insertionSortMinPos r a l) =
    ⟨0, by simp [List.orderedInsert_length]⟩ := by
  rw [insertionSortMinPos]
  exact
    Equiv.apply_symm_apply (insertionSortEquiv r (a :: l)) ⟨0, insertionSortMinPos.proof_1 r a l⟩

lemma insertionSortEquiv_gt_zero_of_ne_insertionSortMinPos {α : Type} (r : α → α → Prop)
    [DecidableRel r] [IsTotal α r] [IsTrans α r] (a : α) (l : List α) (k : Fin (a :: l).length)
    (hk : k ≠ insertionSortMinPos r a l) :
    ⟨0, by simp [List.orderedInsert_length]⟩ < insertionSortEquiv r (a :: l) k := by
  by_contra hn
  simp only [List.insertionSort.eq_2, List.length_cons, not_lt] at hn
  refine hk ((Equiv.apply_eq_iff_eq_symm_apply (insertionSortEquiv r (a :: l))).mp ?_)
  simp_all only [List.length_cons, ne_eq, Fin.le_def, nonpos_iff_eq_zero, List.insertionSort.eq_2]
  simp only [Fin.ext_iff]
  omega

lemma insertionSortMin_lt_mem_insertionSortDropMinPos_of_lt {α : Type} (r : α → α → Prop)
    [DecidableRel r] [IsTotal α r] [IsTrans α r] (a : α) (l : List α)
    (i : Fin (insertionSortDropMinPos r a l).length)
    (h : (insertionSortMinPosFin r a l).succAbove i < insertionSortMinPosFin r a l) :
    ¬ r ((insertionSortDropMinPos r a l)[i]) (insertionSortMin r a l) := by
  simp only [Fin.getElem_fin, insertionSortMin, List.get_eq_getElem, List.length_cons]
  have h1 : (insertionSortDropMinPos r a l)[i] =
    (a :: l).get (finCongr (eraseIdx_length_succ (a :: l) (insertionSortMinPos r a l))
    ((insertionSortMinPosFin r a l).succAbove i)) := by
    trans (insertionSortDropMinPos r a l).get i
    simp only [Fin.getElem_fin, List.get_eq_getElem]
    simp only [insertionSortDropMinPos, List.length_cons, Nat.succ_eq_add_one,
      finCongr_apply, Fin.coe_cast]
    rw [eraseIdx_get]
    simp only [List.length_cons, Function.comp_apply, List.get_eq_getElem, Fin.coe_cast]
    rfl
  erw [h1]
  simp only [List.length_cons, Nat.succ_eq_add_one, List.get_eq_getElem,
    Fin.coe_cast]
  apply insertionSortEquiv_order
  simpa using h
  simp only [List.insertionSort.eq_2, List.length_cons, finCongr_apply]
  apply lt_of_eq_of_lt (insertionSortMinPos_insertionSortEquiv r a l)
  simp only [List.insertionSort.eq_2]
  apply insertionSortEquiv_gt_zero_of_ne_insertionSortMinPos r a l
  simp only [List.length_cons, ne_eq, Fin.ext_iff, Fin.coe_cast]
  have hl : (insertionSortMinPos r a l).val = (insertionSortMinPosFin r a l).val := by
    rfl
  simp only [hl, Nat.succ_eq_add_one, Fin.val_eq_val, ne_eq]
  exact Fin.succAbove_ne (insertionSortMinPosFin r a l) i

end HepLean.List
