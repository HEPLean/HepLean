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
  simp [insertionSortDropMinPos]
  rw [eraseIdx_length']
  simp

def insertionSortMinPosFin  {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (i : α) (l : List α) : Fin (insertionSortDropMinPos r i l).length.succ :=
  ⟨insertionSortMinPos r i l, insertionSortMin_lt_length_succ r i l⟩

lemma insertionSortMin_lt_mem_insertionSortDropMinPos {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l : List α)
    (i :  Fin (insertionSortDropMinPos r a l).length) :
    r (insertionSortMin r a l) ((insertionSortDropMinPos r a l)[i])  := by
  let l1 :=  List.insertionSort r (a :: l)
  have hl1 : l1.Sorted r := by exact List.sorted_insertionSort r (a :: l)
  simp only [l1] at hl1
  rw [insertionSort_eq_insertionSortMin_cons r a l] at hl1
  simp at hl1
  apply hl1.1 ((insertionSortDropMinPos r a l)[i])
  simp

@[simp]
lemma insertionSortMinPos_insertionSortEquiv {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l : List α) :
    insertionSortEquiv r (a ::l) (insertionSortMinPos r a l) = ⟨0, by simp [List.orderedInsert_length]⟩ := by
  rw [insertionSortMinPos]
  exact
    Equiv.apply_symm_apply (insertionSortEquiv r (a :: l)) ⟨0, insertionSortMinPos.proof_1 r a l⟩

lemma insertionSortEquiv_gt_zero_of_ne_insertionSortMinPos {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l : List α) (k : Fin (a :: l).length) (hk : k ≠ insertionSortMinPos r a l) :
    ⟨0, by simp [List.orderedInsert_length]⟩ < insertionSortEquiv r (a :: l) k  := by
    by_contra hn
    simp at hn
    have h0 :  (insertionSortEquiv r (a :: l)) k = ⟨0, by simp [List.orderedInsert_length]⟩ := by
      simp_all [Fin.le_def]
      simp [Fin.ext_iff]
      omega
    have hk' : k = (insertionSortEquiv r (a :: l)).symm ⟨0, by simp [List.orderedInsert_length]⟩ := by
      exact (Equiv.apply_eq_iff_eq_symm_apply (insertionSortEquiv r (a :: l))).mp h0
    exact hk hk'

lemma insertionSortMin_lt_mem_insertionSortDropMinPos_of_lt {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l : List α)
    (i :  Fin (insertionSortDropMinPos r a l).length)
    (h : (insertionSortMinPosFin r a l).succAbove i < insertionSortMinPosFin r a l) :
    ¬ r ((insertionSortDropMinPos r a l)[i]) (insertionSortMin r a l)   := by
  simp [insertionSortMin]
  have h1 : (insertionSortDropMinPos r a l)[i] =
    (a :: l).get (finCongr (eraseIdx_length_succ (a :: l) (insertionSortMinPos r a l))
    ((insertionSortMinPosFin r a l).succAbove i)) := by
    trans (insertionSortDropMinPos r a l).get i
    simp
    simp only [insertionSortDropMinPos, List.length_cons, Nat.succ_eq_add_one,
      finCongr_apply, Fin.coe_cast]
    rw [eraseIdx_get]
    simp
    rfl
  erw [h1]
  simp only [List.length_cons, Nat.succ_eq_add_one,  List.get_eq_getElem,
    Fin.coe_cast]
  apply insertionSortEquiv_order
  simpa using h
  simp
  apply lt_of_eq_of_lt (insertionSortMinPos_insertionSortEquiv r a l)
  simp
  apply insertionSortEquiv_gt_zero_of_ne_insertionSortMinPos r a l
  simp [Fin.ext_iff]
  have hl : (insertionSortMinPos r a l).val = (insertionSortMinPosFin r a l).val := by
    rfl
  simp [hl, Fin.val_eq_val]
  exact Fin.succAbove_ne (insertionSortMinPosFin r a l) i





end HepLean.List
