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
    (i : α) (l : List α) :
    insertionSortMinPos r i l < (insertionSortDropMinPos r i l).length.succ := by
  rw [insertionSortMinPos]
  simp only [List.length_cons, List.insertionSort.eq_2, insertionSortDropMinPos,
    Nat.succ_eq_add_one]
  rw [eraseIdx_length']
  simp

/-- Given a list `i :: l` the left-most minimial position `a` of `i :: l` wrt `r`
  as an element of `Fin (insertionSortDropMinPos r i l).length.succ`. -/
def insertionSortMinPosFin {α : Type} (r : α → α → Prop) [DecidableRel r] (i : α) (l : List α) :
    Fin (insertionSortDropMinPos r i l).length.succ :=
  ⟨insertionSortMinPos r i l, insertionSortMin_lt_length_succ r i l⟩

lemma insertionSortMin_lt_mem_insertionSortDropMinPos {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l : List α)
    (i : Fin (insertionSortDropMinPos r a l).length) :
    r (insertionSortMin r a l) ((insertionSortDropMinPos r a l)[i]) := by
  let l1 := List.insertionSort r (a :: l)
  have hl1 : l1.Sorted r := List.sorted_insertionSort r (a :: l)
  simp only [l1] at hl1
  rw [insertionSort_eq_insertionSortMin_cons r a l] at hl1
  simp only [List.sorted_cons, List.mem_insertionSort] at hl1
  apply hl1.1 ((insertionSortDropMinPos r a l)[i])
  simp

lemma insertionSortMinPos_insertionSortEquiv {α : Type} (r : α → α → Prop) [DecidableRel r]
    (a : α) (l : List α) :
    insertionSortEquiv r (a ::l) (insertionSortMinPos r a l) =
    ⟨0, by simp [List.orderedInsert_length]⟩ := by
  rw [insertionSortMinPos]
  exact
    Equiv.apply_symm_apply (insertionSortEquiv r (a :: l)) ⟨0, insertionSortMinPos.proof_1 r a l⟩

lemma insertionSortEquiv_gt_zero_of_ne_insertionSortMinPos {α : Type} (r : α → α → Prop)
    [DecidableRel r] (a : α) (l : List α) (k : Fin (a :: l).length)
    (hk : k ≠ insertionSortMinPos r a l) :
    ⟨0, by simp [List.orderedInsert_length]⟩ < insertionSortEquiv r (a :: l) k := by
  by_contra hn
  simp only [List.insertionSort.eq_2, List.length_cons, not_lt] at hn
  refine hk ((Equiv.apply_eq_iff_eq_symm_apply (insertionSortEquiv r (a :: l))).mp ?_)
  simp_all only [List.length_cons, ne_eq, Fin.le_def, nonpos_iff_eq_zero, List.insertionSort.eq_2]
  simp only [Fin.ext_iff]
  omega

lemma insertionSortMin_lt_mem_insertionSortDropMinPos_of_lt {α : Type} (r : α → α → Prop)
    [DecidableRel r] (a : α) (l : List α)
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

lemma insertionSort_insertionSort {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (l1 : List α) :
    List.insertionSort r (List.insertionSort r l1) = List.insertionSort r l1 := by
  apply List.Sorted.insertionSort_eq
  exact List.sorted_insertionSort r l1

lemma orderedInsert_commute {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a b : α) (hr : ¬ r a b) : (l : List α) →
    List.orderedInsert r a (List.orderedInsert r b l) =
      List.orderedInsert r b (List.orderedInsert r a l)
  | [] => by
    have hrb : r b a := by
      have ht := IsTotal.total (r := r) a b
      simp_all
    simp [hr, hrb]
  | c :: l => by
    have hrb : r b a := by
      have ht := IsTotal.total (r := r) a b
      simp_all
    simp
    by_cases h : r a c
    · simp [h, hrb]
      rw [if_pos]
      simp [hrb, hr, h]
      exact IsTrans.trans (r :=r) _ _ _ hrb h
    · simp [h]
      have hrca : r c a := by
        have ht := IsTotal.total (r := r) a c
        simp_all
      by_cases hbc : r b c
      · simp [hbc, hr, h]
      · simp [hbc, h]
        exact orderedInsert_commute r a b hr l

lemma insertionSort_orderedInsert_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) : (l1 l2 : List α) →
    List.insertionSort r (List.orderedInsert r a l1 ++ l2) = List.insertionSort r (a :: l1 ++ l2)
  | [], l2 => by
    simp
  | b :: l1, l2 => by
    conv_lhs => simp
    by_cases h : r a b
    · simp [h]
    conv_lhs => simp [h]
    rw [insertionSort_orderedInsert_append r a l1 l2]
    simp
    rw [orderedInsert_commute r a b h]

lemma insertionSort_insertionSort_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] : (l1 l2 : List α) →
    List.insertionSort r (List.insertionSort r l1 ++ l2) = List.insertionSort r (l1 ++ l2)
  | [], l2 => by
    simp
  | a :: l1, l2 => by
    conv_lhs => simp
    rw [insertionSort_orderedInsert_append]
    simp
    rw [insertionSort_insertionSort_append r l1 l2]

lemma insertionSort_append_insertionSort_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] : (l1 l2 l3 : List α) →
    List.insertionSort r (l1 ++ List.insertionSort r l2 ++ l3) =
      List.insertionSort r (l1 ++ l2 ++ l3)
  | [], l2, l3 => by
    simp
    exact insertionSort_insertionSort_append r l2 l3
  | a :: l1, l2, l3 => by
    simp only [List.insertionSort, List.append_eq]
    rw [insertionSort_append_insertionSort_append r l1 l2 l3]

@[simp]
lemma orderedInsert_length {α : Type} (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    (List.orderedInsert r a l).length = (a :: l).length := by
  apply List.Perm.length_eq
  exact List.perm_orderedInsert r a l

lemma takeWhile_orderedInsert {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r]
    (a b : α) (hr : ¬ r a b) : (l : List α) →
    (List.takeWhile (fun c => !decide (r a c)) (List.orderedInsert r b l)).length =
    (List.takeWhile (fun c => !decide (r a c)) l).length + 1
  | [] => by
    simp [hr]
  | c :: l => by
    simp
    by_cases h : r b c
    · simp [h]
      rw [List.takeWhile_cons_of_pos]
      simp
      simp [hr]
    · simp [h]
      have hrba : r b a:= by
        have ht := IsTotal.total (r := r) a b
        simp_all
      have hl : ¬ r a c := by
        by_contra hn
        apply h
        exact IsTrans.trans _ _ _ hrba hn
      simp [hl]
      exact takeWhile_orderedInsert r a b hr l

lemma takeWhile_orderedInsert' {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r]
    (a b : α) (hr : ¬ r a b) : (l : List α) →
    (List.takeWhile (fun c => !decide (r b c)) (List.orderedInsert r a l)).length =
    (List.takeWhile (fun c => !decide (r b c)) l).length
  | [] => by
    simp
    have ht := IsTotal.total (r := r) a b
    simp_all
  | c :: l => by
    have hrba : r b a:= by
      have ht := IsTotal.total (r := r) a b
      simp_all
    simp
    by_cases h : r b c
    · simp [h, hrba]
      by_cases hac : r a c
      · simp [hac, hrba]
      · simp [hac, h]
    · have hcb : r c b := by
        have ht := IsTotal.total (r := r) b c
        simp_all
      by_cases hac : r a c
      · refine False.elim (h ?_)
        exact IsTrans.trans _ _ _ hrba hac
      · simp [hac, h]
        exact takeWhile_orderedInsert' r a b hr l

lemma insertionSortEquiv_commute {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a b : α) (hr : ¬ r a b) (n : ℕ) : (l : List α) →
    (hn : n + 2 < (a :: b :: l).length) →
    insertionSortEquiv r (a :: b :: l) ⟨n + 2, hn⟩ = (finCongr (by simp))
    (insertionSortEquiv r (b :: a :: l) ⟨n + 2, hn⟩) := by
  have hrba : r b a:= by
    have ht := IsTotal.total (r := r) a b
    simp_all
  intro l hn
  simp [insertionSortEquiv]
  conv_lhs => erw [equivCons_succ]
  conv_rhs => erw [equivCons_succ]
  simp
  conv_lhs =>
    rhs
    rhs
    erw [orderedInsertEquiv_succ]
  conv_lhs => erw [orderedInsertEquiv_fin_succ]
  simp
  conv_rhs =>
    rhs
    rhs
    erw [orderedInsertEquiv_succ]
  conv_rhs => erw [orderedInsertEquiv_fin_succ]
  ext
  simp
  let a1 : Fin ((List.orderedInsert r b (List.insertionSort r l)).length + 1) :=
    ⟨↑(orderedInsertPos r (List.orderedInsert r b (List.insertionSort r l)) a),
      orderedInsertPos_lt_length r (List.orderedInsert r b (List.insertionSort r l)) a⟩
  let b1 : Fin ((List.insertionSort r l).length + 1) :=
    ⟨↑(orderedInsertPos r (List.insertionSort r l) b),
      orderedInsertPos_lt_length r (List.insertionSort r l) b⟩
  let a2 : Fin ((List.insertionSort r l).length + 1) :=
    ⟨↑(orderedInsertPos r (List.insertionSort r l) a),
      orderedInsertPos_lt_length r (List.insertionSort r l) a⟩
  let b2 : Fin ((List.orderedInsert r a (List.insertionSort r l)).length + 1) :=
    ⟨↑(orderedInsertPos r (List.orderedInsert r a (List.insertionSort r l)) b),
      orderedInsertPos_lt_length r (List.orderedInsert r a (List.insertionSort r l)) b⟩
  have ht : (List.takeWhile (fun c => !decide (r b c)) (List.insertionSort r l))
      = (List.takeWhile (fun c => !decide (r b c))
        ((List.takeWhile (fun c => !decide (r a c)) (List.insertionSort r l)))) := by
      rw [List.takeWhile_takeWhile]
      simp
      congr
      funext c
      simp
      intro hbc hac
      refine hbc ?_
      exact IsTrans.trans _ _ _ hrba hac
  have ha1 : b1.1 ≤ a2.1 := by
    simp [a1, a2, orderedInsertPos]
    rw [ht]
    apply List.Sublist.length_le
    exact List.takeWhile_sublist fun c => !decide (r b c)
  have ha2 : a1.1 = a2.1 + 1 := by
    simp [a1, a2, orderedInsertPos]
    rw [takeWhile_orderedInsert]
    exact hr
  have hb : b1.1 = b2.1 := by
    simp [b1, b2, orderedInsertPos]
    rw [takeWhile_orderedInsert']
    exact hr
  let n := ((insertionSortEquiv r l) ⟨n, by simpa using hn⟩)
  change (a1.succAbove ⟨b1.succAbove n, _⟩).1 = (b2.succAbove ⟨a2.succAbove n, _⟩).1
  trans if (b1.succAbove n).1 < a1.1 then (b1.succAbove n).1 else (b1.succAbove n).1 + 1
  · rw [Fin.succAbove]
    simp only [Fin.castSucc_mk, Fin.lt_def, Fin.succ_mk]
    by_cases ha : (b1.succAbove n).1 < a1.1
    · simp [ha]
    · simp [ha]
  trans if (a2.succAbove n).1 < b2.1 then (a2.succAbove n).1 else (a2.succAbove n).1 + 1
  swap
  · conv_rhs => rw [Fin.succAbove]
    simp only [Fin.castSucc_mk, Fin.lt_def, Fin.succ_mk]
    by_cases ha : (a2.succAbove n).1 < b2.1
    · simp [ha]
    · simp [ha]
  have hbs1 : (b1.succAbove n).1 = if n.1 < b1.1 then n.1 else n.1 + 1 := by
    rw [Fin.succAbove]
    simp only [Fin.castSucc_mk, Fin.lt_def, Fin.succ_mk]
    by_cases ha : n.1 < b1.1
    · simp [ha]
    · simp [ha]
  have has2 : (a2.succAbove n).1 = if n.1 < a2.1 then n.1 else n.1 + 1 := by
    rw [Fin.succAbove]
    simp only [Fin.castSucc_mk, Fin.lt_def, Fin.succ_mk]
    by_cases ha : n.1 < a2.1
    · simp [ha]
    · simp [ha]
  rw [hbs1, has2, hb, ha2]
  have hnat (a2 b2 n : ℕ) (h : b2 ≤ a2) : (if (if ↑n < ↑b2 then ↑n else ↑n + 1) < ↑a2 + 1 then
      if ↑n < ↑b2 then ↑n else ↑n + 1
      else (if ↑n < ↑b2 then ↑n else ↑n + 1) + 1) =
      if (if ↑n < ↑a2 then ↑n else ↑n + 1) < ↑b2 then if ↑n < ↑a2 then ↑n else ↑n + 1
      else (if ↑n < ↑a2 then ↑n else ↑n + 1) + 1 := by
    by_cases hnb2 : n < b2
    · simp [hnb2]
      have h1 : n < a2 + 1 := by omega
      have h2 : n < a2 := by omega
      simp [h1, h2, hnb2]
    · simp [hnb2]
      by_cases ha2 : n < a2
      · simp [ha2, hnb2]
      · simp [ha2]
        rw [if_neg]
        omega
  apply hnat
  rw [← hb]
  exact ha1

lemma insertionSortEquiv_orderedInsert_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a a2 : α) : (l1 l2 : List α) →
    (insertionSortEquiv r (List.orderedInsert r a l1 ++ a2 :: l2) ⟨l1.length + 1, by
      simp⟩)
    = (finCongr (by simp; omega))
      ((insertionSortEquiv r (a :: l1 ++ a2 :: l2)) ⟨l1.length + 1, by simp⟩)
  | [], l2 => by
    simp
  | b :: l1, l2 => by
    by_cases h : r a b
    · have h1 : (List.orderedInsert r a (b :: l1) ++ a2 :: l2) = (a :: b :: l1 ++ a2 :: l2) := by
        simp [h]
      rw [insertionSortEquiv_congr _ _ h1]
      simp
    · have h1 : (List.orderedInsert r a (b :: l1) ++ a2 :: l2) =
        (b :: List.orderedInsert r a (l1) ++ a2 :: l2) := by
        simp [h]
      rw [insertionSortEquiv_congr _ _ h1]
      simp
      conv_lhs => simp [insertionSortEquiv]
      rw [insertionSortEquiv_orderedInsert_append r a]
      have hl : (List.insertionSort r (List.orderedInsert r a l1 ++ a2 :: l2)) =
        List.insertionSort r (a :: l1 ++ a2 :: l2) := by
        exact insertionSort_orderedInsert_append r a l1 (a2 :: l2)
      rw [orderedInsertEquiv_congr _ _ _ hl]
      simp
      change Fin.cast _
        ((insertionSortEquiv r (b :: a :: (l1 ++ a2 :: l2))) ⟨l1.length + 2, by simp⟩) = _
      have hl : l1.length + 1 +1 = l1.length + 2 := by omega
      simp [hl]
      conv_rhs =>
        erw [insertionSortEquiv_commute _ _ _ h _ _]
      simp

lemma insertionSortEquiv_insertionSort_append {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) : (l1 l2 : List α) →
    (insertionSortEquiv r (List.insertionSort r l1 ++ a :: l2) ⟨l1.length, by simp⟩)
    = finCongr (by simp) (insertionSortEquiv r (l1 ++ a :: l2) ⟨l1.length, by simp⟩)
  | [], l2 => by
    simp
  | b :: l1, l2 => by
    simp
    have hl := insertionSortEquiv_orderedInsert_append r b a (List.insertionSort r l1) l2
    simp at hl
    rw [hl]
    have ih := insertionSortEquiv_insertionSort_append r a l1 l2
    simp [insertionSortEquiv]
    rw [ih]
    have hl : (List.insertionSort r (List.insertionSort r l1 ++ a :: l2)) =
        (List.insertionSort r (l1 ++ a :: l2)) := by
      exact insertionSort_insertionSort_append r l1 (a :: l2)
    rw [orderedInsertEquiv_congr _ _ _ hl]
    simp

/-!

## Insertion sort with equal fields

-/

lemma orderedInsert_filter_of_pos {α : Type} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] (a : α) (p : α → Prop) [DecidablePred p] (h : p a) : (l : List α) →
    (hl : l.Sorted r) →
    List.filter p (List.orderedInsert r a l) = List.orderedInsert r a (List.filter p l)
  | [], hl => by
    simp
    exact h
  | b :: l, hl => by
    simp
    by_cases hpb : p b <;> by_cases hab : r a b
    · simp [hpb, hab]
      rw [List.filter_cons_of_pos (by simp [h])]
      rw [List.filter_cons_of_pos (by simp [hpb])]
    · simp [hab]
      rw [List.filter_cons_of_pos (by simp [hpb])]
      rw [List.filter_cons_of_pos (by simp [hpb])]
      simp [hab]
      simp at hl
      exact orderedInsert_filter_of_pos r a p h l hl.2
    · simp [hab]
      rw [List.filter_cons_of_pos (by simp [h]),
        List.filter_cons_of_neg (by simp [hpb])]
      rw [List.orderedInsert_eq_take_drop]
      have hl : List.takeWhile (fun b => decide ¬r a b)
          (List.filter (fun b => decide (p b)) l) = [] := by
        rw [List.takeWhile_eq_nil_iff]
        intro c hc
        simp at hc
        apply hc
        apply IsTrans.trans a b _ hab
        simp at hl
        apply hl.1
        have hlf : (List.filter (fun b => decide (p b)) l)[0] ∈
            (List.filter (fun b => decide (p b)) l) := by
          exact List.getElem_mem c
        simp [- List.getElem_mem] at hlf
        exact hlf.1
      rw [hl]
      simp
      conv_lhs => rw [← List.takeWhile_append_dropWhile (fun b => decide ¬r a b)
        (List.filter (fun b => decide (p b)) l)]
      rw [hl]
      simp
    · simp [hab]
      rw [List.filter_cons_of_neg (by simp [hpb])]
      rw [List.filter_cons_of_neg (by simp [hpb])]
      simp at hl
      exact orderedInsert_filter_of_pos r a p h l hl.2

lemma orderedInsert_filter_of_neg {α : Type} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] (a : α) (p : α → Prop) [DecidablePred p] (h : ¬ p a) (l : List α) :
    List.filter p (List.orderedInsert r a l) = (List.filter p l) := by
  rw [List.orderedInsert_eq_take_drop]
  simp
  rw [List.filter_cons_of_neg]
  rw [← List.filter_append]
  congr
  exact List.takeWhile_append_dropWhile (fun b => !decide (r a b)) l
  simp [h]

lemma insertionSort_filter {α : Type} (r : α → α → Prop) [DecidableRel r] [IsTotal α r]
    [IsTrans α r] (p : α → Prop) [DecidablePred p] : (l : List α) →
    List.insertionSort r (List.filter p l) =
    List.filter p (List.insertionSort r l)
  | [] => by simp
  | a :: l => by
    simp
    by_cases h : p a
    · rw [orderedInsert_filter_of_pos]
      rw [List.filter_cons_of_pos]
      simp
      rw [insertionSort_filter]
      simp_all
      simp_all
      exact List.sorted_insertionSort r l
    · rw [orderedInsert_filter_of_neg]
      rw [List.filter_cons_of_neg]
      rw [insertionSort_filter]
      simp_all
      exact h

lemma takeWhile_sorted_eq_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) : (l : List α) → (hl : l.Sorted r) →
    List.takeWhile (fun c => ¬ r a c) l = List.filter (fun c => ¬ r a c) l
  | [], _ => by simp
  | b :: l, hl => by
    simp at hl
    by_cases hb : ¬ r a b
    · simp [hb]
      simpa using takeWhile_sorted_eq_filter r a l hl.2
    · simp_all
      intro c hc
      apply IsTrans.trans a b c hb
      exact hl.1 c hc

lemma dropWhile_sorted_eq_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) : (l : List α) → (hl : l.Sorted r) →
    List.dropWhile (fun c => ¬ r a c) l = List.filter (fun c => r a c) l
  | [], _ => by simp
  | b :: l, hl => by
    simp at hl
    by_cases hb : ¬ r a b
    · simp [hb]
      simpa using dropWhile_sorted_eq_filter r a l hl.2
    · simp_all
      symm
      rw [List.filter_eq_self]
      intro c hc
      simp
      apply IsTrans.trans a b c hb
      exact hl.1 c hc

lemma dropWhile_sorted_eq_filter_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) :(l : List α) → (hl : l.Sorted r) →
    List.filter (fun c => r a c) l =
    List.filter (fun c => r a c ∧ r c a) l ++ List.filter (fun c => r a c ∧ ¬ r c a) l
  | [], _ => by
    simp
  | b :: l, hl => by
    simp at hl
    by_cases hb : ¬ r a b
    · simp [hb]
      simpa using dropWhile_sorted_eq_filter_filter r a l hl.2
    · simp_all
      by_cases hba : r b a
      · simp [hba]
        rw [List.filter_cons_of_pos]
        rw [dropWhile_sorted_eq_filter_filter]
        simp
        exact hl.2
        simp_all
      · simp[hba]
        have h1 : List.filter (fun c => decide (r a c) && decide (r c a)) l = [] := by
          rw [@List.filter_eq_nil_iff]
          intro c hc
          simp
          intro hac hca
          apply hba
          apply IsTrans.trans b c a _ hca
          exact hl.1 c hc
        rw [h1]
        rw [dropWhile_sorted_eq_filter_filter]
        simp [h1]
        rw [List.filter_cons_of_pos]
        simp_all
        exact hl.2

lemma filter_rel_eq_insertionSort {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) : (l : List α) →
    List.filter (fun c => r a c ∧ r c a) (l.insertionSort r) =
    List.filter (fun c => r a c ∧ r c a) l
  | [] => by simp
  | b :: l => by
    simp only [List.insertionSort]
    by_cases h : r a b ∧ r b a
    · have hl := orderedInsert_filter_of_pos r b (fun c => r a c ∧ r c a) h
        (List.insertionSort r l) (by exact List.sorted_insertionSort r l)
      simp at hl ⊢
      rw [hl]
      rw [List.orderedInsert_eq_take_drop]
      have ht : List.takeWhile (fun b_1 => decide ¬r b b_1)
        (List.filter (fun b => decide (r a b) && decide (r b a))
          (List.insertionSort r l)) = [] := by
        rw [List.takeWhile_eq_nil_iff]
        intro hl
        simp
        have hx := List.getElem_mem hl
        simp [- List.getElem_mem] at hx
        apply IsTrans.trans b a _ h.2
        simp_all
      rw [ht]
      simp
      rw [List.filter_cons_of_pos]
      simp
      have ih := filter_rel_eq_insertionSort r a l
      simp at ih
      rw [← ih]
      have htd := List.takeWhile_append_dropWhile (fun b_1 => decide ¬r b b_1)
        (List.filter (fun b => decide (r a b) && decide (r b a)) (List.insertionSort r l))
      simp [decide_not, - List.takeWhile_append_dropWhile] at htd
      conv_rhs => rw [← htd]
      simp [- List.takeWhile_append_dropWhile]
      intro hl
      have hx := List.getElem_mem hl
      simp [- List.getElem_mem] at hx
      apply IsTrans.trans b a _ h.2
      simp_all
      simp_all
    · have hl := orderedInsert_filter_of_neg r b (fun c => r a c ∧ r c a) h (List.insertionSort r l)
      simp at hl ⊢
      rw [hl]
      rw [List.filter_cons_of_neg]
      have ih := filter_rel_eq_insertionSort r a l
      simp_all
      simpa using h

lemma insertionSort_of_eq_list {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l1 l l2 : List α)
    (h : ∀ b ∈ l, r a b ∧ r b a) :
    List.insertionSort r (l1 ++ l ++ l2) =
    (List.takeWhile (fun c => ¬ r a c) ((l1 ++ l2).insertionSort r))
    ++ (List.filter (fun c => r a c ∧ r c a) l1)
    ++ l
    ++ (List.filter (fun c => r a c ∧ r c a) l2)
    ++ (List.filter (fun c => r a c ∧ ¬ r c a) ((l1 ++ l2).insertionSort r))
    := by
  have hl : List.insertionSort r (l1 ++ l ++ l2) =
    List.takeWhile (fun c => ¬ r a c) ((l1 ++ l ++ l2).insertionSort r) ++
    List.dropWhile (fun c => ¬ r a c) ((l1 ++ l ++ l2).insertionSort r) := by
    exact (List.takeWhile_append_dropWhile (fun c => decide ¬r a c)
          (List.insertionSort r (l1 ++ l ++ l2))).symm
  have hlt : List.takeWhile (fun c => ¬ r a c) ((l1 ++ l ++ l2).insertionSort r)
      = List.takeWhile (fun c => ¬ r a c) ((l1 ++ l2).insertionSort r) := by
    rw [takeWhile_sorted_eq_filter, takeWhile_sorted_eq_filter]
    rw [← insertionSort_filter, ← insertionSort_filter]
    congr 1
    simp
    exact fun b hb => (h b hb).1
    exact List.sorted_insertionSort r (l1 ++ l2)
    exact List.sorted_insertionSort r (l1 ++ l ++ l2)
  conv_lhs => rw [hl, hlt]
  simp only [decide_not, Bool.decide_and]
  simp
  have h1 := dropWhile_sorted_eq_filter r a (List.insertionSort r (l1 ++ (l ++ l2)))
  simp at h1
  rw [h1]
  rw [dropWhile_sorted_eq_filter_filter, filter_rel_eq_insertionSort]
  simp
  congr 1
  simp
  exact fun a a_1 => h a a_1
  congr 1
  have h1 := insertionSort_filter r (fun c => decide (r a c) && !decide (r c a)) (l1 ++ (l ++ l2))
  simp at h1
  rw [← h1]
  have h2 := insertionSort_filter r (fun c => decide (r a c) && !decide (r c a)) (l1 ++ l2)
  simp at h2
  rw [← h2]
  congr
  have hl : List.filter (fun b => decide (r a b) && !decide (r b a)) l = [] := by
    rw [@List.filter_eq_nil_iff]
    intro c hc
    simp_all
  rw [hl]
  simp
  exact List.sorted_insertionSort r (l1 ++ (l ++ l2))
  exact List.sorted_insertionSort r (l1 ++ (l ++ l2))

lemma insertionSort_of_takeWhile_filter {α : Type} (r : α → α → Prop) [DecidableRel r]
    [IsTotal α r] [IsTrans α r] (a : α) (l1 l2 : List α) :
    List.insertionSort r (l1 ++ l2) =
    (List.takeWhile (fun c => ¬ r a c) ((l1 ++ l2).insertionSort r))
    ++ (List.filter (fun c => r a c ∧ r c a) l1)
    ++ (List.filter (fun c => r a c ∧ r c a) l2)
    ++ (List.filter (fun c => r a c ∧ ¬ r c a) ((l1 ++ l2).insertionSort r))
    := by
  trans List.insertionSort r (l1 ++ [] ++ l2)
  simp
  rw [insertionSort_of_eq_list r a l1 [] l2]
  simp
  simp

end HepLean.List
