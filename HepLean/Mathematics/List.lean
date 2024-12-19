/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import HepLean.Mathematics.Fin
/-!
# List lemmas

-/
namespace HepLean.List

open Fin
open HepLean
variable {n : Nat}


lemma takeWile_eraseIdx {I : Type} (P : I → Prop) [DecidablePred P]  :
    (l : List I) → (i : ℕ) → (hi : ∀ (i j : Fin l.length), i < j → P (l.get j) → P (l.get i)) →
    List.takeWhile P (List.eraseIdx l i) = (List.takeWhile P l).eraseIdx i
  | [], _, h => by
    simp
  | a :: [], 0, h => by
    simp [List.takeWhile]
    split
    next x heq => simp_all only [decide_eq_true_eq, List.tail_cons]
    next x heq => simp_all only [decide_eq_false_iff_not, List.tail_nil]
  | a :: [], Nat.succ n , h => by
    simp
    rw [List.eraseIdx_of_length_le ]
    have h1 : (List.takeWhile P [a]).length ≤ [a].length :=
        List.Sublist.length_le (List.takeWhile_sublist _)
    simp at h1
    omega
  | a :: b :: l, 0, h => by
    simp [List.takeWhile]
    by_cases hPb : P b
    · have hPa : P a := by
        simpa using h ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp [Fin.lt_def]) (by simpa using hPb)
      simp [hPb, hPa]
    · simp [hPb]
      simp_all only [List.length_cons, List.get_eq_getElem]
      split
      next x heq => simp_all only [decide_eq_true_eq, List.tail_cons]
      next x heq => simp_all only [decide_eq_false_iff_not, List.tail_nil]
  | a :: b :: l, Nat.succ n, h => by
    simp
    by_cases hPa : P a
    · dsimp [List.takeWhile]
      simp [hPa]
      rw [takeWile_eraseIdx]
      rfl
      intro i j hij hP
      simpa using  h (Fin.succ i) (Fin.succ j) (by simpa using hij) (by simpa using hP)
    · simp [hPa]


lemma dropWile_eraseIdx {I : Type} (P : I → Prop) [DecidablePred P]  :
    (l : List I) → (i : ℕ) → (hi : ∀ (i j : Fin l.length), i < j → P (l.get j) → P (l.get i)) →
    List.dropWhile P (List.eraseIdx l i) =
      if (List.takeWhile P l).length ≤  i then
        (List.dropWhile P l).eraseIdx (i - (List.takeWhile P l).length)
      else (List.dropWhile P l)
  | [], _, h => by
    simp
  | a :: [], 0, h => by
    simp [List.dropWhile]
    simp_all only [List.length_singleton, List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero, implies_true,
      decide_True, decide_False, List.tail_cons, ite_self]
  | a :: [], Nat.succ n , h => by
    simp [List.dropWhile, List.takeWhile]
    rw [List.eraseIdx_of_length_le ]
    simp_all only [List.length_singleton, List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero, implies_true,
      ite_self]
    simp_all only [List.length_singleton, List.get_eq_getElem, Fin.val_eq_zero, List.getElem_cons_zero, implies_true]
    split
    next x heq =>
      simp_all only [decide_eq_true_eq, List.length_nil, List.length_singleton, add_tsub_cancel_right, zero_le]
    next x heq =>
      simp_all only [decide_eq_false_iff_not, List.length_singleton, List.length_nil, tsub_zero,
        le_add_iff_nonneg_left, zero_le]
  | a :: b :: l, 0, h => by
    simp [List.takeWhile, List.dropWhile]
    by_cases hPb : P b
    · have hPa : P a := by
        simpa using h ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp [Fin.lt_def]) (by simpa using hPb)
      simp [hPb, hPa]
    · simp [hPb]
      simp_all only [List.length_cons, List.get_eq_getElem]
      simp_all only [decide_False, nonpos_iff_eq_zero, List.length_eq_zero]
      split
      next h_1 =>
        simp_all only [nonpos_iff_eq_zero, List.length_eq_zero]
        split
        next x heq => simp_all only [List.cons_ne_self]
        next x heq => simp_all only [decide_eq_false_iff_not, List.tail_cons]
      next h_1 =>
        simp_all only [nonpos_iff_eq_zero, List.length_eq_zero]
        split
        next x heq => simp_all only [List.cons_ne_self, not_false_eq_true, decide_eq_true_eq]
        next x heq => simp_all only [not_true_eq_false]
  | a :: b :: l, Nat.succ n, h => by
    simp
    by_cases hPb : P b
    · have hPa : P a := by
        simpa using h ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp [Fin.lt_def]) (by simpa using hPb)
      simp [List.takeWhile, List.dropWhile, hPb, hPa]
      rw [dropWile_eraseIdx]
      simp_all only [List.length_cons, List.get_eq_getElem, decide_True, List.takeWhile_cons_of_pos,
        List.dropWhile_cons_of_pos]
      intro i j  hij hP
      simpa using  h (Fin.succ i) (Fin.succ j) (by simpa using hij) (by simpa using hP)
    · simp [List.takeWhile, List.dropWhile, hPb]
      by_cases hPa : P a
      · rw [dropWile_eraseIdx]
        simp [hPa, List.dropWhile, hPb]
        intro i j hij hP
        simpa using  h (Fin.succ i) (Fin.succ j) (by simpa using hij) (by simpa using hP)
      · simp [hPa]

def orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    Fin (List.orderedInsert le1 r0 r).length :=
  ⟨(List.takeWhile (fun b => decide ¬ le1 r0 b) r).length, by
    rw [List.orderedInsert_length]
    have h1 : (List.takeWhile (fun b => decide ¬le1 r0 b) r).length ≤ r.length :=
      List.Sublist.length_le (List.takeWhile_sublist fun b => decide ¬le1 r0 b)
    omega⟩

lemma orderedInsertPos_lt_length {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) : orderedInsertPos le1 r r0 < (r0 :: r).length := by
  simp only [orderedInsertPos, List.length_cons]
  have h1 : (List.takeWhile (fun b => decide ¬le1 r0 b) r).length ≤ r.length :=
    List.Sublist.length_le (List.takeWhile_sublist fun b => decide ¬le1 r0 b)
  omega

@[simp]
lemma orderedInsert_get_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r)[(orderedInsertPos le1 r r0).val] = r0 := by
  simp [orderedInsertPos, List.orderedInsert_eq_take_drop]
  rw [List.getElem_append]
  simp

@[simp]
lemma orderedInsert_eraseIdx_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r).eraseIdx ↑(orderedInsertPos le1 r r0) = r  := by
  simp only [List.orderedInsert_eq_take_drop]
  rw [List.eraseIdx_append_of_length_le]
  · simp [orderedInsertPos]
  · simp [orderedInsertPos]

lemma orderedInsertPos_cons  {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 r1 : I) :
    (orderedInsertPos le1 (r1 ::r) r0).val =
    if le1 r0 r1 then ⟨0, by simp⟩ else (Fin.succ (orderedInsertPos le1 r r0)) := by
  simp [orderedInsertPos, List.takeWhile]
  by_cases h : le1 r0 r1
  · simp [h]
  · simp [h]


lemma orderedInsertPos_sigma {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (le1 : I → I → Prop) [DecidableRel le1] (l : List (Σ i, f i))
    (k : I) (a :  f k)  :
    (orderedInsertPos (fun (i j : Σ i, f i) => le1 i.1 j.1) l ⟨k, a⟩).1 =
    (orderedInsertPos le1 (List.map (fun (i : Σ i, f i) => i.1) l) k).1 := by
  simp [orderedInsertPos]
  induction l with
  | nil =>
    simp
  | cons a l ih =>
    simp [List.takeWhile]
    obtain ⟨fst, snd⟩ := a
    simp_all only
    split
    next x heq =>
      simp_all only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, List.length_cons, decide_False,
        Bool.not_false]
    next x heq =>
      simp_all only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq, List.length_nil, decide_True,
        Bool.not_true]

@[simp]
lemma orderedInsert_get_lt {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : ℕ)
    (hi : i < orderedInsertPos le1 r r0) :
    (List.orderedInsert le1 r0 r)[i] = r.get ⟨i, by
      simp only [orderedInsertPos] at hi
      have h1 : (List.takeWhile (fun b => decide ¬le1 r0 b) r).length ≤ r.length :=
        List.Sublist.length_le (List.takeWhile_sublist fun b => decide ¬le1 r0 b)
      omega⟩ := by
  simp [orderedInsertPos] at hi
  simp [List.orderedInsert_eq_take_drop]
  rw [List.getElem_append]
  simp [hi]
  rw [List.IsPrefix.getElem]
  exact List.takeWhile_prefix fun b => !decide (le1 r0 b)

lemma orderedInsertPos_take_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.take (orderedInsertPos le1 r r0) (List.orderedInsert le1 r0 r)) =
    List.takeWhile (fun b => decide ¬le1 r0 b) r := by
  simp [orderedInsertPos, List.orderedInsert_eq_take_drop]


lemma orderedInsertPos_take_eq_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.take (orderedInsertPos le1 r r0) r =
    List.take (orderedInsertPos le1 r r0) (List.orderedInsert le1 r0 r) := by
  refine List.ext_get ?_  ?_
  · simp
    exact Nat.le_of_lt_succ (orderedInsertPos_lt_length le1 r r0 )
  · intro n h1 h2
    simp
    erw [orderedInsert_get_lt le1 r r0 n]
    rfl
    simp at h1
    exact h1.1

lemma orderedInsertPos_drop_eq_orderedInsert {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.drop (orderedInsertPos le1 r r0) r =
    List.drop (orderedInsertPos le1 r r0).succ (List.orderedInsert le1 r0 r) := by
  conv_rhs => simp [orderedInsertPos, List.orderedInsert_eq_take_drop]
  have hr : r = List.takeWhile (fun b => !decide (le1 r0 b)) r ++ List.dropWhile (fun b => !decide (le1 r0 b)) r := by
    exact Eq.symm (List.takeWhile_append_dropWhile (fun b => !decide (le1 r0 b)) r)
  conv_lhs =>
    rhs
    rw [hr]
  rw [List.drop_append_eq_append_drop]
  simp [orderedInsertPos]

lemma orderedInsertPos_take {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.take (orderedInsertPos le1 r r0) r = List.takeWhile (fun b => decide ¬le1 r0 b) r := by
  rw [orderedInsertPos_take_eq_orderedInsert]
  rw [orderedInsertPos_take_orderedInsert]

lemma orderedInsertPos_drop {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.drop (orderedInsertPos le1 r r0) r = List.dropWhile (fun b => decide ¬le1 r0 b) r := by
  rw [orderedInsertPos_drop_eq_orderedInsert]
  simp [orderedInsertPos, List.orderedInsert_eq_take_drop]

lemma orderedInsertPos_succ_take_orderedInsert  {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.take (orderedInsertPos le1 r r0).succ (List.orderedInsert le1 r0 r)) =
     List.takeWhile (fun b => decide ¬le1 r0 b) r ++ [r0] := by
  simp [orderedInsertPos, List.orderedInsert_eq_take_drop, List.take_append_eq_append_take]

lemma lt_orderedInsertPos_rel {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r0 : I)  (r : List I) (n : Fin r.length)
    (hn : n.val < (orderedInsertPos le1 r r0).val) : ¬ le1 r0 (r.get n) := by
  have htake : r.get n ∈ List.take (orderedInsertPos le1 r r0) r := by
    rw [@List.mem_take_iff_getElem]
    use n
    simp
    exact hn
  rw [orderedInsertPos_take] at htake
  have htake' := List.mem_takeWhile_imp htake
  simpa using htake'

lemma gt_orderedInsertPos_rel {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    [IsTotal I le1] [IsTrans I le1] (r0 : I)  (r : List I) (hs : List.Sorted le1 r) (n : Fin r.length)
    (hn : ¬ n.val < (orderedInsertPos le1 r r0).val) : le1 r0 (r.get n) := by
  have hrsSorted : List.Sorted le1 (List.orderedInsert le1 r0 r) :=
    List.Sorted.orderedInsert r0 r hs
  apply List.Sorted.rel_of_mem_take_of_mem_drop (k := (orderedInsertPos le1 r r0).succ) hrsSorted
  · rw [orderedInsertPos_succ_take_orderedInsert]
    simp
  · rw [← orderedInsertPos_drop_eq_orderedInsert]
    refine List.mem_drop_iff_getElem.mpr ?hy.a
    use n - (orderedInsertPos le1 r r0).val
    have hn : ↑n - ↑(orderedInsertPos le1 r r0) + ↑(orderedInsertPos le1 r r0) < r.length := by
      omega
    use hn
    congr
    omega


lemma orderedInsert_eraseIdx_lt_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : ℕ)
    (hi : i < orderedInsertPos le1 r r0)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx i = List.orderedInsert le1 r0 (r.eraseIdx i) := by
  conv_lhs => simp only [List.orderedInsert_eq_take_drop]
  rw [List.eraseIdx_append_of_lt_length]
  · simp only [List.orderedInsert_eq_take_drop]
    congr 1
    · rw [takeWile_eraseIdx]
      exact hr
    · rw [dropWile_eraseIdx]
      simp [orderedInsertPos] at hi
      have hi' : ¬ (List.takeWhile (fun b => !decide (le1 r0 b)) r).length ≤ ↑i := by
        omega
      simp [hi']
      exact fun i j a a_1 => hr i j a a_1
  · exact hi

lemma orderedInsert_eraseIdx_orderedInsertPos_le {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : ℕ)
    (hi : orderedInsertPos le1 r r0 ≤ i)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx (Nat.succ i) = List.orderedInsert le1 r0 (r.eraseIdx i) := by
  conv_lhs => simp only [List.orderedInsert_eq_take_drop]
  rw [List.eraseIdx_append_of_length_le]
  · simp only [List.orderedInsert_eq_take_drop]
    congr 1
    · rw [takeWile_eraseIdx]
      rw [List.eraseIdx_of_length_le]
      simp [orderedInsertPos] at hi
      simp
      omega
      exact hr
    · simp only [Nat.succ_eq_add_one]
      have hn : (i + 1 - (List.takeWhile (fun b => (decide (¬ le1 r0 b))) r).length)
        = (i - (List.takeWhile (fun b => decide (¬ le1 r0 b)) r).length) + 1 := by
        simp only [orderedInsertPos] at hi
        omega
      rw [hn]
      simp only [List.eraseIdx_cons_succ, List.cons.injEq, true_and]
      rw [dropWile_eraseIdx]
      rw [if_pos]
      · simp only [orderedInsertPos] at hi
        omega
      · exact hr
  · simp only [orderedInsertPos] at hi
    omega

def orderedInsertEquiv  {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    Fin (r0 :: r).length ≃ Fin (List.orderedInsert le1 r0 r).length := by
  let e2 : Fin (List.orderedInsert le1 r0 r).length ≃ Fin (r0 :: r).length :=
    (Fin.castOrderIso (List.orderedInsert_length le1 r r0)).toEquiv
  let e3 : Fin (r0 :: r).length ≃ Fin 1 ⊕ Fin (r).length := finExtractOne 0
  let e4 : Fin (r0 :: r).length ≃ Fin 1 ⊕ Fin (r).length := finExtractOne ⟨orderedInsertPos le1 r r0, orderedInsertPos_lt_length le1 r r0⟩
  exact e3.trans (e4.symm.trans e2.symm)

@[simp]
lemma orderedInsertEquiv_zero {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) : orderedInsertEquiv le1 r r0 ⟨0, by simp⟩ = orderedInsertPos le1 r r0 := by
  simp [orderedInsertEquiv]

@[simp]
lemma orderedInsertEquiv_succ {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) (n : ℕ) (hn : Nat.succ n < (r0 :: r).length) :
    orderedInsertEquiv le1 r r0 ⟨Nat.succ n, hn⟩ = Fin.cast (List.orderedInsert_length le1 r r0).symm
    ((Fin.succAbove ⟨(orderedInsertPos le1 r r0), orderedInsertPos_lt_length le1 r r0⟩) ⟨n, Nat.succ_lt_succ_iff.mp hn⟩) := by
  simp [orderedInsertEquiv]
  match r with
  | [] =>
    simp
  | r1 :: r =>
    erw [finExtractOne_apply_neq]
    simp [orderedInsertPos]
    rfl
    exact ne_of_beq_false rfl

@[simp]
lemma orderedInsertEquiv_fin_succ {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) (n : Fin r.length)  :
    orderedInsertEquiv le1 r r0 n.succ = Fin.cast (List.orderedInsert_length le1 r r0).symm
    ((Fin.succAbove ⟨(orderedInsertPos le1 r r0), orderedInsertPos_lt_length le1 r r0⟩) ⟨n, n.isLt⟩) := by
  simp [orderedInsertEquiv]
  match r with
  | [] =>
    simp
  | r1 :: r =>
    erw [finExtractOne_apply_neq]
    simp [orderedInsertPos]
    rfl
    exact ne_of_beq_false rfl

lemma orderedInsertEquiv_congr {α : Type} {r : α → α → Prop} [DecidableRel r] (a : α) (l l' : List α)
    (h : l = l') : orderedInsertEquiv r l a = (Fin.castOrderIso (by simp [h])).toEquiv.trans
    ((orderedInsertEquiv r l' a).trans (Fin.castOrderIso (by simp [h])).toEquiv) := by
  subst h
  rfl

lemma get_eq_orderedInsertEquiv {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) :
    (r0 :: r).get = (List.orderedInsert le1 r0 r).get ∘ (orderedInsertEquiv le1 r r0) := by
  funext x
  match x with
  | ⟨0, h⟩ =>
    simp
    erw [orderedInsertEquiv_zero]
    simp
  | ⟨Nat.succ n, h⟩ =>
    simp
    erw [orderedInsertEquiv_succ]
    simp [Fin.succAbove]
    by_cases hn : n < ↑(orderedInsertPos le1 r r0)
    · simp [hn]
    · simp [hn]
      simp [List.orderedInsert_eq_take_drop]
      rw [List.getElem_append]
      have hn' : ¬ n + 1 < (List.takeWhile (fun b => !decide (le1 r0 b)) r).length := by
        simp [orderedInsertPos]  at hn
        omega
      simp [hn']
      have hnn : n + 1 - (List.takeWhile (fun b => !decide (le1 r0 b)) r).length =
        (n - (List.takeWhile (fun b => !decide (le1 r0 b)) r).length) + 1 := by
        simp [orderedInsertPos]  at hn
        omega
      simp [hnn]
      conv_rhs =>
        rw [List.IsSuffix.getElem (List.dropWhile_suffix fun b => !decide (le1 r0 b))]
      congr
      have hr : r.length = (List.takeWhile (fun b => !decide (le1 r0 b)) r).length +  (List.dropWhile (fun b => !decide (le1 r0 b)) r).length := by
        rw [← List.length_append]
        congr
        exact Eq.symm (List.takeWhile_append_dropWhile (fun b => !decide (le1 r0 b)) r)
      simp [hr]
      omega

lemma orderedInsertEquiv_get {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) :
    (r0 :: r).get ∘ (orderedInsertEquiv le1 r r0).symm = (List.orderedInsert le1 r0 r).get := by
  rw [get_eq_orderedInsertEquiv le1]
  funext x
  simp


lemma orderedInsert_eraseIdx_orderedInsertEquiv_zero
    {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r).eraseIdx (orderedInsertEquiv le1 r r0 ⟨0, by simp⟩) = r := by
  simp [orderedInsertEquiv]

lemma orderedInsert_eraseIdx_orderedInsertEquiv_succ
    {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) (n : ℕ) (hn : Nat.succ n < (r0 :: r).length)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx (orderedInsertEquiv le1 r r0 ⟨Nat.succ n, hn⟩) =
    (List.orderedInsert le1 r0 (r.eraseIdx n)) := by
  induction r with
  | nil =>
    simp at hn
  | cons r1 r ih =>
    rw [orderedInsertEquiv_succ]
    simp only [List.length_cons, Fin.succAbove,
      Fin.castSucc_mk, Fin.mk_lt_mk, Fin.succ_mk, Fin.coe_cast]
    by_cases hn' : n < (orderedInsertPos le1 (r1 :: r) r0)
    · simp only [hn', ↓reduceIte]
      rw [orderedInsert_eraseIdx_lt_orderedInsertPos le1 (r1 :: r) r0 n hn' hr]
    · simp only [hn', ↓reduceIte]
      rw [orderedInsert_eraseIdx_orderedInsertPos_le le1 (r1 :: r) r0 n _ hr]
      omega

lemma orderedInsert_eraseIdx_orderedInsertEquiv_fin_succ
    {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) (n : Fin r.length)
    (hr : ∀ (i j : Fin r.length), i < j → ¬le1 r0 (r.get j) → ¬le1 r0 (r.get i)) :
    (List.orderedInsert le1 r0 r).eraseIdx (orderedInsertEquiv le1 r r0 n.succ) =
    (List.orderedInsert le1 r0 (r.eraseIdx n)) := by
  have hn : n.succ = ⟨n.val + 1, by omega⟩ := by
    rw [Fin.ext_iff]
    simp
  rw [hn]
  exact orderedInsert_eraseIdx_orderedInsertEquiv_succ le1 r r0 n.val _ hr

lemma orderedInsertEquiv_sigma {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (le1 : I → I → Prop) [DecidableRel le1] (l : List (Σ i, f i))
    (i : I) (a :  f i)  :
    (orderedInsertEquiv  (fun i j => le1 i.fst j.fst) l ⟨i, a⟩) =
    (Fin.castOrderIso (by simp)).toEquiv.trans
    ((orderedInsertEquiv le1 (List.map (fun i => i.1) l) i).trans
    (Fin.castOrderIso (by simp [List.orderedInsert_length])).toEquiv) := by
  ext x
  match x with
  | ⟨0, h0⟩ =>
    simp
    erw [orderedInsertEquiv_zero, orderedInsertEquiv_zero]
    simp [orderedInsertPos_sigma]
  | ⟨Nat.succ n, h0⟩ =>
    simp
    erw [orderedInsertEquiv_succ, orderedInsertEquiv_succ]
    simp [orderedInsertPos_sigma]
    rw [Fin.succAbove, Fin.succAbove]
    simp
    split
    next h => simp_all only
    next h => simp_all only [not_lt]


lemma orderedInsert_eq_insertIdx_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    List.orderedInsert le1 r0 r = List.insertIdx (orderedInsertPos le1 r r0).1 r0 r  := by
  apply List.ext_get
  · simp [List.orderedInsert_length]
    rw [List.length_insertIdx]
    have h1 := orderedInsertPos_lt_length le1 r r0
    simp at h1
    omega
  intro n h1 h2
  obtain ⟨n', hn'⟩ := (orderedInsertEquiv le1 r r0).surjective ⟨n, h1⟩
  rw [← hn']
  have hn'' : n = ((orderedInsertEquiv le1 r r0) n').val := by rw [hn']
  subst hn''
  rw [← orderedInsertEquiv_get]
  simp
  match n' with
  | ⟨0, h0⟩ =>
    simp
    simp [orderedInsertEquiv]
    rw [List.getElem_insertIdx_self]
    exact Nat.le_of_lt_succ (orderedInsertPos_lt_length le1 r r0)
  | ⟨Nat.succ n', h0⟩ =>
    simp
    have hr := orderedInsertEquiv_succ le1 r r0 n' h0
    trans (List.insertIdx (↑(orderedInsertPos le1 r r0)) r0 r).get ⟨↑((orderedInsertEquiv le1 r r0) ⟨n' +1, h0⟩), h2⟩
    swap
    rfl
    rw [Fin.ext_iff] at hr
    have hx :  (⟨↑((orderedInsertEquiv le1 r r0) ⟨n' +1, h0⟩), h2⟩ :Fin (List.insertIdx (↑(orderedInsertPos le1 r r0)) r0 r).length) =
       ⟨(
        (⟨↑(orderedInsertPos le1 r r0), orderedInsertPos_lt_length le1 r r0⟩ : Fin ((r).length + 1))).succAbove ⟨n',  Nat.succ_lt_succ_iff.mp h0⟩, by
          erw [← hr]
          exact h2
          ⟩ := by
      rw [Fin.ext_iff]
      simp
      simpa using hr
    rw [hx]
    simp [Fin.succAbove]
    by_cases hn' : n' < ↑(orderedInsertPos le1 r r0)
    · simp [hn']
      erw [List.getElem_insertIdx_of_lt]
      exact hn'
    · simp [hn']
      sorry

/-- The equivalence between `Fin l.length ≃ Fin (List.insertionSort r l).length` induced by the
  sorting algorithm. -/
def insertionSortEquiv {α : Type} (r : α → α → Prop) [DecidableRel r] : (l : List α) →
    Fin l.length ≃ Fin (List.insertionSort r l).length
  | [] => Equiv.refl _
  | a :: l =>
    (Fin.equivCons (insertionSortEquiv r l)).trans (orderedInsertEquiv r (List.insertionSort r l) a)

lemma insertionSortEquiv_get {α : Type} {r : α → α → Prop} [DecidableRel r] : (l : List α) →
    l.get ∘ (insertionSortEquiv r l).symm = (List.insertionSort r l).get
  | [] => by
    simp [insertionSortEquiv]
  | a :: l => by
    rw [insertionSortEquiv]
    change ((a :: l).get ∘ ((Fin.equivCons (insertionSortEquiv r l))).symm) ∘
      (orderedInsertEquiv r (List.insertionSort r l) a).symm = _
    have hl : (a :: l).get ∘ ((Fin.equivCons (insertionSortEquiv r l))).symm =
        (a :: List.insertionSort r l).get := by
      ext x
      match x with
      | ⟨0, h⟩ => rfl
      | ⟨Nat.succ x, h⟩ =>
        change _ = (List.insertionSort r l).get _
        rw [← insertionSortEquiv_get (r := r) l]
        rfl
    rw [hl]
    rw [orderedInsertEquiv_get r (List.insertionSort r l) a]
    rfl

lemma insertionSortEquiv_congr {α : Type} {r : α → α → Prop} [DecidableRel r] (l l' : List α)
    (h : l = l') : insertionSortEquiv r l = (Fin.castOrderIso (by simp [h])).toEquiv.trans
      ((insertionSortEquiv r l').trans (Fin.castOrderIso (by simp [h])).toEquiv) := by
  subst h
  rfl
lemma insertionSort_get_comp_insertionSortEquiv  {α : Type} {r : α → α → Prop} [DecidableRel r] (l : List α)  :
    (List.insertionSort r l).get ∘ (insertionSortEquiv r l) = l.get := by
  rw [← insertionSortEquiv_get]
  funext x
  simp

lemma insertionSort_eq_ofFn {α : Type} {r : α → α → Prop} [DecidableRel r] (l : List α) :
    List.insertionSort r l = List.ofFn (l.get ∘ (insertionSortEquiv r l).symm) := by
  rw [insertionSortEquiv_get (r := r)]
  exact Eq.symm (List.ofFn_get (List.insertionSort r l))



def optionErase {I : Type} (l : List I) (i : Option (Fin l.length)) : List I :=
  match i with
  | none => l
  | some i => List.eraseIdx l i

def optionEraseZ {I : Type} (l : List I) (a : I) (i : Option (Fin l.length)) : List I :=
  match i with
  | none => a :: l
  | some i => List.eraseIdx l i

lemma eraseIdx_length {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).length + 1 = l.length := by
  simp [List.length_eraseIdx]
  have hi := i.prop
  omega

lemma eraseIdx_cons_length {I : Type} (a : I) (l : List I) (i : Fin (a :: l).length) :
    (List.eraseIdx (a :: l) i).length= l.length := by
  simp [List.length_eraseIdx]


lemma eraseIdx_get {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).get  = l.get ∘ (Fin.cast (eraseIdx_length l i)) ∘ (Fin.cast (eraseIdx_length l i).symm i).succAbove := by
  ext x
  simp only [Function.comp_apply, List.get_eq_getElem, List.eraseIdx, List.getElem_eraseIdx]
  simp [Fin.succAbove]
  by_cases hi: x.castSucc < Fin.cast (by exact Eq.symm (eraseIdx_length l i)) i
  · simp [ hi]
    intro h
    rw [Fin.lt_def] at hi
    simp_all
    omega
  · simp [ hi]
    rw [Fin.lt_def] at hi
    simp at hi
    have hn : ¬ x.val < i.val := by omega
    simp [hn]

lemma eraseIdx_insertionSort {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    [IsTotal I le1] [IsTrans I le1] :
    (n : ℕ) → (r : List I) → (hn : n < r.length) →
    (List.insertionSort le1 r).eraseIdx ↑((HepLean.List.insertionSortEquiv le1 r) ⟨n, hn⟩)
    = List.insertionSort le1 (r.eraseIdx n)
  | 0, [], _ => by
    simp
  | 0, (r0 :: r), hn => by
    simp only [List.insertionSort, List.insertionSort.eq_2, List.length_cons, insertionSortEquiv,
      Nat.succ_eq_add_one, Fin.zero_eta, Equiv.trans_apply, equivCons_zero, List.eraseIdx_zero,
      List.tail_cons]
    erw [orderedInsertEquiv_zero]
    simp
  | Nat.succ n, [], hn => by
    simp [insertionSortEquiv]
  | Nat.succ n, (r0 :: r), hn => by
    simp [insertionSortEquiv]
    have hOr := orderedInsert_eraseIdx_orderedInsertEquiv_fin_succ le1
      (List.insertionSort le1 r) r0 ((insertionSortEquiv le1 r) ⟨n, by simpa using hn⟩)
    erw [hOr]
    congr
    refine eraseIdx_insertionSort le1 n r _
    intro i j hij hn
    have hx := List.Sorted.rel_get_of_lt (r := le1) (l := (List.insertionSort le1 r))
      (List.sorted_insertionSort le1 r) hij
    have hr : le1 ((List.insertionSort le1 r).get j) r0 := by
      have hn := IsTotal.total (r := le1) ((List.insertionSort le1 r).get j) r0
      simp_all only [List.get_eq_getElem, List.length_cons, or_false]
    have ht (i j k : I) (hij : le1 i j) (hjk : ¬ le1 k j) : ¬ le1 k i := by
      intro hik
      have ht := IsTrans.trans (r := le1) k i j hik hij
      exact hjk ht
    exact ht ((List.insertionSort le1 r).get i) ((List.insertionSort le1 r).get j) r0 hx hn

lemma eraseIdx_insertionSort_fin {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    [IsTotal I le1] [IsTrans I le1]  (r : List I)  (n : Fin r.length) :
    (List.insertionSort le1 r).eraseIdx ↑((HepLean.List.insertionSortEquiv le1 r) n)
    = List.insertionSort le1 (r.eraseIdx n) :=
  eraseIdx_insertionSort le1 n.val r (Fin.prop n)




end HepLean.List
