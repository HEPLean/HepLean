/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic
import HepLean.PerturbationTheory.Wick.Signs.InsertSign
/-!

# Koszul sign insert

-/

namespace Wick

open HepLean.List
/-- Gives a factor of `-1` when inserting `a` into a list `List I` in the ordered position
  for each fermion-fermion cross. -/
def koszulSignInsert {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) (a : I) :
    List I → ℂ
  | [] => 1
  | b :: l => if r a b then koszulSignInsert r q a l else
    if q a = 1 ∧ q b = 1 then - koszulSignInsert r q a l else koszulSignInsert r q a l

/-- When inserting a boson the `koszulSignInsert` is always `1`. -/
lemma koszulSignInsert_boson {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) (a : I)
    (ha : q a = 0) : (l : List I) → koszulSignInsert r q a l = 1
  | [] => by
    simp [koszulSignInsert]
  | b :: l => by
    simp only [koszulSignInsert, Fin.isValue, ite_eq_left_iff]
    rw [koszulSignInsert_boson r q a ha l, ha]
    simp only [Fin.isValue, zero_ne_one, false_and, ↓reduceIte, ite_self]

@[simp]
lemma koszulSignInsert_mul_self {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (a : I) : (l : List I) → koszulSignInsert r q a l * koszulSignInsert r q a l = 1
  | [] => by
    simp [koszulSignInsert]
  | b :: l => by
    simp only [koszulSignInsert, Fin.isValue, mul_ite, ite_mul, neg_mul, mul_neg]
    by_cases hr : r a b
    · simp only [hr, ↓reduceIte]
      rw [koszulSignInsert_mul_self]
    · simp only [hr, ↓reduceIte, Fin.isValue]
      by_cases hq : q a = 1 ∧ q b = 1
      · simp only [hq, Fin.isValue, and_self, ↓reduceIte, neg_neg]
        rw [koszulSignInsert_mul_self]
      · simp only [Fin.isValue, hq, ↓reduceIte]
        rw [koszulSignInsert_mul_self]

lemma koszulSignInsert_le_forall {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (a : I) (l : List I) (hi : ∀ b, r a b) : koszulSignInsert r q a l = 1 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [koszulSignInsert, Fin.isValue, ite_eq_left_iff]
    rw [ih]
    simp only [Fin.isValue, ite_eq_left_iff, ite_eq_right_iff, and_imp]
    intro h
    exact False.elim (h (hi j))

lemma koszulSignInsert_ge_forall_append {I : Type} (r : I → I → Prop) [DecidableRel r]
    (q : I → Fin 2) (l : List I) (j i : I) (hi : ∀ j, r j i) :
    koszulSignInsert r q j l = koszulSignInsert r q j (l ++ [i]) := by
  induction l with
  | nil => simp [koszulSignInsert, hi]
  | cons b l ih =>
    simp only [koszulSignInsert, Fin.isValue, List.append_eq]
    by_cases hr : r j b
    · rw [if_pos hr, if_pos hr]
      rw [ih]
    · rw [if_neg hr, if_neg hr]
      rw [ih]

lemma koszulSignInsert_eq_filter {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (r0 : I) : (r : List I) →
    koszulSignInsert le1 q r0 r =
    koszulSignInsert le1 q r0 (List.filter (fun i => decide (¬ le1 r0 i)) r)
  | [] => by
    simp [koszulSignInsert]
  | r1 :: r => by
    dsimp only [koszulSignInsert, Fin.isValue]
    simp only [Fin.isValue, List.filter, decide_not]
    by_cases h : le1 r0 r1
    · simp only [h, ↓reduceIte, decide_True, Bool.not_true]
      rw [koszulSignInsert_eq_filter]
      congr
      simp
    · simp only [h, ↓reduceIte, Fin.isValue, decide_False, Bool.not_false]
      dsimp only [Fin.isValue, koszulSignInsert]
      simp only [Fin.isValue, h, ↓reduceIte]
      rw [koszulSignInsert_eq_filter]
      congr
      simp only [decide_not]
      simp

lemma koszulSignInsert_eq_cons {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    [IsTotal I le1] (r0 : I) (r : List I) :
    koszulSignInsert le1 q r0 r = koszulSignInsert le1 q r0 (r0 :: r) := by
  simp only [koszulSignInsert, Fin.isValue, and_self]
  have h1 : le1 r0 r0 := by
    simpa using IsTotal.total (r := le1) r0 r0
  simp [h1]

lemma koszulSignInsert_eq_grade {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (r0 : I) (r : List I) : koszulSignInsert le1 q r0 r = if grade q [r0] = 1 ∧
    grade q (List.filter (fun i => decide (¬ le1 r0 i)) r) = 1 then -1 else 1 := by
  induction r with
  | nil =>
    simp [koszulSignInsert]
  | cons r1 r ih =>
    rw [koszulSignInsert_eq_filter]
    by_cases hr1 : ¬ le1 r0 r1
    · rw [List.filter_cons_of_pos]
      · dsimp only [koszulSignInsert, Fin.isValue, decide_not]
        rw [if_neg hr1]
        dsimp only [Fin.isValue, grade, ite_eq_right_iff, zero_ne_one, imp_false, decide_not]
        simp only [Fin.isValue, decide_not, ite_eq_right_iff, zero_ne_one, imp_false]
        have ha (a b c : Fin 2) : (if a = 1 ∧ b = 1 then -if ¬a = 0 ∧
          c = 1 then -1 else (1 : ℂ)
          else if ¬a = 0 ∧ c = 1 then -1 else 1) =
          if ¬a = 0 ∧ ¬b = c then -1 else 1 := by
          fin_cases a <;> fin_cases b <;> fin_cases c
          any_goals rfl
          simp
        rw [← ha (q r0) (q r1) (grade q (List.filter (fun a => !decide (le1 r0 a)) r))]
        congr
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [grade] using ih
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [grade] using ih
      · simp [hr1]
    · rw [List.filter_cons_of_neg]
      simp only [decide_not, Fin.isValue]
      rw [koszulSignInsert_eq_filter] at ih
      simpa [grade] using ih
      simpa using hr1

lemma koszulSignInsert_eq_perm {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) (r r' : List I)
    (a : I) [DecidableRel le1] (h : r.Perm r') :
    koszulSignInsert le1 q a r = koszulSignInsert le1 q a r' := by
  rw [koszulSignInsert_eq_grade]
  rw [koszulSignInsert_eq_grade]
  congr 1
  simp only [Fin.isValue, decide_not, eq_iff_iff, and_congr_right_iff]
  intro h'
  have hg : grade q (List.filter (fun i => !decide (le1 a i)) r) =
      grade q (List.filter (fun i => !decide (le1 a i)) r') := by
    rw [grade_count, grade_count]
    rw [List.countP_filter, List.countP_filter]
    rw [h.countP_eq]
  rw [hg]

lemma koszulSignInsert_eq_sort {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) (r : List I)
    (a : I) [DecidableRel le1] :
    koszulSignInsert le1 q a r = koszulSignInsert le1 q a (List.insertionSort le1 r) := by
  apply koszulSignInsert_eq_perm
  exact List.Perm.symm (List.perm_insertionSort le1 r)

lemma koszulSignInsert_eq_insertSign {I : Type} (q : I → Fin 2) (le1 : I → I → Prop)
    [DecidableRel le1] [IsTotal I le1] [IsTrans I le1] (r0 : I) (r : List I) :
    koszulSignInsert le1 q r0 r = insertSign q (orderedInsertPos le1 (List.insertionSort le1 r) r0)
      r0 (List.insertionSort le1 r) := by
  rw [koszulSignInsert_eq_cons, koszulSignInsert_eq_sort, koszulSignInsert_eq_filter,
    koszulSignInsert_eq_grade, insertSign, superCommuteCoef]
  congr
  simp only [List.filter_filter, Bool.and_self]
  rw [List.insertionSort]
  nth_rewrite 1 [List.orderedInsert_eq_take_drop]
  rw [List.filter_append]
  have h1 : List.filter (fun a => decide ¬le1 r0 a)
    (List.takeWhile (fun b => decide ¬le1 r0 b) (List.insertionSort le1 r))
    = (List.takeWhile (fun b => decide ¬le1 r0 b) (List.insertionSort le1 r)) := by
    induction r with
    | nil => simp
    | cons r1 r ih =>
      simp only [decide_not, List.insertionSort, List.filter_eq_self, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not]
      intro a ha
      have ha' := List.mem_takeWhile_imp ha
      simp_all
  rw [h1]
  rw [List.filter_cons]
  simp only [decide_not, (IsTotal.to_isRefl le1).refl r0, not_true_eq_false, decide_False,
    Bool.false_eq_true, ↓reduceIte]
  rw [orderedInsertPos_take]
  simp only [decide_not, List.append_right_eq_self, List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, Decidable.not_not]
  intro a ha
  refine List.Sorted.rel_of_mem_take_of_mem_drop
    (k := (orderedInsertPos le1 (List.insertionSort le1 r) r0).1 + 1)
    (List.sorted_insertionSort le1 (r0 :: r)) ?_ ?_
  · simp only [List.insertionSort, List.orderedInsert_eq_take_drop, decide_not]
    rw [List.take_append_eq_append_take]
    rw [List.take_of_length_le]
    · simp [orderedInsertPos]
    · simp [orderedInsertPos]
  · simp only [List.insertionSort, List.orderedInsert_eq_take_drop, decide_not]
    rw [List.drop_append_eq_append_drop]
    rw [List.drop_of_length_le]
    · simpa [orderedInsertPos] using ha
    · simp [orderedInsertPos]

lemma koszulSignInsert_insertIdx {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (i j : I) (r : List I) (n : ℕ) (hn : n ≤ r.length) :
    koszulSignInsert le1 q j (List.insertIdx n i r) = koszulSignInsert le1 q j (i :: r) := by
  apply koszulSignInsert_eq_perm
  exact List.perm_insertIdx i r hn

/-- The difference in `koszulSignInsert` on inserting `r0` into `r` compared to
  into `r1 :: r` for any `r`. -/
def koszulSignCons {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (r0 r1 : I) :
    ℂ :=
  if le1 r0 r1 then 1 else
  if q r0 = 1 ∧ q r1 = 1 then -1 else 1

lemma koszulSignCons_eq_superComuteCoef {I : Type} (q : I → Fin 2) (le1 : I → I → Prop)
    [DecidableRel le1] (r0 r1 : I) : koszulSignCons q le1 r0 r1 =
    if le1 r0 r1 then 1 else superCommuteCoef q [r0] [r1] := by
  simp only [koszulSignCons, Fin.isValue, superCommuteCoef, grade, ite_eq_right_iff, zero_ne_one,
    imp_false]
  congr 1
  by_cases h0 : q r0 = 1
  · by_cases h1 : q r1 = 1
    · simp [h0, h1]
    · have h1 : q r1 = 0 := by omega
      simp [h0, h1]
  · have h0 : q r0 = 0 := by omega
    by_cases h1 : q r1 = 1
    · simp [h0, h1]
    · have h1 : q r1 = 0 := by omega
      simp [h0, h1]

lemma koszulSignInsert_cons {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (r0 r1 : I) (r : List I) :
    koszulSignInsert le1 q r0 (r1 :: r) = (koszulSignCons q le1 r0 r1) *
    koszulSignInsert le1 q r0 r := by
  simp [koszulSignInsert, koszulSignCons]

end Wick
