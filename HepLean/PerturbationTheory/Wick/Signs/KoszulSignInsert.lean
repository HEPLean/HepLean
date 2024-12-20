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
open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- Gives a factor of `-1` when inserting `a` into a list `List I` in the ordered position
  for each fermion-fermion cross. -/
def koszulSignInsert {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop)
    [DecidableRel le] (a : 𝓕) : List 𝓕 → ℂ
  | [] => 1
  | b :: l => if le a b then koszulSignInsert q le a l else
    if q a = fermionic ∧ q b = fermionic then - koszulSignInsert q le a l else
      koszulSignInsert q le a l

/-- When inserting a boson the `koszulSignInsert` is always `1`. -/
lemma koszulSignInsert_boson (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]
    (a : 𝓕) (ha : q a = bosonic) : (l : List 𝓕) → koszulSignInsert q le a l = 1
  | [] => by
    simp [koszulSignInsert]
  | b :: l => by
    simp only [koszulSignInsert, Fin.isValue, ite_eq_left_iff]
    rw [koszulSignInsert_boson q le a ha l, ha]
    simp only [reduceCtorEq, false_and, ↓reduceIte, ite_self]

@[simp]
lemma koszulSignInsert_mul_self (a : 𝓕) :
    (l : List 𝓕) → koszulSignInsert q le a l * koszulSignInsert q le a l = 1
  | [] => by
    simp [koszulSignInsert]
  | b :: l => by
    simp only [koszulSignInsert, Fin.isValue, mul_ite, ite_mul, neg_mul, mul_neg]
    by_cases hr : le a b
    · simp only [hr, ↓reduceIte]
      rw [koszulSignInsert_mul_self]
    · simp only [hr, ↓reduceIte]
      by_cases hq : q a = fermionic ∧ q b = fermionic
      · simp only [hq, and_self, ↓reduceIte, neg_neg]
        rw [koszulSignInsert_mul_self]
      · simp only [hq, ↓reduceIte]
        rw [koszulSignInsert_mul_self]

lemma koszulSignInsert_le_forall (a : 𝓕) (l : List 𝓕) (hi : ∀ b, le a b) :
    koszulSignInsert q le a l = 1 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [koszulSignInsert, Fin.isValue, ite_eq_left_iff]
    rw [ih]
    simp only [Fin.isValue, ite_eq_left_iff, ite_eq_right_iff, and_imp]
    intro h
    exact False.elim (h (hi j))

lemma koszulSignInsert_ge_forall_append (l : List 𝓕) (j i : 𝓕) (hi : ∀ j, le j i) :
    koszulSignInsert q le j l = koszulSignInsert q le j (l ++ [i]) := by
  induction l with
  | nil => simp [koszulSignInsert, hi]
  | cons b l ih =>
    simp only [koszulSignInsert, Fin.isValue, List.append_eq]
    by_cases hr : le j b
    · rw [if_pos hr, if_pos hr]
      rw [ih]
    · rw [if_neg hr, if_neg hr]
      rw [ih]

lemma koszulSignInsert_eq_filter (r0 : 𝓕) : (r : List 𝓕) →
    koszulSignInsert q le r0 r =
    koszulSignInsert q le r0 (List.filter (fun i => decide (¬ le r0 i)) r)
  | [] => by
    simp [koszulSignInsert]
  | r1 :: r => by
    dsimp only [koszulSignInsert, Fin.isValue]
    simp only [Fin.isValue, List.filter, decide_not]
    by_cases h : le r0 r1
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

lemma koszulSignInsert_eq_cons [IsTotal 𝓕 le] (r0 : 𝓕) (r : List 𝓕) :
    koszulSignInsert q le r0 r = koszulSignInsert q le r0 (r0 :: r) := by
  simp only [koszulSignInsert, Fin.isValue, and_self]
  have h1 : le r0 r0 := by
    simpa using IsTotal.total (r := le) r0 r0
  simp [h1]

lemma koszulSignInsert_eq_grade (r0 : 𝓕) (r : List 𝓕) :
    koszulSignInsert q le r0 r = if ofList q [r0] = fermionic ∧
    ofList q (List.filter (fun i => decide (¬ le r0 i)) r) = fermionic then -1 else 1 := by
  induction r with
  | nil =>
    simp [koszulSignInsert]
  | cons r1 r ih =>
    rw [koszulSignInsert_eq_filter]
    by_cases hr1 : ¬ le r0 r1
    · rw [List.filter_cons_of_pos]
      · dsimp only [koszulSignInsert, Fin.isValue, decide_not]
        rw [if_neg hr1]
        dsimp only [Fin.isValue, ofList, ite_eq_right_iff, zero_ne_one, imp_false, decide_not]
        simp only [decide_not, ite_eq_right_iff, reduceCtorEq, imp_false]
        have ha (a b c : FieldStatistic) : (if a = fermionic ∧ b = fermionic then -if ¬a = bosonic ∧
          c = fermionic then -1 else (1 : ℂ)
          else if ¬a = bosonic ∧ c = fermionic then -1 else 1) =
          if ¬a = bosonic ∧ ¬b = c then -1 else 1 := by
          fin_cases a <;> fin_cases b <;> fin_cases c
          any_goals rfl
          simp
        rw [← ha (q r0) (q r1) (ofList q (List.filter (fun a => !decide (le r0 a)) r))]
        congr
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [ofList] using ih
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [ofList] using ih
      · simp [hr1]
    · rw [List.filter_cons_of_neg]
      simp only [decide_not, Fin.isValue]
      rw [koszulSignInsert_eq_filter] at ih
      simpa [ofList] using ih
      simpa using hr1

lemma koszulSignInsert_eq_perm (r r' : List 𝓕) (a : 𝓕) (h : r.Perm r') :
    koszulSignInsert q le a r = koszulSignInsert q le a r' := by
  rw [koszulSignInsert_eq_grade]
  rw [koszulSignInsert_eq_grade]
  congr 1
  simp only [Fin.isValue, decide_not, eq_iff_iff, and_congr_right_iff]
  intro h'
  have hg : ofList q (List.filter (fun i => !decide (le a i)) r) =
      ofList q (List.filter (fun i => !decide (le a i)) r') := by
    apply ofList_perm
    exact List.Perm.filter (fun i => !decide (le a i)) h
  rw [hg]

lemma koszulSignInsert_eq_sort (r : List 𝓕) (a : 𝓕) :
    koszulSignInsert q le a r = koszulSignInsert q le a (List.insertionSort le r) := by
  apply koszulSignInsert_eq_perm
  exact List.Perm.symm (List.perm_insertionSort le r)

lemma koszulSignInsert_eq_insertSign [IsTotal 𝓕 le] [IsTrans 𝓕 le] (r0 : 𝓕) (r : List 𝓕) :
    koszulSignInsert q le r0 r = insertSign q (orderedInsertPos le (List.insertionSort le r) r0)
      r0 (List.insertionSort le r) := by
  rw [koszulSignInsert_eq_cons, koszulSignInsert_eq_sort, koszulSignInsert_eq_filter,
    koszulSignInsert_eq_grade, insertSign, superCommuteCoef]
  congr
  simp only [List.filter_filter, Bool.and_self]
  rw [List.insertionSort]
  nth_rewrite 1 [List.orderedInsert_eq_take_drop]
  rw [List.filter_append]
  have h1 : List.filter (fun a => decide ¬le r0 a)
    (List.takeWhile (fun b => decide ¬le r0 b) (List.insertionSort le r))
    = (List.takeWhile (fun b => decide ¬le r0 b) (List.insertionSort le r)) := by
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
  simp only [decide_not, (IsTotal.to_isRefl le).refl r0, not_true_eq_false, decide_False,
    Bool.false_eq_true, ↓reduceIte]
  rw [orderedInsertPos_take]
  simp only [decide_not, List.append_right_eq_self, List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, Decidable.not_not]
  intro a ha
  refine List.Sorted.rel_of_mem_take_of_mem_drop
    (k := (orderedInsertPos le (List.insertionSort le r) r0).1 + 1)
    (List.sorted_insertionSort le (r0 :: r)) ?_ ?_
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

lemma koszulSignInsert_insertIdx (i j : 𝓕) (r : List 𝓕) (n : ℕ) (hn : n ≤ r.length) :
    koszulSignInsert q le j (List.insertIdx n i r) = koszulSignInsert q le j (i :: r) := by
  apply koszulSignInsert_eq_perm
  exact List.perm_insertIdx i r hn

/-- The difference in `koszulSignInsert` on inserting `r0` into `r` compared to
  into `r1 :: r` for any `r`. -/
def koszulSignCons (r0 r1 : 𝓕) : ℂ :=
  if le r0 r1 then 1 else
  if q r0 = fermionic ∧ q r1 = fermionic then -1 else 1

lemma koszulSignCons_eq_superComuteCoef (r0 r1 : 𝓕) : koszulSignCons q le r0 r1 =
    if le r0 r1 then 1 else superCommuteCoef q [r0] [r1] := by
  simp only [koszulSignCons, Fin.isValue, superCommuteCoef, ofList, ite_eq_right_iff, zero_ne_one,
    imp_false]
  congr 1
  by_cases h0 : q r0 = fermionic
  · by_cases h1 : q r1 = fermionic
    · simp [h0, h1]
    · have h1 : q r1 = bosonic := (neq_fermionic_iff_eq_bosonic (q r1)).mp h1
      simp [h0, h1]
  · have h0 : q r0 = bosonic := (neq_fermionic_iff_eq_bosonic (q r0)).mp h0
    by_cases h1 : q r1 = fermionic
    · simp [h0, h1]
    · have h1 : q r1 = bosonic := (neq_fermionic_iff_eq_bosonic (q r1)).mp h1
      simp [h0, h1]

lemma koszulSignInsert_cons (r0 r1 : 𝓕) (r : List 𝓕) :
    koszulSignInsert q le r0 (r1 :: r) = (koszulSignCons q le r0 r1) *
    koszulSignInsert q le r0 r := by
  simp [koszulSignInsert, koszulSignCons]

end Wick
