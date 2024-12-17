/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Species
import HepLean.Lorentz.RealVector.Basic
import HepLean.Mathematics.Fin
import HepLean.SpaceTime.Basic
import HepLean.Mathematics.SuperAlgebra.Basic
import HepLean.Mathematics.List
import HepLean.Meta.Notes.Basic
import Init.Data.List.Sort.Basic
import Mathlib.Data.Fin.Tuple.Take
import HepLean.PerturbationTheory.Wick.Koszul.Order
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

def grade {I : Type} (q : I → Fin 2) : (l : List I) → Fin 2
  | [] => 0
  | a :: l => if q a = grade q l then 0 else 1

@[simp]
lemma grade_freeMonoid  {I : Type} (q : I → Fin 2) (i : I) : grade q (FreeMonoid.of i) = q i := by
  simp only [grade, Fin.isValue]
  have ha (a : Fin 2) : (if a = 0 then 0 else 1) = a := by
    fin_cases a <;> rfl
  rw [ha]

@[simp]
lemma grade_empty {I : Type} (q : I → Fin 2) : grade q [] = 0 := by
  simp [grade]

@[simp]
lemma grade_append {I : Type} (q : I → Fin 2) (l r : List I) :
    grade q (l ++ r) = if grade q l = grade q r then 0 else 1 := by
  induction l with
  | nil =>
    simp only [List.nil_append, grade_empty, Fin.isValue]
    have ha (a : Fin 2) : (if 0 = a then 0 else 1) = a := by
      fin_cases a <;> rfl
    exact Eq.symm (Fin.eq_of_val_eq (congrArg Fin.val (ha (grade q r))))
  | cons a l ih =>
    simp only [grade, List.append_eq, Fin.isValue]
    erw [ih]
    have hab (a b c : Fin 2) : (if a = if b = c then 0 else 1 then (0 : Fin 2) else 1) =
         if (if a = b then 0 else 1) = c then 0 else 1 := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
    exact hab (q a) (grade q l) (grade q r)

lemma grade_orderedInsert {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (l : List I) ( i : I ) :
    grade q (List.orderedInsert le1 i l) = grade q (i :: l) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp
    by_cases hij : le1 i j
    · simp [hij]
    · simp [hij]
      rw [grade]
      rw [ih]
      simp [grade]
      have h1 (a b c : Fin 2) : (if a = if b = c then 0 else 1 then (0 : Fin 2) else 1) = if b = if a = c then 0 else 1 then 0 else 1 := by
        fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
      exact h1 _ _ _

@[simp]
lemma grade_insertionSort {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (l : List I) :
    grade q (List.insertionSort le1 l) = grade q l := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp [grade]
    rw [grade_orderedInsert]
    simp [grade]
    rw [ih]

def superCommuteCoef {I : Type} (q : I → Fin 2) (la lb : List I) : ℂ :=
  if grade q la = 1 ∧ grade q lb = 1 then - 1 else  1

lemma superCommuteCoef_empty {I : Type} (q : I → Fin 2) (la : List I) :
    superCommuteCoef q la [] = 1 := by
  simp only [superCommuteCoef, Fin.isValue, grade_empty, zero_ne_one, and_false, ↓reduceIte]

lemma superCommuteCoef_append {I : Type} (q : I → Fin 2) (la lb lc  : List I) :
    superCommuteCoef q la (lb ++ lc) = superCommuteCoef q la lb * superCommuteCoef q la lc := by
  simp only [superCommuteCoef, Fin.isValue, grade_append, ite_eq_right_iff, zero_ne_one, imp_false,
    mul_ite, mul_neg, mul_one]
  by_cases hla : grade q la = 1
  · by_cases hlb : grade q lb = 1
    · by_cases hlc : grade q lc = 1
      · simp [hlc, hlb, hla]
      · have hc : grade q lc = 0 := by
          omega
        simp [hc, hlb, hla]
    · have hb : grade q lb = 0 := by
        omega
      by_cases hlc : grade q lc = 1
      · simp [hlc, hb]
      · have hc : grade q lc = 0 := by
          omega
        simp [hc, hb]
  · have ha : grade q la = 0 := by
      omega
    simp [ha]

def superCommuteCoefM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) : ℂ :=
    (if grade (fun i => q i.fst) l = 1 ∧ grade q r = 1 then -1 else 1)

lemma superCommuteCoefM_empty  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)):
    superCommuteCoefM q l [] = 1 := by
  simp [superCommuteCoefM]

lemma koszulSign_first_remove {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (l : List I)
    [DecidableRel le1] (a : I) :
    let n0 := ((HepLean.List.insertionSortEquiv le1 (a :: l)).symm ⟨0, by
      rw [List.length_insertionSort]; simp⟩)
    koszulSign le1 q (a :: l) = superCommuteCoef q [(a :: l).get n0] (List.take n0 (a :: l)) *
      koszulSign le1 q ((a :: l).eraseIdx n0) := by sorry

def superCommuteCoefLE  {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (n : Fin r.length) : ℂ  :=
  koszulSign le1 q r *
  superCommuteCoef q [i] (List.take (↑((HepLean.List.insertionSortEquiv le1 r) n))
    (List.insertionSort le1 r)) *
  koszulSign le1 q (r.eraseIdx ↑n)




def natTestQ' : ℕ → Fin 2 := fun n => if n % 2 = 0 then 0 else 1

#eval superCommuteCoefLE (natTestQ') (fun i j => i ≤ j) [5, 4, 4, 3, 0] 0 ⟨0, by simp⟩
#eval koszulSign (fun i j => i ≤ j) (natTestQ') [5, 4, 4, 3, 0]

lemma koszulSignInsert_eq_superCommuteCoef{I : Type} (q : I → Fin 2) (le1 : I → I → Prop) (r : List I)
    (a : I) [DecidableRel le1] (i : I) :
    koszulSignInsert le1 q a r = superCommuteCoef q [i]
      (List.take (↑((HepLean.List.insertionSortEquiv le1 (a :: r)) ⟨0, by simp⟩))
      (List.orderedInsert le1 a (List.insertionSort le1 r))) := by

  sorry

lemma superCommuteCoefLE_zero {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) (r : List I)
    (a : I)
    [DecidableRel le1] (i : I) :
    superCommuteCoefLE q le1 (a :: r) i ⟨0, Nat.zero_lt_succ r.length⟩ = 1 := by
  simp [superCommuteCoefLE]
  simp [koszulSign]
  trans koszulSignInsert le1 q a r * (koszulSign le1 q r * koszulSign le1 q r) *
      superCommuteCoef q [i]
        (List.take (↑((HepLean.List.insertionSortEquiv le1 (a :: r)) ⟨0, Nat.zero_lt_succ r.length⟩))
          (List.orderedInsert le1 a (List.insertionSort le1 r)))
  · ring_nf
    rfl
  rw [koszulSign_mul_self]
  simp
  sorry

lemma superCommuteCoefLE_eq_get_boson {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (hi : q i = 0 ) (n : Fin r.length)
    (heq : q i = q (r.get n)) :
    superCommuteCoefLE q le1 r i n = superCommuteCoef q [r.get n] (r.take n) := by
  simp [superCommuteCoefLE, superCommuteCoef]
  simp [grade, hi]
  simp [hi] at heq
  simp [heq]
  rw [koszulSign_erase_boson]
  rw [koszulSign_mul_self]
  exact id (Eq.symm heq)

lemma koszulSignInsert_eq_filter {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (r0 : I)
     :  (r : List I) →
    koszulSignInsert le1 q r0 r = koszulSignInsert le1 q r0 (List.filter (fun i => decide (¬ le1 r0 i)) r)
  | [] => by
    simp [koszulSignInsert]
  | r1 :: r => by
    dsimp [koszulSignInsert]
    simp [List.filter]
    by_cases h : le1 r0 r1
    · simp [h]
      rw [koszulSignInsert_eq_filter]
      congr
      simp
    · simp [h]
      dsimp [koszulSignInsert]
      simp [h]
      rw [koszulSignInsert_eq_filter]
      congr
      simp
      simp

lemma filter_le_orderedInsert {I : Type} (le1 : I → I → Prop)
    (le_trans : ∀ {i j k}, le1 i j → le1 j k → le1 i k)
      (le_connected : ∀ {i j}, ¬ le1 i j → le1 j i) [DecidableRel le1] (rn r0 : I)
     (r : List I) (hr : (List.filter (fun i => decide (¬ le1 rn i)) r) =
      List.takeWhile (fun i => decide (¬ le1 rn i)) r) :
      (List.filter (fun i => decide (¬ le1 rn i)) (List.orderedInsert le1 r0 r)) =
      List.takeWhile (fun i => decide (¬ le1 rn i)) (List.orderedInsert le1 r0 r) := by
  induction r with
  | nil =>
    simp [List.filter, List.takeWhile]
  | cons r1 r ih =>
    simp
    by_cases hr1 : le1 r0 r1
    · simp [hr1]
      rw [List.filter, List.takeWhile]
      by_cases hrn : le1 rn r0
      · simp [hrn]
        apply And.intro
        · exact le_trans hrn hr1
        · intro rp hr'
          have hrn1 := le_trans hrn hr1
          simp [List.filter, List.takeWhile, hrn1] at hr
          exact hr rp hr'
      · simp [hrn]
        simpa using hr
    · simp [hr1, List.filter, List.takeWhile]
      by_cases hrn : le1 rn r1
      · simp [hrn]
        apply And.intro
        · exact le_trans hrn (le_connected hr1)
        · simp [List.filter, List.takeWhile, hrn] at hr
          exact hr
      · simp [hrn]
        have hr' : List.filter (fun i => decide ¬le1 rn i) r = List.takeWhile (fun i => decide ¬le1 rn i) r := by
          simp [List.filter, List.takeWhile, hrn] at hr
          simpa using hr
        simpa only [decide_not] using ih hr'


lemma filter_le_sort  {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (le_trans : ∀ {i j k}, le1 i j → le1 j k → le1 i k)
    (le_connected : ∀ {i j}, ¬ le1 i j → le1 j i)  (r0 : I) (r : List I) :
    List.filter (fun i => decide (¬ le1 r0 i)) (List.insertionSort le1 r) =
    List.takeWhile (fun i => decide (¬ le1 r0 i)) (List.insertionSort le1 r) := by
  induction r with
  | nil =>
    simp
  | cons r1 r ih =>
    simp only [ List.insertionSort]
    rw [filter_le_orderedInsert]
    exact fun {i j k} a a_1 => le_trans a a_1
    exact fun {i j} a => le_connected a
    exact ih

lemma koszulSignInsert_eq_grade {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (r0 : I)
     (r : List I)  :
    koszulSignInsert le1 q r0 r = if grade q [r0] = 1 ∧
      grade q (List.filter (fun i => decide (¬ le1 r0 i)) r) = 1 then -1 else 1 := by
  induction r with
  | nil =>
    simp [koszulSignInsert]
  | cons r1 r ih =>
    rw [koszulSignInsert_eq_filter]
    by_cases hr1 : ¬ le1 r0 r1
    · rw [List.filter_cons_of_pos]
      · dsimp [koszulSignInsert]
        rw [if_neg hr1]
        dsimp [grade]
        simp [grade]
        have ha (a b c : Fin 2) : (if a = 1 ∧ b = 1 then -if ¬a = 0 ∧
          c = 1 then -1 else (1 : ℂ)
          else if ¬a = 0 ∧ c = 1 then -1 else 1) =
         if ¬a = 0 ∧ ¬b = c then -1 else 1:= by
          fin_cases a <;> fin_cases b <;> fin_cases c
          any_goals rfl
          simp
        rw [← ha (q r0) (q r1) (grade q (List.filter (fun a => !decide (le1 r0 a)) r) )]
        congr
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [grade] using ih
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [grade] using ih
      · simp [hr1]
    · rw [List.filter_cons_of_neg]
      simp
      rw [koszulSignInsert_eq_filter] at ih
      simpa [grade] using ih
      simpa using hr1



lemma koszulSign_erase_fermion {I : Type} (q : I → Fin 2) (le1 :I → I → Prop)
    [DecidableRel le1]  :
    (r : List I) → (n : Fin r.length) →  (heq : q (r.get n) = 1) →
    koszulSign le1 q (r.eraseIdx n) = koszulSign le1 q r *
      if grade q (r.take n) = grade q (List.take (↑((HepLean.List.insertionSortEquiv le1 r) n)) (List.insertionSort le1 r))
        then 1 else -1
  | [], _ => by
    simp
  | r0 :: r, ⟨0, h⟩ => by
    simp [koszulSign]
    intro h
    rw [koszulSignInsert_boson]
    simp
    sorry
    sorry
  | r0 :: r, ⟨n + 1, h⟩ => by
    intro hn
    simp only [List.eraseIdx_cons_succ, List.take_succ_cons, List.insertionSort, List.length_cons,
       mul_one, mul_neg]
    sorry

lemma superCommuteCoefLE_eq_get_fermion {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (hi : q i = 1 ) (n : Fin r.length)
    (heq : q i = q (r.get n)) :
    superCommuteCoefLE q le1 r i n = superCommuteCoef q [r.get n] (r.take n) := by
  simp [superCommuteCoefLE, superCommuteCoef]
  simp [grade, hi]
  simp [hi] at heq
  simp [← heq]
  sorry


lemma superCommuteCoefLE_eq_get {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (n : Fin r.length) (heq : q i = q (r.get n)) :
    superCommuteCoefLE q le1 r i n = superCommuteCoef q [r.get n] (r.take n) := by
  sorry

end Wick
