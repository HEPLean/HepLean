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

def test {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1]  (n : Fin r.length) : ℂ  :=
    if grade q (List.take n r) = grade q ((List.take (↑((HepLean.List.insertionSortEquiv le1 r) n))
    (List.insertionSort le1 r))) then 1 else -1

def superCommuteCoefLE  {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (n : Fin r.length) : ℂ  :=
  koszulSign le1 q r *
  superCommuteCoef q [i] (List.take (↑((HepLean.List.insertionSortEquiv le1 r) n))
    (List.insertionSort le1 r)) *
  koszulSign le1 q (r.eraseIdx ↑n)

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


lemma superCommuteCoefLE_eq_get {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (n : Fin r.length) :
    superCommuteCoefLE q le1 r i n =  superCommuteCoef q [r.get n] (r.take n) := by
  sorry
end Wick
