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

noncomputable section

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

end
end Wick
