/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic
/-!

# Koszul sign insert

-/

namespace Wick

/-- Given a grading map `q : I → Fin 2` and a list `l : List I` counts the parity of the number of
  elements in `l` which are of grade `1`. -/
def grade {I : Type} (q : I → Fin 2) : (l : List I) → Fin 2
  | [] => 0
  | a :: l => if q a = grade q l then 0 else 1

@[simp]
lemma grade_freeMonoid {I : Type} (q : I → Fin 2) (i : I) : grade q (FreeMonoid.of i) = q i := by
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

lemma grade_count {I : Type} (q : I → Fin 2) (l : List I) :
    grade q l = if Nat.mod (List.countP (fun i => decide (q i = 1)) l) 2 = 0 then 0 else 1 := by
  induction l with
  | nil => simp
  | cons r0 r ih =>
    simp only [grade, Fin.isValue]
    rw [List.countP_cons]
    simp only [Fin.isValue, decide_eq_true_eq]
    rw [ih]
    by_cases h: q r0 = 1
    · simp only [h, Fin.isValue, ↓reduceIte]
      split
      next h1 =>
        simp_all only [Fin.isValue, ↓reduceIte, one_ne_zero]
        split
        next h2 =>
          simp_all only [Fin.isValue, one_ne_zero]
          have ha (a : ℕ) (ha : a % 2 = 0) : (a + 1) % 2 ≠ 0 := by
            omega
          exact ha (List.countP (fun i => decide (q i = 1)) r) h1 h2
        next h2 => simp_all only [Fin.isValue]
      next h1 =>
        simp_all only [Fin.isValue, ↓reduceIte]
        split
        next h2 => simp_all only [Fin.isValue]
        next h2 =>
          simp_all only [Fin.isValue, zero_ne_one]
          have ha (a : ℕ) (ha : ¬ a % 2 = 0) : (a + 1) % 2 = 0 := by
            omega
          exact h2 (ha (List.countP (fun i => decide (q i = 1)) r) h1)
    · have h0 : q r0 = 0 := by omega
      simp only [h0, Fin.isValue, zero_ne_one, ↓reduceIte, add_zero]
      by_cases hn : (List.countP (fun i => decide (q i = 1)) r).mod 2 = 0
      · simp [hn]
      · simp [hn]

lemma grade_perm {I : Type} (q : I → Fin 2) {l l' : List I} (h : l.Perm l') :
    grade q l = grade q l' := by
  rw [grade_count, grade_count, h.countP_eq]

lemma grade_orderedInsert {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (i : I) : grade q (List.orderedInsert le1 i l) = grade q (i :: l) := by
  apply grade_perm
  exact List.perm_orderedInsert le1 i l

@[simp]
lemma grade_insertionSort {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) : grade q (List.insertionSort le1 l) = grade q l := by
  apply grade_perm
  exact List.perm_insertionSort le1 l

end Wick
