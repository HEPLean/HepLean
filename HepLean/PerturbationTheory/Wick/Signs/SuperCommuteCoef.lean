/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Mathematics.List
import HepLean.PerturbationTheory.Wick.Signs.Grade
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick
open HepLean.List

/-- Given two lists `la` and `lb` returns `-1` if they are both of grade `1` and
  `1` otherwise. This corresponds to the sign associated with the super commutator
  when commuting `la` and `lb` in the free algebra.
  In terms of physics it is `-1` if commuting two fermionic operators and `1` otherwise. -/
def superCommuteCoef {I : Type} (q : I → Fin 2) (la lb : List I) : ℂ :=
  if grade q la = 1 ∧ grade q lb = 1 then - 1 else 1

lemma superCommuteCoef_comm {I : Type} (q : I → Fin 2) (la lb : List I) :
    superCommuteCoef q la lb = superCommuteCoef q lb la := by
  simp only [superCommuteCoef, Fin.isValue]
  congr 1
  exact Eq.propIntro (fun a => id (And.symm a)) fun a => id (And.symm a)

/-- Given a list `l : List (Σ i, f i)` and a list `r : List I` returns `-1` if the
  grade of `l` is `1` and the grade of `r` is `1` and `1` otherwise. This corresponds
  to the sign associated with the super commutator when commuting
  the lift of `l` and `r` (by summing over fibers) in the
  free algebra over `Σ i, f i`.
  In terms of physics it is `-1` if commuting two fermionic operators and `1` otherwise. -/
def superCommuteLiftCoef {I : Type} {f : I → Type}
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) : ℂ :=
    (if grade (fun i => q i.fst) l = 1 ∧ grade q r = 1 then -1 else 1)

lemma superCommuteLiftCoef_empty {I : Type} {f : I → Type}
    (q : I → Fin 2) (l : List (Σ i, f i)) :
    superCommuteLiftCoef q l [] = 1 := by
  simp [superCommuteLiftCoef]

lemma superCommuteCoef_perm_snd {I : Type} (q : I → Fin 2) (la lb lb' : List I)
    (h : lb.Perm lb') :
    superCommuteCoef q la lb = superCommuteCoef q la lb' := by
  rw [superCommuteCoef, superCommuteCoef, grade_perm q h]

lemma superCommuteCoef_mul_self {I : Type} (q : I → Fin 2) (l lb : List I) :
    superCommuteCoef q l lb * superCommuteCoef q l lb = 1 := by
  simp only [superCommuteCoef, Fin.isValue, mul_ite, mul_neg, mul_one]
  have ha (a b : Fin 2) : (if a = 1 ∧ b = 1 then -if a = 1 ∧ b = 1 then -1 else 1
    else if a = 1 ∧ b = 1 then -1 else 1) = (1 : ℂ) := by
      fin_cases a <;> fin_cases b
      any_goals rfl
      simp
  exact ha (grade q l) (grade q lb)

lemma superCommuteCoef_empty {I : Type} (q : I → Fin 2) (la : List I) :
    superCommuteCoef q la [] = 1 := by
  simp only [superCommuteCoef, Fin.isValue, grade_empty, zero_ne_one, and_false, ↓reduceIte]

lemma superCommuteCoef_append {I : Type} (q : I → Fin 2) (la lb lc : List I) :
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

lemma superCommuteCoef_cons {I : Type} (q : I → Fin 2) (i : I) (la lb : List I) :
    superCommuteCoef q la (i :: lb) = superCommuteCoef q la [i] * superCommuteCoef q la lb := by
  trans superCommuteCoef q la ([i] ++ lb)
  simp only [List.singleton_append]
  rw [superCommuteCoef_append]

end Wick
