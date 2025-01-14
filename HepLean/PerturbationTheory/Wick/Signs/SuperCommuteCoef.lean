/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStatistics
/-!

# Super commutation coefficient.

This is a complex number which is `-1` when commuting two fermionic operators and `1` otherwise.

-/

namespace Wick
open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic)

/-- Given two lists `la` and `lb` returns `-1` if they are both of grade `1` and
  `1` otherwise. This corresponds to the sign associated with the super commutator
  when commuting `la` and `lb` in the free algebra.
  In terms of physics it is `-1` if commuting two fermionic operators and `1` otherwise. -/
def superCommuteCoef (la lb : List 𝓕) : ℂ :=
  if FieldStatistic.ofList q la = fermionic ∧
    FieldStatistic.ofList q lb = fermionic then - 1 else 1

lemma superCommuteCoef_comm (la lb : List 𝓕) :
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
def superCommuteLiftCoef {f : 𝓕 → Type} (φs : List (Σ i, f i)) (φs' : List 𝓕) : ℂ :=
    (if FieldStatistic.ofList (fun i => q i.fst) φs = fermionic ∧
      FieldStatistic.ofList q φs' = fermionic then -1 else 1)

lemma superCommuteLiftCoef_empty {f : 𝓕 → Type} (φs : List (Σ i, f i)) :
    superCommuteLiftCoef q φs [] = 1 := by
  simp [superCommuteLiftCoef]

lemma superCommuteCoef_perm_snd (la lb lb' : List 𝓕)
    (h : lb.Perm lb') :
    superCommuteCoef q la lb = superCommuteCoef q la lb' := by
  rw [superCommuteCoef, superCommuteCoef, FieldStatistic.ofList_perm q h]

lemma superCommuteCoef_mul_self (l lb : List 𝓕) :
    superCommuteCoef q l lb * superCommuteCoef q l lb = 1 := by
  simp only [superCommuteCoef, Fin.isValue, mul_ite, mul_neg, mul_one]
  have ha (a b : FieldStatistic) : (if a = fermionic ∧ b = fermionic then
      -if a = fermionic ∧ b = fermionic then -1 else 1
    else if a = fermionic ∧ b = fermionic then -1 else 1) = (1 : ℂ) := by
      fin_cases a <;> fin_cases b
      any_goals rfl
      simp
  exact ha (FieldStatistic.ofList q l) (FieldStatistic.ofList q lb)

lemma superCommuteCoef_empty (la : List 𝓕) :
    superCommuteCoef q la [] = 1 := by
  simp only [superCommuteCoef, ofList_empty, reduceCtorEq, and_false, ↓reduceIte]

lemma superCommuteCoef_append (la lb lc : List 𝓕) :
    superCommuteCoef q la (lb ++ lc) = superCommuteCoef q la lb * superCommuteCoef q la lc := by
  simp only [superCommuteCoef, Fin.isValue, ofList_append, ite_eq_right_iff, zero_ne_one, imp_false,
    mul_ite, mul_neg, mul_one]
  by_cases hla : ofList q la = fermionic
  · by_cases hlb : ofList q lb = fermionic
    · by_cases hlc : ofList q lc = fermionic
      · simp [hlc, hlb, hla]
      · have hc : ofList q lc = bosonic := by
          exact (neq_fermionic_iff_eq_bosonic (ofList q lc)).mp hlc
        simp [hc, hlb, hla]
    · have hb : ofList q lb = bosonic := by
        exact (neq_fermionic_iff_eq_bosonic (ofList q lb)).mp hlb
      by_cases hlc : ofList q lc = fermionic
      · simp [hlc, hb]
      · have hc : ofList q lc = bosonic := by
          exact (neq_fermionic_iff_eq_bosonic (ofList q lc)).mp hlc
        simp [hc, hb]
  · have ha : ofList q la = bosonic := by
      exact (neq_fermionic_iff_eq_bosonic (ofList q la)).mp hla
    simp [ha]

lemma superCommuteCoef_cons (i : 𝓕) (la lb : List 𝓕) :
    superCommuteCoef q la (i :: lb) = superCommuteCoef q la [i] * superCommuteCoef q la lb := by
  trans superCommuteCoef q la ([i] ++ lb)
  simp only [List.singleton_append]
  rw [superCommuteCoef_append]

end Wick
