/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.WickContraction.Sign.InsertNone
import HepLean.PerturbationTheory.WickContraction.Sign.InsertSome
import HepLean.PerturbationTheory.FieldOpAlgebra.NormalOrder.WickContractions
import HepLean.PerturbationTheory.FieldOpAlgebra.WickTerm
import HepLean.Meta.Remark.Basic
/-!

# Wick's theorem

This file contrains the time-dependent version of Wick's theorem
for lists of fields containing both fermions and bosons.

Wick's theorem is related to Isserlis' theorem in mathematics.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldOpFreeAlgebra
open FieldOpAlgebra
open HepLean.List
open WickContraction
open FieldStatistic

/-!

## Wick terms

-/

/-!

## Wick's theorem

-/

lemma wicks_theorem_congr {φs φs' : List 𝓕.FieldOp} (h : φs = φs') :
    ∑ (φsΛ : WickContraction φs.length), φsΛ.wickTerm
    = ∑ (φs'Λ : WickContraction φs'.length), φs'Λ.wickTerm := by
  subst h
  rfl

remark wicks_theorem_context := "
  In perturbation quantum field theory, Wick's theorem allows
  us to expand expectation values of time-ordered products of fields in terms of normal-orders
  and time contractions.
  The theorem is used to simplify the calculation of scattering amplitudes, and is the precurser
  to Feynman diagrams.

  There is are actually three different versions of Wick's theorem used.
  The static version, the time-dependent version, and the normal-ordered time-dependent version.
  HepLean contains a formalization of all three of these theorems in complete generality for
  mixtures of bosonic and fermionic fields.

  The statement of these theorems for bosons is simplier then when fermions are involved, since
  one does not have to worry about the minus-signs picked up on exchanging fields."

/-- Wick's theorem states that for a list of fields `φs = φ₀…φₙ`
`𝓣(φs) = ∑ φsΛ, (φsΛ.sign • φsΛ.timeContract) * 𝓝([φsΛ]ᵘᶜ)`
where the sum is over all Wick contractions `φsΛ` of `φs`.

The proof is via induction on `φs`. The base case `φs = []` is handled by `wicks_theorem_nil`.
The inductive step works as follows:
- The lemma `timeOrder_eq_maxTimeField_mul_finset` is used to write
  `𝓣(φ₀…φₙ)` as ` 𝓢(φᵢ,φ₀…φᵢ₋₁) • φᵢ * 𝓣(φ₀…φᵢ₋₁φᵢ₊₁φₙ)` where `φᵢ` is
  the maximal time field in `φ₀…φₙ`.
- The induction hypothesis is used to expand `𝓣(φ₀…φᵢ₋₁φᵢ₊₁φₙ)` as a sum over Wick contractions of
  `φ₀…φᵢ₋₁φᵢ₊₁φₙ`.
- Further the lemmas `wick_term_cons_eq_sum_wick_term` and `insertLift_sum` are used.
-/
theorem wicks_theorem : (φs : List 𝓕.FieldOp) → 𝓣(ofFieldOpList φs) =
    ∑ (φsΛ : WickContraction φs.length), φsΛ.wickTerm
  | [] => by
    rw [timeOrder_ofFieldOpList_nil]
    simp only [map_one, List.length_nil, Algebra.smul_mul_assoc]
    rw [sum_WickContraction_nil]
    simp
  | φ :: φs => by
    have ih := wicks_theorem (eraseMaxTimeField φ φs)
    conv_lhs => rw [timeOrder_eq_maxTimeField_mul_finset, ih, Finset.mul_sum]
    have h1 : φ :: φs =
        (eraseMaxTimeField φ φs).insertIdx (maxTimeFieldPosFin φ φs) (maxTimeField φ φs) := by
      simp only [eraseMaxTimeField, insertionSortDropMinPos, List.length_cons, Nat.succ_eq_add_one,
        maxTimeField, insertionSortMin, List.get_eq_getElem]
      erw [insertIdx_eraseIdx_fin]
    conv_rhs => rw [wicks_theorem_congr h1]
    conv_rhs => rw [insertLift_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Algebra.smul_mul_assoc, mul_wickTerm_eq_sum
      (maxTimeField φ φs) (eraseMaxTimeField φ φs) (maxTimeFieldPosFin φ φs) c]
    trans (1 : ℂ) • ∑ k : Option { x // x ∈ c.uncontracted },
      (c ↩Λ (maxTimeField φ φs) (maxTimeFieldPosFin φ φs) k).wickTerm
    swap
    · simp [uncontractedListGet]
    rw [smul_smul]
    simp only [instCommGroup.eq_1, exchangeSign_mul_self, Nat.succ_eq_add_one,
      Algebra.smul_mul_assoc, Fintype.sum_option, timeContract_insert_none,
      Finset.univ_eq_attach, smul_add, one_smul, uncontractedListGet]
    · exact fun k => timeOrder_maxTimeField _ _ k
    · exact fun k => lt_maxTimeFieldPosFin_not_timeOrder _ _ k
termination_by φs => φs.length

end FieldSpecification
