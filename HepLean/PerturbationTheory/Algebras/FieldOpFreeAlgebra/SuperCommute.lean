/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.FieldOpFreeAlgebra.Basic
import HepLean.PerturbationTheory.Algebras.FieldOpFreeAlgebra.Grading
/-!

# Super Commute
-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

namespace FieldOpFreeAlgebra

/-!

## The super commutor on the FieldOpFreeAlgebra.

-/

open FieldStatistic

/-- The super commutor on the creation and annihlation algebra. For two bosonic operators
  or a bosonic and fermionic operator this corresponds to the usual commutator
  whilst for two fermionic operators this corresponds to the anti-commutator. -/
noncomputable def superCommuteF : 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] 𝓕.FieldOpFreeAlgebra →ₗ[ℂ] 𝓕.FieldOpFreeAlgebra :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  Basis.constr ofCrAnListBasis ℂ fun φs' =>
  ofCrAnList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList (φs' ++ φs)

/-- The super commutor on the creation and annihlation algebra. For two bosonic operators
  or a bosonic and fermionic operator this corresponds to the usual commutator
  whilst for two fermionic operators this corresponds to the anti-commutator. -/
scoped[FieldSpecification.FieldOpFreeAlgebra] notation "[" φs "," φs' "]ₛca" => superCommuteF φs φs'

/-!

## The super commutor of different types of elements

-/

lemma superCommuteF_ofCrAnList_ofCrAnList (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnList φs, ofCrAnList φs']ₛca =
    ofCrAnList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList (φs' ++ φs) := by
  rw [← ofListBasis_eq_ofList, ← ofListBasis_eq_ofList]
  simp only [superCommuteF, Basis.constr_basis]

lemma superCommuteF_ofCrAnState_ofCrAnState (φ φ' : 𝓕.CrAnStates) :
    [ofCrAnState φ, ofCrAnState φ']ₛca =
    ofCrAnState φ * ofCrAnState φ' - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofCrAnState φ' * ofCrAnState φ := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rw [superCommuteF_ofCrAnList_ofCrAnList, ofCrAnList_append]
  congr
  rw [ofCrAnList_append]
  rw [FieldStatistic.ofList_singleton, FieldStatistic.ofList_singleton, smul_mul_assoc]

lemma superCommuteF_ofCrAnList_ofStatesList (φcas : List 𝓕.CrAnStates) (φs : List 𝓕.States) :
    [ofCrAnList φcas, ofStateList φs]ₛca = ofCrAnList φcas * ofStateList φs -
    𝓢(𝓕 |>ₛ φcas, 𝓕 |>ₛ φs) • ofStateList φs * ofCrAnList φcas := by
  conv_lhs => rw [ofStateList_sum]
  rw [map_sum]
  conv_lhs =>
    enter [2, x]
    rw [superCommuteF_ofCrAnList_ofCrAnList, CrAnSection.statistics_eq_state_statistics,
      ofCrAnList_append, ofCrAnList_append]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.smul_sum,
    ← Finset.sum_mul, ← ofStateList_sum]
  simp

lemma superCommuteF_ofStateList_ofStatesList (φ : List 𝓕.States) (φs : List 𝓕.States) :
    [ofStateList φ, ofStateList φs]ₛca = ofStateList φ * ofStateList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofStateList φs * ofStateList φ := by
  conv_lhs => rw [ofStateList_sum]
  simp only [map_sum, LinearMap.coeFn_sum, Finset.sum_apply, instCommGroup.eq_1,
    Algebra.smul_mul_assoc]
  conv_lhs =>
    enter [2, x]
    rw [superCommuteF_ofCrAnList_ofStatesList]
  simp only [instCommGroup.eq_1, CrAnSection.statistics_eq_state_statistics,
    Algebra.smul_mul_assoc, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.smul_sum, ← Finset.mul_sum, ← ofStateList_sum]

lemma superCommuteF_ofState_ofStatesList (φ : 𝓕.States) (φs : List 𝓕.States) :
    [ofState φ, ofStateList φs]ₛca = ofState φ * ofStateList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofStateList φs * ofState φ := by
  rw [← ofStateList_singleton, superCommuteF_ofStateList_ofStatesList, ofStateList_singleton]
  simp

lemma superCommuteF_ofStateList_ofState (φs : List 𝓕.States) (φ : 𝓕.States) :
    [ofStateList φs, ofState φ]ₛca = ofStateList φs * ofState φ -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofState φ * ofStateList φs := by
  rw [← ofStateList_singleton, superCommuteF_ofStateList_ofStatesList, ofStateList_singleton]
  simp

lemma superCommuteF_anPartF_crPartF (φ φ' : 𝓕.States) :
    [anPartF φ, crPartF φ']ₛca = anPartF φ * crPartF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPartF φ' * anPartF φ := by
  match φ, φ' with
  | States.inAsymp φ, _ =>
    simp
  | _, States.outAsymp φ =>
    simp only [crPartF_posAsymp, map_zero, mul_zero, instCommGroup.eq_1, smul_zero, zero_mul,
      sub_self]
  | States.position φ, States.position φ' =>
    simp only [anPartF_position, crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.outAsymp φ, States.position φ' =>
    simp only [anPartF_posAsymp, crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.position φ, States.inAsymp φ' =>
    simp only [anPartF_position, crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp only [List.singleton_append, instCommGroup.eq_1, crAnStatistics,
      FieldStatistic.ofList_singleton, Function.comp_apply, crAnStatesToStates_prod, ←
      ofCrAnList_append]
  | States.outAsymp φ, States.inAsymp φ' =>
    simp only [anPartF_posAsymp, crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommuteF_crPartF_anPartF (φ φ' : 𝓕.States) :
    [crPartF φ, anPartF φ']ₛca = crPartF φ * anPartF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPartF φ' * crPartF φ := by
    match φ, φ' with
    | States.outAsymp φ, _ =>
    simp only [crPartF_posAsymp, map_zero, LinearMap.zero_apply, zero_mul, instCommGroup.eq_1,
      mul_zero, sub_self]
    | _, States.inAsymp φ =>
    simp only [anPartF_negAsymp, map_zero, mul_zero, instCommGroup.eq_1, smul_zero, zero_mul,
      sub_self]
    | States.position φ, States.position φ' =>
    simp only [crPartF_position, anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
    | States.position φ, States.outAsymp φ' =>
    simp only [crPartF_position, anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
    | States.inAsymp φ, States.position φ' =>
    simp only [crPartF_negAsymp, anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
    | States.inAsymp φ, States.outAsymp φ' =>
    simp only [crPartF_negAsymp, anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommuteF_crPartF_crPartF (φ φ' : 𝓕.States) :
    [crPartF φ, crPartF φ']ₛca = crPartF φ * crPartF φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPartF φ' * crPartF φ := by
  match φ, φ' with
  | States.outAsymp φ, _ =>
  simp only [crPartF_posAsymp, map_zero, LinearMap.zero_apply, zero_mul, instCommGroup.eq_1,
    mul_zero, sub_self]
  | _, States.outAsymp φ =>
  simp only [crPartF_posAsymp, map_zero, mul_zero, instCommGroup.eq_1, smul_zero, zero_mul,
    sub_self]
  | States.position φ, States.position φ' =>
  simp only [crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.position φ, States.inAsymp φ' =>
  simp only [crPartF_position, crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.inAsymp φ, States.position φ' =>
  simp only [crPartF_negAsymp, crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.inAsymp φ, States.inAsymp φ' =>
  simp only [crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommuteF_anPartF_anPartF (φ φ' : 𝓕.States) :
    [anPartF φ, anPartF φ']ₛca =
    anPartF φ * anPartF φ' - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPartF φ' * anPartF φ := by
  match φ, φ' with
  | States.inAsymp φ, _ =>
    simp
  | _, States.inAsymp φ =>
    simp
  | States.position φ, States.position φ' =>
    simp only [anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.position φ, States.outAsymp φ' =>
    simp only [anPartF_position, anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.outAsymp φ, States.position φ' =>
    simp only [anPartF_posAsymp, anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.outAsymp φ, States.outAsymp φ' =>
    simp only [anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommuteF_crPartF_ofStateList (φ : 𝓕.States) (φs : List 𝓕.States) :
    [crPartF φ, ofStateList φs]ₛca =
    crPartF φ * ofStateList φs - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofStateList φs *
    crPartF φ := by
  match φ with
  | States.inAsymp φ =>
    simp only [crPartF_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofStatesList]
    simp [crAnStatistics]
  | States.position φ =>
    simp only [crPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofStatesList]
    simp [crAnStatistics]
  | States.outAsymp φ =>
    simp

lemma superCommuteF_anPartF_ofStateList (φ : 𝓕.States) (φs : List 𝓕.States) :
    [anPartF φ, ofStateList φs]ₛca =
    anPartF φ * ofStateList φs - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) •
    ofStateList φs * anPartF φ := by
  match φ with
  | States.inAsymp φ =>
    simp
  | States.position φ =>
    simp only [anPartF_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofStatesList]
    simp [crAnStatistics]
  | States.outAsymp φ =>
    simp only [anPartF_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofStatesList]
    simp [crAnStatistics]

lemma superCommuteF_crPartF_ofState (φ φ' : 𝓕.States) :
    [crPartF φ, ofState φ']ₛca =
    crPartF φ * ofState φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofState φ' * crPartF φ := by
  rw [← ofStateList_singleton, superCommuteF_crPartF_ofStateList]
  simp

lemma superCommuteF_anPartF_ofState (φ φ' : 𝓕.States) :
    [anPartF φ, ofState φ']ₛca =
    anPartF φ * ofState φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofState φ' * anPartF φ := by
  rw [← ofStateList_singleton, superCommuteF_anPartF_ofStateList]
  simp

/-!

## Mul equal superCommuteF

Lemmas which rewrite a multiplication of two elements of the algebra as their commuted
multiplication with a sign plus the super commutor.

-/
lemma ofCrAnList_mul_ofCrAnList_eq_superCommuteF (φs φs' : List 𝓕.CrAnStates) :
    ofCrAnList φs * ofCrAnList φs' = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnList φs
    + [ofCrAnList φs, ofCrAnList φs']ₛca := by
  rw [superCommuteF_ofCrAnList_ofCrAnList]
  simp [ofCrAnList_append]

lemma ofCrAnState_mul_ofCrAnList_eq_superCommuteF (φ : 𝓕.CrAnStates) (φs' : List 𝓕.CrAnStates) :
    ofCrAnState φ * ofCrAnList φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnState φ
    + [ofCrAnState φ, ofCrAnList φs']ₛca := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofCrAnList_eq_superCommuteF]
  simp

lemma ofStateList_mul_ofStateList_eq_superCommuteF (φs φs' : List 𝓕.States) :
    ofStateList φs * ofStateList φs' = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofStateList φs' * ofStateList φs
    + [ofStateList φs, ofStateList φs']ₛca := by
  rw [superCommuteF_ofStateList_ofStatesList]
  simp

lemma ofState_mul_ofStateList_eq_superCommuteF (φ : 𝓕.States) (φs' : List 𝓕.States) :
    ofState φ * ofStateList φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofStateList φs' * ofState φ
    + [ofState φ, ofStateList φs']ₛca := by
  rw [superCommuteF_ofState_ofStatesList]
  simp

lemma ofStateList_mul_ofState_eq_superCommuteF (φs : List 𝓕.States) (φ : 𝓕.States) :
    ofStateList φs * ofState φ = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofState φ * ofStateList φs
    + [ofStateList φs, ofState φ]ₛca := by
  rw [superCommuteF_ofStateList_ofState]
  simp

lemma crPartF_mul_anPartF_eq_superCommuteF (φ φ' : 𝓕.States) :
    crPartF φ * anPartF φ' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPartF φ' * crPartF φ +
    [crPartF φ, anPartF φ']ₛca := by
  rw [superCommuteF_crPartF_anPartF]
  simp

lemma anPartF_mul_crPartF_eq_superCommuteF (φ φ' : 𝓕.States) :
    anPartF φ * crPartF φ' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    crPartF φ' * anPartF φ +
    [anPartF φ, crPartF φ']ₛca := by
  rw [superCommuteF_anPartF_crPartF]
  simp

lemma crPartF_mul_crPartF_eq_superCommuteF (φ φ' : 𝓕.States) :
    crPartF φ * crPartF φ' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPartF φ' * crPartF φ +
    [crPartF φ, crPartF φ']ₛca := by
  rw [superCommuteF_crPartF_crPartF]
  simp

lemma anPartF_mul_anPartF_eq_superCommuteF (φ φ' : 𝓕.States) :
    anPartF φ * anPartF φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPartF φ' * anPartF φ +
    [anPartF φ, anPartF φ']ₛca := by
  rw [superCommuteF_anPartF_anPartF]
  simp

lemma ofCrAnList_mul_ofStateList_eq_superCommuteF (φs : List 𝓕.CrAnStates) (φs' : List 𝓕.States) :
    ofCrAnList φs * ofStateList φs' = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofStateList φs' * ofCrAnList φs
    + [ofCrAnList φs, ofStateList φs']ₛca := by
  rw [superCommuteF_ofCrAnList_ofStatesList]
  simp

/-!

## Symmetry of the super commutor.

-/

lemma superCommuteF_ofCrAnList_ofCrAnList_symm (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnList φs, ofCrAnList φs']ₛca =
    (- 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs')) • [ofCrAnList φs', ofCrAnList φs]ₛca := by
  rw [superCommuteF_ofCrAnList_ofCrAnList, superCommuteF_ofCrAnList_ofCrAnList, smul_sub]
  simp only [instCommGroup.eq_1, neg_smul, sub_neg_eq_add]
  rw [smul_smul]
  conv_rhs =>
    rhs
    rw [exchangeSign_symm, exchangeSign_mul_self]
  simp only [one_smul]
  abel

lemma superCommuteF_ofCrAnState_ofCrAnState_symm (φ φ' : 𝓕.CrAnStates) :
    [ofCrAnState φ, ofCrAnState φ']ₛca =
    (- 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ')) • [ofCrAnState φ', ofCrAnState φ]ₛca := by
  rw [superCommuteF_ofCrAnState_ofCrAnState, superCommuteF_ofCrAnState_ofCrAnState]
  rw [smul_sub]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc, neg_smul, sub_neg_eq_add]
  rw [smul_smul]
  conv_rhs =>
    rhs
    rw [exchangeSign_symm, exchangeSign_mul_self]
  simp only [one_smul]
  abel

/-!

## Splitting the super commutor on lists into sums.

-/

lemma superCommuteF_ofCrAnList_ofCrAnList_cons (φ : 𝓕.CrAnStates) (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnList φs, ofCrAnList (φ :: φs')]ₛca =
    [ofCrAnList φs, ofCrAnState φ]ₛca * ofCrAnList φs' +
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ)
    • ofCrAnState φ * [ofCrAnList φs, ofCrAnList φs']ₛca := by
  rw [superCommuteF_ofCrAnList_ofCrAnList]
  conv_rhs =>
    lhs
    rw [← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList, sub_mul, ← ofCrAnList_append]
    rhs
    rw [FieldStatistic.ofList_singleton, ofCrAnList_append, ofCrAnList_singleton, smul_mul_assoc,
      mul_assoc, ← ofCrAnList_append]
  conv_rhs =>
    rhs
    rw [superCommuteF_ofCrAnList_ofCrAnList, mul_sub, smul_mul_assoc]
  simp only [instCommGroup.eq_1, List.cons_append, List.append_assoc, List.nil_append,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, sub_add_sub_cancel, sub_right_inj]
  rw [← ofCrAnList_cons, smul_smul, FieldStatistic.ofList_cons_eq_mul]
  simp only [instCommGroup, map_mul, mul_comm]

lemma superCommuteF_ofCrAnList_ofStateList_cons (φ : 𝓕.States) (φs : List 𝓕.CrAnStates)
    (φs' : List 𝓕.States) : [ofCrAnList φs, ofStateList (φ :: φs')]ₛca =
    [ofCrAnList φs, ofState φ]ₛca * ofStateList φs' +
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofState φ * [ofCrAnList φs, ofStateList φs']ₛca := by
  rw [superCommuteF_ofCrAnList_ofStatesList]
  conv_rhs =>
    lhs
    rw [← ofStateList_singleton, superCommuteF_ofCrAnList_ofStatesList, sub_mul, mul_assoc,
      ← ofStateList_append]
    rhs
    rw [FieldStatistic.ofList_singleton, ofStateList_singleton, smul_mul_assoc,
      smul_mul_assoc, mul_assoc]
  conv_rhs =>
    rhs
    rw [superCommuteF_ofCrAnList_ofStatesList, mul_sub, smul_mul_assoc]
  simp only [instCommGroup, Algebra.smul_mul_assoc, List.singleton_append, Algebra.mul_smul_comm,
    sub_add_sub_cancel, sub_right_inj]
  rw [ofStateList_cons, mul_assoc, smul_smul, FieldStatistic.ofList_cons_eq_mul]
  simp [mul_comm]

/--
Within the creation and annihilation algebra, we have that
`[φᶜᵃs, φᶜᵃ₀ … φᶜᵃₙ]ₛca = ∑ i, sᵢ • φᶜᵃs₀ … φᶜᵃᵢ₋₁ * [φᶜᵃs, φᶜᵃᵢ]ₛca * φᶜᵃᵢ₊₁ … φᶜᵃₙ`
where `sᵢ` is the exchange sign for `φᶜᵃs` and `φᶜᵃs₀ … φᶜᵃᵢ₋₁`.
-/
lemma superCommuteF_ofCrAnList_ofCrAnList_eq_sum (φs : List 𝓕.CrAnStates) :
    (φs' : List 𝓕.CrAnStates) → [ofCrAnList φs, ofCrAnList φs']ₛca =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
    ofCrAnList (φs'.take n) * [ofCrAnList φs, ofCrAnState (φs'.get n)]ₛca *
    ofCrAnList (φs'.drop (n + 1))
  | [] => by
    simp [← ofCrAnList_nil, superCommuteF_ofCrAnList_ofCrAnList]
  | φ :: φs' => by
    rw [superCommuteF_ofCrAnList_ofCrAnList_cons, superCommuteF_ofCrAnList_ofCrAnList_eq_sum φs φs']
    conv_rhs => erw [Fin.sum_univ_succ]
    congr 1
    · simp
    · simp [Finset.mul_sum, smul_smul, ofCrAnList_cons, mul_assoc,
        FieldStatistic.ofList_cons_eq_mul, mul_comm]

lemma superCommuteF_ofCrAnList_ofStateList_eq_sum (φs : List 𝓕.CrAnStates) : (φs' : List 𝓕.States) →
    [ofCrAnList φs, ofStateList φs']ₛca =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
      ofStateList (φs'.take n) * [ofCrAnList φs, ofState (φs'.get n)]ₛca *
      ofStateList (φs'.drop (n + 1))
  | [] => by
    simp only [superCommuteF_ofCrAnList_ofStatesList, instCommGroup, ofList_empty,
      exchangeSign_bosonic, one_smul, List.length_nil, Finset.univ_eq_empty, List.take_nil,
      List.get_eq_getElem, List.drop_nil, Finset.sum_empty]
    simp
  | φ :: φs' => by
    rw [superCommuteF_ofCrAnList_ofStateList_cons,
      superCommuteF_ofCrAnList_ofStateList_eq_sum φs φs']
    conv_rhs => erw [Fin.sum_univ_succ]
    congr 1
    · simp
    · simp [Finset.mul_sum, smul_smul, ofStateList_cons, mul_assoc,
        FieldStatistic.ofList_cons_eq_mul, mul_comm]

lemma summerCommute_jacobi_ofCrAnList (φs1 φs2 φs3 : List 𝓕.CrAnStates) :
    [ofCrAnList φs1, [ofCrAnList φs2, ofCrAnList φs3]ₛca]ₛca =
    𝓢(𝓕 |>ₛ φs1, 𝓕 |>ₛ φs3) •
    (- 𝓢(𝓕 |>ₛ φs2, 𝓕 |>ₛ φs3) • [ofCrAnList φs3, [ofCrAnList φs1, ofCrAnList φs2]ₛca]ₛca -
    𝓢(𝓕 |>ₛ φs1, 𝓕 |>ₛ φs2) • [ofCrAnList φs2, [ofCrAnList φs3, ofCrAnList φs1]ₛca]ₛca) := by
  repeat rw [superCommuteF_ofCrAnList_ofCrAnList]
  simp only [instCommGroup, map_sub, map_smul, neg_smul]
  repeat rw [superCommuteF_ofCrAnList_ofCrAnList]
  simp only [instCommGroup.eq_1, ofList_append_eq_mul, List.append_assoc]
  by_cases h1 : (𝓕 |>ₛ φs1) = bosonic <;>
    by_cases h2 : (𝓕 |>ₛ φs2) = bosonic <;>
    by_cases h3 : (𝓕 |>ₛ φs3) = bosonic
  · simp only [h1, h2, h3, mul_self, bosonic_exchangeSign, one_smul, exchangeSign_bosonic, neg_sub]
    abel
  · simp only [h1, h2, bosonic_exchangeSign, one_smul, mul_bosonic, mul_self, map_one,
    exchangeSign_bosonic, neg_sub]
    abel
  · simp only [h1, h3, mul_bosonic, bosonic_exchangeSign, one_smul, exchangeSign_bosonic, neg_sub,
    mul_self, map_one]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, mul_self, bosonic_exchangeSign, one_smul,
      fermionic_exchangeSign_fermionic, neg_smul, neg_sub, bosonic_mul_fermionic, sub_neg_eq_add,
      mul_bosonic, smul_add, exchangeSign_bosonic]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, mul_self, map_one, one_smul, exchangeSign_bosonic, mul_bosonic,
      bosonic_exchangeSign, bosonic_mul_fermionic, neg_sub]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, bosonic_mul_fermionic, fermionic_exchangeSign_fermionic, neg_smul,
      one_smul, sub_neg_eq_add, bosonic_exchangeSign, mul_bosonic, smul_add, exchangeSign_bosonic,
      neg_sub, mul_self]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, mul_bosonic, fermionic_exchangeSign_fermionic, neg_smul, one_smul,
      sub_neg_eq_add, exchangeSign_bosonic, bosonic_mul_fermionic, smul_add, mul_self,
      bosonic_exchangeSign, neg_sub]
    abel
  · simp only [neq_bosonic_iff_eq_fermionic] at h1 h2 h3
    simp only [h1, h2, h3, mul_self, map_one, one_smul, fermionic_exchangeSign_fermionic, neg_smul,
      neg_sub]
    abel

/-!

## Interaction with grading.

-/

lemma superCommuteF_grade {a b : 𝓕.FieldOpFreeAlgebra} {f1 f2 : FieldStatistic}
    (ha : a ∈ statisticSubmodule f1) (hb : b ∈ statisticSubmodule f2) :
    [a, b]ₛca ∈ statisticSubmodule (f1 + f2) := by
  let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule f2) : Prop :=
    [a, a2]ₛca ∈ statisticSubmodule (f1 + f2)
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    simp only [add_eq_mul, instCommGroup, p]
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule f1) : Prop :=
        [a2, ofCrAnList φs]ₛca ∈ statisticSubmodule (f1 + f2)
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp only [add_eq_mul, instCommGroup, p]
      rw [superCommuteF_ofCrAnList_ofCrAnList]
      apply Submodule.sub_mem _
      · apply ofCrAnList_mem_statisticSubmodule_of
        rw [ofList_append_eq_mul, hφs, hφs']
      · apply Submodule.smul_mem
        apply ofCrAnList_mem_statisticSubmodule_of
        rw [ofList_append_eq_mul, hφs, hφs']
        rw [mul_comm]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp only [add_eq_mul, instCommGroup, map_add, LinearMap.add_apply, p]
      exact Submodule.add_mem _ hp1 hp2
    · intro c x hx hp1
      simp only [add_eq_mul, instCommGroup, map_smul, LinearMap.smul_apply, p]
      exact Submodule.smul_mem _ c hp1
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp only [add_eq_mul, instCommGroup, map_add, p]
    exact Submodule.add_mem _ hp1 hp2
  · intro c x hx hp1
    simp only [add_eq_mul, instCommGroup, map_smul, p]
    exact Submodule.smul_mem _ c hp1
  · exact hb

lemma superCommuteF_bosonic_bosonic {a b : 𝓕.FieldOpFreeAlgebra}
    (ha : a ∈ statisticSubmodule bosonic) (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
    [a, a2]ₛca = a * a2 - a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
        [a2, ofCrAnList φs]ₛca = a2 * ofCrAnList φs - ofCrAnList φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp only [p]
      rw [superCommuteF_ofCrAnList_ofCrAnList]
      simp [hφs, ofCrAnList_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all only [p, map_add, LinearMap.add_apply, add_mul, mul_add]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all only [p, map_add, mul_add, add_mul]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb

lemma superCommuteF_bosonic_fermionic {a b : 𝓕.FieldOpFreeAlgebra}
    (ha : a ∈ statisticSubmodule bosonic) (hb : b ∈ statisticSubmodule fermionic) :
    [a, b]ₛca = a * b - b * a := by
  let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
    [a, a2]ₛca = a * a2 - a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
        [a2, ofCrAnList φs]ₛca = a2 * ofCrAnList φs - ofCrAnList φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp only [p]
      rw [superCommuteF_ofCrAnList_ofCrAnList]
      simp [hφs, hφs', ofCrAnList_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all only [p, map_add, LinearMap.add_apply, add_mul, mul_add]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all only [p, map_add, mul_add, add_mul]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb

lemma superCommuteF_fermionic_bonsonic {a b : 𝓕.FieldOpFreeAlgebra}
    (ha : a ∈ statisticSubmodule fermionic) (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
    [a, a2]ₛca = a * a2 - a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
        [a2, ofCrAnList φs]ₛca = a2 * ofCrAnList φs - ofCrAnList φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp only [p]
      rw [superCommuteF_ofCrAnList_ofCrAnList]
      simp [hφs, hφs', ofCrAnList_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all only [p, map_add, LinearMap.add_apply, add_mul, mul_add]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all only [map_add, mul_add, add_mul, p]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb

lemma superCommuteF_bonsonic {a b : 𝓕.FieldOpFreeAlgebra} (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  rw [← bosonicProj_add_fermionicProj a]
  simp only [map_add, LinearMap.add_apply]
  rw [superCommuteF_bosonic_bosonic (by simp) hb, superCommuteF_fermionic_bonsonic (by simp) hb]
  simp only [add_mul, mul_add]
  abel

lemma bosonic_superCommuteF {a b : 𝓕.FieldOpFreeAlgebra} (ha : a ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  rw [← bosonicProj_add_fermionicProj b]
  simp only [map_add, LinearMap.add_apply]
  rw [superCommuteF_bosonic_bosonic ha (by simp), superCommuteF_bosonic_fermionic ha (by simp)]
  simp only [add_mul, mul_add]
  abel

lemma superCommuteF_bonsonic_symm {a b : 𝓕.FieldOpFreeAlgebra} (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = - [b, a]ₛca := by
  rw [bosonic_superCommuteF hb, superCommuteF_bonsonic hb]
  simp

lemma bonsonic_superCommuteF_symm {a b : 𝓕.FieldOpFreeAlgebra} (ha : a ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = - [b, a]ₛca := by
  rw [bosonic_superCommuteF ha, superCommuteF_bonsonic ha]
  simp

lemma superCommuteF_fermionic_fermionic {a b : 𝓕.FieldOpFreeAlgebra}
    (ha : a ∈ statisticSubmodule fermionic) (hb : b ∈ statisticSubmodule fermionic) :
    [a, b]ₛca = a * b + b * a := by
  let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
    [a, a2]ₛca = a * a2 + a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.FieldOpFreeAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
        [a2, ofCrAnList φs]ₛca = a2 * ofCrAnList φs + ofCrAnList φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp only [p]
      rw [superCommuteF_ofCrAnList_ofCrAnList]
      simp [hφs, hφs', ofCrAnList_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all only [p, map_add, LinearMap.add_apply, add_mul, mul_add]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all only [map_add, mul_add, add_mul, p]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb

lemma superCommuteF_fermionic_fermionic_symm {a b : 𝓕.FieldOpFreeAlgebra}
    (ha : a ∈ statisticSubmodule fermionic) (hb : b ∈ statisticSubmodule fermionic) :
    [a, b]ₛca = [b, a]ₛca := by
  rw [superCommuteF_fermionic_fermionic ha hb]
  rw [superCommuteF_fermionic_fermionic hb ha]
  abel

lemma superCommuteF_expand_bosonicProj_fermionicProj (a b : 𝓕.FieldOpFreeAlgebra) :
    [a, b]ₛca = bosonicProj a * bosonicProj b - bosonicProj b * bosonicProj a +
    bosonicProj a * fermionicProj b - fermionicProj b * bosonicProj a +
    fermionicProj a * bosonicProj b - bosonicProj b * fermionicProj a +
    fermionicProj a * fermionicProj b + fermionicProj b * fermionicProj a := by
  conv_lhs => rw [← bosonicProj_add_fermionicProj a, ← bosonicProj_add_fermionicProj b]
  simp only [map_add, LinearMap.add_apply]
  rw [superCommuteF_bonsonic (by simp),
      superCommuteF_fermionic_bonsonic (by simp) (by simp),
      superCommuteF_bosonic_fermionic (by simp) (by simp),
      superCommuteF_fermionic_fermionic (by simp) (by simp)]
  abel

lemma superCommuteF_ofCrAnList_ofCrAnList_bosonic_or_fermionic (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnList φs, ofCrAnList φs']ₛca ∈ statisticSubmodule bosonic ∨
    [ofCrAnList φs, ofCrAnList φs']ₛca ∈ statisticSubmodule fermionic := by
  by_cases h1 : (𝓕 |>ₛ φs) = bosonic <;> by_cases h2 : (𝓕 |>ₛ φs') = bosonic
  · left
    have h : bosonic = bosonic + bosonic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommuteF_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ h1
    apply ofCrAnList_mem_statisticSubmodule_of _ _ h2
  · right
    have h : fermionic = bosonic + fermionic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommuteF_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ h1
    apply ofCrAnList_mem_statisticSubmodule_of _ _ (by simpa using h2)
  · right
    have h : fermionic = fermionic + bosonic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommuteF_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ (by simpa using h1)
    apply ofCrAnList_mem_statisticSubmodule_of _ _ h2
  · left
    have h : bosonic = fermionic + fermionic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommuteF_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ (by simpa using h1)
    apply ofCrAnList_mem_statisticSubmodule_of _ _ (by simpa using h2)

lemma superCommuteF_ofCrAnState_ofCrAnState_bosonic_or_fermionic (φ φ' : 𝓕.CrAnStates) :
    [ofCrAnState φ, ofCrAnState φ']ₛca ∈ statisticSubmodule bosonic ∨
    [ofCrAnState φ, ofCrAnState φ']ₛca ∈ statisticSubmodule fermionic := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton]
  exact superCommuteF_ofCrAnList_ofCrAnList_bosonic_or_fermionic [φ] [φ']

lemma superCommuteF_superCommuteF_ofCrAnState_bosonic_or_fermionic (φ1 φ2 φ3 : 𝓕.CrAnStates) :
    [ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca ∈ statisticSubmodule bosonic ∨
    [ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca ∈ statisticSubmodule fermionic := by
  rcases superCommuteF_ofCrAnState_ofCrAnState_bosonic_or_fermionic φ2 φ3 with hs | hs
    <;> rcases ofCrAnState_bosonic_or_fermionic φ1 with h1 | h1
  · left
    have h : bosonic = bosonic + bosonic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommuteF_grade h1 hs
  · right
    have h : fermionic = fermionic + bosonic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommuteF_grade h1 hs
  · right
    have h : fermionic = bosonic + fermionic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommuteF_grade h1 hs
  · left
    have h : bosonic = fermionic + fermionic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommuteF_grade h1 hs

lemma superCommuteF_bosonic_ofCrAnList_eq_sum (a : 𝓕.FieldOpFreeAlgebra) (φs : List 𝓕.CrAnStates)
    (ha : a ∈ statisticSubmodule bosonic) :
    [a, ofCrAnList φs]ₛca = ∑ (n : Fin φs.length),
      ofCrAnList (φs.take n) * [a, ofCrAnState (φs.get n)]ₛca *
      ofCrAnList (φs.drop (n + 1)) := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (ha : a ∈ statisticSubmodule bosonic) : Prop :=
      [a, ofCrAnList φs]ₛca = ∑ (n : Fin φs.length),
      ofCrAnList (φs.take n) * [a, ofCrAnState (φs.get n)]ₛca *
      ofCrAnList (φs.drop (n + 1))
  change p a ha
  apply Submodule.span_induction (p := p)
  · intro a ha
    obtain ⟨φs, rfl, hφs⟩ := ha
    simp only [List.get_eq_getElem, p]
    rw [superCommuteF_ofCrAnList_ofCrAnList_eq_sum]
    congr
    funext n
    simp [hφs]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all only [List.get_eq_getElem, map_add, LinearMap.add_apply, p]
    rw [← Finset.sum_add_distrib]
    congr
    funext n
    simp [mul_add, add_mul]
  · intro c x hx hpx
    simp_all [p, Finset.smul_sum]
  · exact ha

lemma superCommuteF_fermionic_ofCrAnList_eq_sum (a : 𝓕.FieldOpFreeAlgebra) (φs : List 𝓕.CrAnStates)
    (ha : a ∈ statisticSubmodule fermionic) :
    [a, ofCrAnList φs]ₛca = ∑ (n : Fin φs.length), 𝓢(fermionic, 𝓕 |>ₛ φs.take n) •
      ofCrAnList (φs.take n) * [a, ofCrAnState (φs.get n)]ₛca *
      ofCrAnList (φs.drop (n + 1)) := by
  let p (a : 𝓕.FieldOpFreeAlgebra) (ha : a ∈ statisticSubmodule fermionic) : Prop :=
      [a, ofCrAnList φs]ₛca = ∑ (n : Fin φs.length), 𝓢(fermionic, 𝓕 |>ₛ φs.take n) •
      ofCrAnList (φs.take n) * [a, ofCrAnState (φs.get n)]ₛca *
      ofCrAnList (φs.drop (n + 1))
  change p a ha
  apply Submodule.span_induction (p := p)
  · intro a ha
    obtain ⟨φs, rfl, hφs⟩ := ha
    simp only [instCommGroup, List.get_eq_getElem, Algebra.smul_mul_assoc, p]
    rw [superCommuteF_ofCrAnList_ofCrAnList_eq_sum]
    congr
    funext n
    simp [hφs]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all only [p, instCommGroup, List.get_eq_getElem, Algebra.smul_mul_assoc, map_add,
      LinearMap.add_apply]
    rw [← Finset.sum_add_distrib]
    congr
    funext n
    simp [mul_add, add_mul]
  · intro c x hx hpx
    simp_all only [p, instCommGroup, List.get_eq_getElem, Algebra.smul_mul_assoc, map_smul,
      LinearMap.smul_apply, Finset.smul_sum, Algebra.mul_smul_comm]
    congr
    funext x
    simp [smul_smul, mul_comm]
  · exact ha

lemma statistic_neq_of_superCommuteF_fermionic {φs φs' : List 𝓕.CrAnStates}
    (h : [ofCrAnList φs, ofCrAnList φs']ₛca ∈ statisticSubmodule fermionic) :
    (𝓕 |>ₛ φs) ≠ (𝓕 |>ₛ φs') ∨ [ofCrAnList φs, ofCrAnList φs']ₛca = 0 := by
  by_cases h0 : [ofCrAnList φs, ofCrAnList φs']ₛca = 0
  · simp [h0]
  simp only [ne_eq, h0, or_false]
  by_contra hn
  refine h0 (eq_zero_of_bosonic_and_fermionic ?_ h)
  by_cases hc : (𝓕 |>ₛ φs) = bosonic
  · have h1 : bosonic = bosonic + bosonic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h1]
    apply superCommuteF_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ hc
    apply ofCrAnList_mem_statisticSubmodule_of _ _
    rw [← hn, hc]
  · have h1 : bosonic = fermionic + fermionic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h1]
    apply superCommuteF_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _
    simpa using hc
    apply ofCrAnList_mem_statisticSubmodule_of _ _
    rw [← hn]
    simpa using hc

end FieldOpFreeAlgebra

end FieldSpecification
