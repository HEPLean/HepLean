/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.Basic
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.Grading
/-!

# Super Commute
-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

namespace CrAnAlgebra

/-!

## The super commutor on the CrAnAlgebra.

-/

open FieldStatistic

/-- The super commutor on the creation and annihlation algebra. For two bosonic operators
  or a bosonic and fermionic operator this corresponds to the usual commutator
  whilst for two fermionic operators this corresponds to the anti-commutator. -/
noncomputable def superCommute : 𝓕.CrAnAlgebra →ₗ[ℂ] 𝓕.CrAnAlgebra →ₗ[ℂ] 𝓕.CrAnAlgebra :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  Basis.constr ofCrAnListBasis ℂ fun φs' =>
  ofCrAnList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList (φs' ++ φs)

/-- The super commutor on the creation and annihlation algebra. For two bosonic operators
  or a bosonic and fermionic operator this corresponds to the usual commutator
  whilst for two fermionic operators this corresponds to the anti-commutator. -/
scoped[FieldSpecification.CrAnAlgebra] notation "[" φs "," φs' "]ₛca" => superCommute φs φs'

/-!

## The super commutor of different types of elements

-/

lemma superCommute_ofCrAnList_ofCrAnList (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnList φs, ofCrAnList φs']ₛca =
    ofCrAnList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList (φs' ++ φs) := by
  rw [← ofListBasis_eq_ofList, ← ofListBasis_eq_ofList]
  simp only [superCommute, Basis.constr_basis]

lemma superCommute_ofCrAnState_ofCrAnState (φ φ' : 𝓕.CrAnStates) :
    [ofCrAnState φ, ofCrAnState φ']ₛca =
    ofCrAnState φ * ofCrAnState φ' - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofCrAnState φ' * ofCrAnState φ := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rw [superCommute_ofCrAnList_ofCrAnList, ofCrAnList_append]
  congr
  rw [ofCrAnList_append]
  rw [FieldStatistic.ofList_singleton, FieldStatistic.ofList_singleton, smul_mul_assoc]

lemma superCommute_ofCrAnList_ofStatesList (φcas : List 𝓕.CrAnStates) (φs : List 𝓕.States) :
    [ofCrAnList φcas, ofStateList φs]ₛca = ofCrAnList φcas * ofStateList φs -
    𝓢(𝓕 |>ₛ φcas, 𝓕 |>ₛ φs) • ofStateList φs * ofCrAnList φcas := by
  conv_lhs => rw [ofStateList_sum]
  rw [map_sum]
  conv_lhs =>
    enter [2, x]
    rw [superCommute_ofCrAnList_ofCrAnList, CrAnSection.statistics_eq_state_statistics,
      ofCrAnList_append, ofCrAnList_append]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.smul_sum,
    ← Finset.sum_mul, ← ofStateList_sum]
  simp

lemma superCommute_ofStateList_ofStatesList (φ : List 𝓕.States) (φs : List 𝓕.States) :
    [ofStateList φ, ofStateList φs]ₛca = ofStateList φ * ofStateList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofStateList φs * ofStateList φ := by
  conv_lhs => rw [ofStateList_sum]
  simp only [map_sum, LinearMap.coeFn_sum, Finset.sum_apply, instCommGroup.eq_1,
    Algebra.smul_mul_assoc]
  conv_lhs =>
    enter [2, x]
    rw [superCommute_ofCrAnList_ofStatesList]
  simp only [instCommGroup.eq_1, CrAnSection.statistics_eq_state_statistics,
    Algebra.smul_mul_assoc, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.smul_sum, ← Finset.mul_sum, ← ofStateList_sum]

lemma superCommute_ofState_ofStatesList (φ : 𝓕.States) (φs : List 𝓕.States) :
    [ofState φ, ofStateList φs]ₛca = ofState φ * ofStateList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofStateList φs * ofState φ := by
  rw [← ofStateList_singleton, superCommute_ofStateList_ofStatesList, ofStateList_singleton]
  simp

lemma superCommute_ofStateList_ofState (φs : List 𝓕.States) (φ : 𝓕.States) :
    [ofStateList φs, ofState φ]ₛca = ofStateList φs * ofState φ -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofState φ * ofStateList φs := by
  rw [← ofStateList_singleton, superCommute_ofStateList_ofStatesList, ofStateList_singleton]
  simp

lemma superCommute_anPart_crPart (φ φ' : 𝓕.States) :
    [anPart φ, crPart φ']ₛca =
    anPart φ * crPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * anPart φ := by
  match φ, φ' with
  | States.inAsymp φ, _ =>
    simp
  | _, States.outAsymp φ =>
    simp only [crPart_posAsymp, map_zero, mul_zero, instCommGroup.eq_1, smul_zero, zero_mul,
      sub_self]
  | States.position φ, States.position φ' =>
    simp only [anPart_position, crPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.outAsymp φ, States.position φ' =>
    simp only [anPart_posAsymp, crPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.position φ, States.inAsymp φ' =>
    simp only [anPart_position, crPart_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp only [List.singleton_append, instCommGroup.eq_1, crAnStatistics,
      FieldStatistic.ofList_singleton, Function.comp_apply, crAnStatesToStates_prod, ←
      ofCrAnList_append]
  | States.outAsymp φ, States.inAsymp φ' =>
    simp only [anPart_posAsymp, crPart_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommute_crPart_anPart (φ φ' : 𝓕.States) :
    [crPart φ, anPart φ']ₛca =
    crPart φ * anPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    anPart φ' * crPart φ := by
    match φ, φ' with
    | States.outAsymp φ, _ =>
    simp only [crPart_posAsymp, map_zero, LinearMap.zero_apply, zero_mul, instCommGroup.eq_1,
      mul_zero, sub_self]
    | _, States.inAsymp φ =>
    simp only [anPart_negAsymp, map_zero, mul_zero, instCommGroup.eq_1, smul_zero, zero_mul,
      sub_self]
    | States.position φ, States.position φ' =>
    simp only [crPart_position, anPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
    | States.position φ, States.outAsymp φ' =>
    simp only [crPart_position, anPart_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
    | States.inAsymp φ, States.position φ' =>
    simp only [crPart_negAsymp, anPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
    | States.inAsymp φ, States.outAsymp φ' =>
    simp only [crPart_negAsymp, anPart_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommute_crPart_crPart (φ φ' : 𝓕.States) :
    [crPart φ, crPart φ']ₛca =
    crPart φ * crPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    crPart φ' * crPart φ := by
  match φ, φ' with
  | States.outAsymp φ, _ =>
  simp only [crPart_posAsymp, map_zero, LinearMap.zero_apply, zero_mul, instCommGroup.eq_1,
    mul_zero, sub_self]
  | _, States.outAsymp φ =>
  simp only [crPart_posAsymp, map_zero, mul_zero, instCommGroup.eq_1, smul_zero, zero_mul, sub_self]
  | States.position φ, States.position φ' =>
  simp only [crPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.position φ, States.inAsymp φ' =>
  simp only [crPart_position, crPart_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.inAsymp φ, States.position φ' =>
  simp only [crPart_negAsymp, crPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]
  | States.inAsymp φ, States.inAsymp φ' =>
  simp only [crPart_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
  simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommute_anPart_anPart (φ φ' : 𝓕.States) :
    [anPart φ, anPart φ']ₛca =
    anPart φ * anPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    anPart φ' * anPart φ := by
  match φ, φ' with
  | States.inAsymp φ, _ =>
    simp
  | _, States.inAsymp φ =>
    simp
  | States.position φ, States.position φ' =>
    simp only [anPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.position φ, States.outAsymp φ' =>
    simp only [anPart_position, anPart_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.outAsymp φ, States.position φ' =>
    simp only [anPart_posAsymp, anPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]
  | States.outAsymp φ, States.outAsymp φ' =>
    simp only [anPart_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
    simp [crAnStatistics, ← ofCrAnList_append]

lemma superCommute_crPart_ofStateList (φ : 𝓕.States) (φs : List 𝓕.States) :
    [crPart φ, ofStateList φs]ₛca =
    crPart φ * ofStateList φs - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofStateList φs *
    crPart φ := by
  match φ with
  | States.inAsymp φ =>
    simp only [crPart_negAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofStatesList]
    simp [crAnStatistics]
  | States.position φ =>
    simp only [crPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofStatesList]
    simp [crAnStatistics]
  | States.outAsymp φ =>
    simp

lemma superCommute_anPart_ofStateList (φ : 𝓕.States) (φs : List 𝓕.States) :
    [anPart φ, ofStateList φs]ₛca =
    anPart φ * ofStateList φs - 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) •
    ofStateList φs * anPart φ := by
  match φ with
  | States.inAsymp φ =>
    simp
  | States.position φ =>
    simp only [anPart_position, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofStatesList]
    simp [crAnStatistics]
  | States.outAsymp φ =>
    simp only [anPart_posAsymp, instCommGroup.eq_1, Algebra.smul_mul_assoc]
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofStatesList]
    simp [crAnStatistics]

lemma superCommute_crPart_ofState (φ φ' : 𝓕.States) :
    [crPart φ, ofState φ']ₛca =
    crPart φ * ofState φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofState φ' * crPart φ := by
  rw [← ofStateList_singleton, superCommute_crPart_ofStateList]
  simp

lemma superCommute_anPart_ofState (φ φ' : 𝓕.States) :
    [anPart φ, ofState φ']ₛca =
    anPart φ * ofState φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofState φ' * anPart φ := by
  rw [← ofStateList_singleton, superCommute_anPart_ofStateList]
  simp

/-!

## Mul equal superCommute

Lemmas which rewrite a multiplication of two elements of the algebra as their commuted
multiplication with a sign plus the super commutor.

-/
lemma ofCrAnList_mul_ofCrAnList_eq_superCommute (φs φs' : List 𝓕.CrAnStates) :
    ofCrAnList φs * ofCrAnList φs' = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnList φs
    + [ofCrAnList φs, ofCrAnList φs']ₛca := by
  rw [superCommute_ofCrAnList_ofCrAnList]
  simp [ofCrAnList_append]

lemma ofCrAnState_mul_ofCrAnList_eq_superCommute (φ : 𝓕.CrAnStates) (φs' : List 𝓕.CrAnStates) :
    ofCrAnState φ * ofCrAnList φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofCrAnList φs' * ofCrAnState φ
    + [ofCrAnState φ, ofCrAnList φs']ₛca := by
  rw [← ofCrAnList_singleton, ofCrAnList_mul_ofCrAnList_eq_superCommute]
  simp

lemma ofStateList_mul_ofStateList_eq_superCommute (φs φs' : List 𝓕.States) :
    ofStateList φs * ofStateList φs' = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofStateList φs' * ofStateList φs
    + [ofStateList φs, ofStateList φs']ₛca := by
  rw [superCommute_ofStateList_ofStatesList]
  simp

lemma ofState_mul_ofStateList_eq_superCommute (φ : 𝓕.States) (φs' : List 𝓕.States) :
    ofState φ * ofStateList φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofStateList φs' * ofState φ
    + [ofState φ, ofStateList φs']ₛca := by
  rw [superCommute_ofState_ofStatesList]
  simp

lemma ofStateList_mul_ofState_eq_superCommute (φs : List 𝓕.States) (φ : 𝓕.States) :
    ofStateList φs * ofState φ = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofState φ * ofStateList φs
    + [ofStateList φs, ofState φ]ₛca := by
  rw [superCommute_ofStateList_ofState]
  simp

lemma crPart_mul_anPart_eq_superCommute (φ φ' : 𝓕.States) :
    crPart φ * anPart φ' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * crPart φ +
    [crPart φ, anPart φ']ₛca := by
  rw [superCommute_crPart_anPart]
  simp

lemma anPart_mul_crPart_eq_superCommute (φ φ' : 𝓕.States) :
    anPart φ * crPart φ' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    crPart φ' * anPart φ +
    [anPart φ, crPart φ']ₛca := by
  rw [superCommute_anPart_crPart]
  simp

lemma crPart_mul_crPart_eq_superCommute (φ φ' : 𝓕.States) :
    crPart φ * crPart φ' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * crPart φ +
    [crPart φ, crPart φ']ₛca := by
  rw [superCommute_crPart_crPart]
  simp

lemma anPart_mul_anPart_eq_superCommute (φ φ' : 𝓕.States) :
    anPart φ * anPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ +
    [anPart φ, anPart φ']ₛca := by
  rw [superCommute_anPart_anPart]
  simp

lemma ofCrAnList_mul_ofStateList_eq_superCommute (φs : List 𝓕.CrAnStates) (φs' : List 𝓕.States) :
    ofCrAnList φs * ofStateList φs' = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofStateList φs' * ofCrAnList φs
    + [ofCrAnList φs, ofStateList φs']ₛca := by
  rw [superCommute_ofCrAnList_ofStatesList]
  simp

/-!

## Symmetry of the super commutor.

-/

lemma superCommute_ofCrAnList_ofCrAnList_symm (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnList φs, ofCrAnList φs']ₛca =
    (- 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs')) • [ofCrAnList φs', ofCrAnList φs]ₛca := by
  rw [superCommute_ofCrAnList_ofCrAnList, superCommute_ofCrAnList_ofCrAnList, smul_sub]
  simp only [instCommGroup.eq_1, neg_smul, sub_neg_eq_add]
  rw [smul_smul]
  conv_rhs =>
    rhs
    rw [exchangeSign_symm, exchangeSign_mul_self]
  simp only [one_smul]
  abel

lemma superCommute_ofCrAnState_ofCrAnState_symm (φ φ' : 𝓕.CrAnStates) :
    [ofCrAnState φ, ofCrAnState φ']ₛca =
    (- 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ')) • [ofCrAnState φ', ofCrAnState φ]ₛca := by
  rw [superCommute_ofCrAnState_ofCrAnState, superCommute_ofCrAnState_ofCrAnState]
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
lemma superCommute_ofCrAnList_ofCrAnList_cons (φ : 𝓕.CrAnStates) (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnList φs, ofCrAnList (φ :: φs')]ₛca =
    [ofCrAnList φs, ofCrAnState φ]ₛca * ofCrAnList φs' +
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ)
    • ofCrAnState φ * [ofCrAnList φs, ofCrAnList φs']ₛca := by
  rw [superCommute_ofCrAnList_ofCrAnList]
  conv_rhs =>
    lhs
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList, sub_mul, ← ofCrAnList_append]
    rhs
    rw [FieldStatistic.ofList_singleton, ofCrAnList_append, ofCrAnList_singleton, smul_mul_assoc,
      mul_assoc, ← ofCrAnList_append]
  conv_rhs =>
    rhs
    rw [superCommute_ofCrAnList_ofCrAnList, mul_sub, smul_mul_assoc]
  simp only [instCommGroup.eq_1, List.cons_append, List.append_assoc, List.nil_append,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, sub_add_sub_cancel, sub_right_inj]
  rw [← ofCrAnList_cons, smul_smul, FieldStatistic.ofList_cons_eq_mul]
  simp only [instCommGroup, map_mul, mul_comm]

lemma superCommute_ofCrAnList_ofStateList_cons (φ : 𝓕.States) (φs : List 𝓕.CrAnStates)
    (φs' : List 𝓕.States) : [ofCrAnList φs, ofStateList (φ :: φs')]ₛca =
    [ofCrAnList φs, ofState φ]ₛca * ofStateList φs' +
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofState φ * [ofCrAnList φs, ofStateList φs']ₛca := by
  rw [superCommute_ofCrAnList_ofStatesList]
  conv_rhs =>
    lhs
    rw [← ofStateList_singleton, superCommute_ofCrAnList_ofStatesList, sub_mul, mul_assoc,
      ← ofStateList_append]
    rhs
    rw [FieldStatistic.ofList_singleton, ofStateList_singleton, smul_mul_assoc,
      smul_mul_assoc, mul_assoc]
  conv_rhs =>
    rhs
    rw [superCommute_ofCrAnList_ofStatesList, mul_sub, smul_mul_assoc]
  simp only [instCommGroup, Algebra.smul_mul_assoc, List.singleton_append, Algebra.mul_smul_comm,
    sub_add_sub_cancel, sub_right_inj]
  rw [ofStateList_cons, mul_assoc, smul_smul, FieldStatistic.ofList_cons_eq_mul]
  simp [mul_comm]

/--
Within the creation and annihilation algebra, we have that
`[φᶜᵃs, φᶜᵃ₀ … φᶜᵃₙ]ₛca = ∑ i, sᵢ • φᶜᵃs₀ … φᶜᵃᵢ₋₁ * [φᶜᵃs, φᶜᵃᵢ]ₛca * φᶜᵃᵢ₊₁ … φᶜᵃₙ`
where `sᵢ` is the exchange sign for `φᶜᵃs` and `φᶜᵃs₀ … φᶜᵃᵢ₋₁`.
-/
lemma superCommute_ofCrAnList_ofCrAnList_eq_sum (φs : List 𝓕.CrAnStates) :
    (φs' : List 𝓕.CrAnStates) → [ofCrAnList φs, ofCrAnList φs']ₛca =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
    ofCrAnList (φs'.take n) * [ofCrAnList φs, ofCrAnState (φs'.get n)]ₛca *
    ofCrAnList (φs'.drop (n + 1))
  | [] => by
    simp [← ofCrAnList_nil, superCommute_ofCrAnList_ofCrAnList]
  | φ :: φs' => by
    rw [superCommute_ofCrAnList_ofCrAnList_cons, superCommute_ofCrAnList_ofCrAnList_eq_sum φs φs']
    conv_rhs => erw [Fin.sum_univ_succ]
    congr 1
    · simp
    · simp [Finset.mul_sum, smul_smul, ofCrAnList_cons, mul_assoc,
        FieldStatistic.ofList_cons_eq_mul, mul_comm]

lemma superCommute_ofCrAnList_ofStateList_eq_sum (φs : List 𝓕.CrAnStates) : (φs' : List 𝓕.States) →
    [ofCrAnList φs, ofStateList φs']ₛca =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
      ofStateList (φs'.take n) * [ofCrAnList φs, ofState (φs'.get n)]ₛca *
      ofStateList (φs'.drop (n + 1))
  | [] => by
    simp only [superCommute_ofCrAnList_ofStatesList, instCommGroup, ofList_empty,
      exchangeSign_bosonic, one_smul, List.length_nil, Finset.univ_eq_empty, List.take_nil,
      List.get_eq_getElem, List.drop_nil, Finset.sum_empty]
    simp
  | φ :: φs' => by
    rw [superCommute_ofCrAnList_ofStateList_cons, superCommute_ofCrAnList_ofStateList_eq_sum φs φs']
    conv_rhs => erw [Fin.sum_univ_succ]
    congr 1
    · simp
    · simp [Finset.mul_sum, smul_smul, ofStateList_cons, mul_assoc,
        FieldStatistic.ofList_cons_eq_mul, mul_comm]
/-!

## Interaction with grading.

-/

lemma superCommute_grade {a b : 𝓕.CrAnAlgebra} {f1 f2 : FieldStatistic}
    (ha : a ∈ statisticSubmodule f1) (hb : b ∈ statisticSubmodule f2) :
    [a, b]ₛca ∈ statisticSubmodule (f1 + f2) := by
  let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule f2) : Prop :=
       [a, a2]ₛca ∈ statisticSubmodule (f1 + f2)
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    simp [p]
    let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule f1) : Prop :=
        [a2 , ofCrAnList φs]ₛca ∈ statisticSubmodule (f1 + f2)
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp [p]
      rw [superCommute_ofCrAnList_ofCrAnList]
      apply Submodule.sub_mem _
      · apply ofCrAnList_mem_statisticSubmodule_of
        rw [ofList_append_eq_mul, hφs, hφs']
      · apply Submodule.smul_mem
        apply ofCrAnList_mem_statisticSubmodule_of
        rw [ofList_append_eq_mul, hφs, hφs']
        rw [mul_comm]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp [p]
      exact Submodule.add_mem _ hp1 hp2
    · intro c x hx hp1
      simp [p]
      exact Submodule.smul_mem _ c hp1
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp [p]
    exact Submodule.add_mem _ hp1 hp2
  · intro c x hx hp1
    simp [p]
    exact Submodule.smul_mem _ c hp1
  · exact hb

lemma superCommute_bosonic_bosonic {a b : 𝓕.CrAnAlgebra}
    (ha : a ∈ statisticSubmodule bosonic) (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
       [a, a2]ₛca = a * a2 - a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
        [a2 , ofCrAnList φs]ₛca = a2 * ofCrAnList φs - ofCrAnList φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp [p]
      rw [superCommute_ofCrAnList_ofCrAnList]
      simp [hφs, ofCrAnList_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all [p, mul_add, add_mul]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all [p, mul_add, add_mul]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb


lemma superCommute_bosonic_fermionic {a b : 𝓕.CrAnAlgebra}
    (ha : a ∈ statisticSubmodule bosonic) (hb : b ∈ statisticSubmodule fermionic) :
    [a, b]ₛca = a * b - b * a := by
  let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
       [a, a2]ₛca = a * a2 - a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
        [a2 , ofCrAnList φs]ₛca = a2 * ofCrAnList φs - ofCrAnList φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp [p]
      rw [superCommute_ofCrAnList_ofCrAnList]
      simp [hφs, hφs', ofCrAnList_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all [p, mul_add, add_mul]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all [p, mul_add, add_mul]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb


lemma superCommute_fermionic_bonsonic {a b : 𝓕.CrAnAlgebra}
    (ha : a ∈ statisticSubmodule fermionic) (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule bosonic) : Prop :=
       [a, a2]ₛca = a * a2 - a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
        [a2 , ofCrAnList φs]ₛca = a2 * ofCrAnList φs - ofCrAnList φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp [p]
      rw [superCommute_ofCrAnList_ofCrAnList]
      simp [hφs, hφs', ofCrAnList_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all [p, mul_add, add_mul]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all [p, mul_add, add_mul]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb

lemma superCommute_bonsonic {a b : 𝓕.CrAnAlgebra}  (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  rw [← bosonicProj_add_fermionicProj a]
  simp only [map_add, LinearMap.add_apply]
  rw [superCommute_bosonic_bosonic (by simp) hb, superCommute_fermionic_bonsonic (by simp) hb]
  simp only [add_mul, mul_add]
  abel

lemma bosonic_superCommute {a b : 𝓕.CrAnAlgebra}  (ha : a ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = a * b - b * a := by
  rw [← bosonicProj_add_fermionicProj b]
  simp only [map_add, LinearMap.add_apply]
  rw [superCommute_bosonic_bosonic ha (by simp), superCommute_bosonic_fermionic ha (by simp)]
  simp only [add_mul, mul_add]
  abel

lemma superCommute_bonsonic_symm {a b : 𝓕.CrAnAlgebra}  (hb : b ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = - [b, a]ₛca := by
  rw [bosonic_superCommute hb, superCommute_bonsonic hb]
  simp

lemma bonsonic_superCommute_symm {a b : 𝓕.CrAnAlgebra}  (ha : a ∈ statisticSubmodule bosonic) :
    [a, b]ₛca = - [b, a]ₛca := by
  rw [bosonic_superCommute ha, superCommute_bonsonic ha]
  simp

lemma superCommute_fermionic_fermionic {a b : 𝓕.CrAnAlgebra}
    (ha : a ∈ statisticSubmodule fermionic) (hb : b ∈ statisticSubmodule fermionic) :
    [a, b]ₛca = a * b + b * a := by
  let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
       [a, a2]ₛca = a * a2 + a2 * a
  change p b hb
  apply Submodule.span_induction (p := p)
  · intro x hx
    obtain ⟨φs, rfl, hφs⟩ := hx
    let p (a2 : 𝓕.CrAnAlgebra) (hx : a2 ∈ statisticSubmodule fermionic) : Prop :=
        [a2 , ofCrAnList φs]ₛca = a2 * ofCrAnList φs + ofCrAnList φs * a2
    change p a ha
    apply Submodule.span_induction (p := p)
    · intro x hx
      obtain ⟨φs', rfl, hφs'⟩ := hx
      simp [p]
      rw [superCommute_ofCrAnList_ofCrAnList]
      simp [hφs, hφs', ofCrAnList_append]
    · simp [p]
    · intro x y hx hy hp1 hp2
      simp_all [p, mul_add, add_mul]
      abel
    · intro c x hx hp1
      simp_all [p, smul_sub]
    · exact ha
  · simp [p]
  · intro x y hx hy hp1 hp2
    simp_all [p, mul_add, add_mul]
    abel
  · intro c x hx hp1
    simp_all [p, smul_sub]
  · exact hb

lemma superCommute_fermionic_fermionic_symm {a b : 𝓕.CrAnAlgebra}
    (ha : a ∈ statisticSubmodule fermionic) (hb : b ∈ statisticSubmodule fermionic) :
    [a, b]ₛca = [b, a]ₛca := by
  rw [superCommute_fermionic_fermionic ha hb]
  rw [superCommute_fermionic_fermionic hb ha]
  abel

lemma superCommute_ofCrAnList_ofCrAnList_bosonic_or_fermionic (φs φs' : List 𝓕.CrAnStates) :
     [ofCrAnList φs, ofCrAnList φs']ₛca ∈ statisticSubmodule bosonic ∨
    [ofCrAnList φs, ofCrAnList φs']ₛca ∈ statisticSubmodule fermionic := by
  by_cases h1 : (𝓕 |>ₛ φs) = bosonic <;> by_cases h2 : (𝓕 |>ₛ φs') = bosonic
  · left
    have h : bosonic = bosonic + bosonic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommute_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ h1
    apply ofCrAnList_mem_statisticSubmodule_of _ _ h2
  · right
    have h : fermionic = bosonic + fermionic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommute_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ h1
    apply ofCrAnList_mem_statisticSubmodule_of _ _ (by simpa using h2)
  · right
    have h : fermionic = fermionic + bosonic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommute_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ (by simpa using h1)
    apply ofCrAnList_mem_statisticSubmodule_of _ _ h2
  · left
    have h : bosonic = fermionic + fermionic := by
      simp only [add_eq_mul, instCommGroup, mul_self]
      rfl
    rw [h]
    apply superCommute_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ (by simpa using h1)
    apply ofCrAnList_mem_statisticSubmodule_of _ _ (by simpa using h2)


lemma superCommute_bosonic_ofCrAnList_eq_sum (a : 𝓕.CrAnAlgebra) (φs : List 𝓕.CrAnStates)
    (ha : a ∈ statisticSubmodule bosonic) :
    [a, ofCrAnList φs]ₛca = ∑ (n : Fin φs.length),
      ofCrAnList (φs.take n) * [a, ofCrAnState (φs.get n)]ₛca *
      ofCrAnList (φs.drop (n + 1)) := by
  let p (a : 𝓕.CrAnAlgebra) (ha : a ∈ statisticSubmodule bosonic) : Prop :=
       [a, ofCrAnList φs]ₛca = ∑ (n : Fin φs.length),
      ofCrAnList (φs.take n) * [a, ofCrAnState (φs.get n)]ₛca *
      ofCrAnList (φs.drop (n + 1))
  change p a ha
  apply Submodule.span_induction (p := p)
  · intro a ha
    obtain ⟨φs, rfl, hφs⟩ := ha
    simp [p]
    rw [superCommute_ofCrAnList_ofCrAnList_eq_sum]
    congr
    funext n
    simp [hφs]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all [p]
    rw [← Finset.sum_add_distrib]
    congr
    funext n
    simp [mul_add, add_mul]
  · intro c x hx hpx
    simp_all [p, Finset.smul_sum]
  · exact ha


lemma superCommute_fermionic_ofCrAnList_eq_sum (a : 𝓕.CrAnAlgebra) (φs : List 𝓕.CrAnStates)
    (ha : a ∈ statisticSubmodule fermionic) :
    [a, ofCrAnList φs]ₛca = ∑ (n : Fin φs.length),  𝓢(fermionic, 𝓕 |>ₛ φs.take n) •
      ofCrAnList (φs.take n) * [a, ofCrAnState (φs.get n)]ₛca *
      ofCrAnList (φs.drop (n + 1)) := by
  let p (a : 𝓕.CrAnAlgebra) (ha : a ∈ statisticSubmodule fermionic) : Prop :=
       [a, ofCrAnList φs]ₛca = ∑ (n : Fin φs.length), 𝓢(fermionic, 𝓕 |>ₛ φs.take n) •
      ofCrAnList (φs.take n) * [a, ofCrAnState (φs.get n)]ₛca *
      ofCrAnList (φs.drop (n + 1))
  change p a ha
  apply Submodule.span_induction (p := p)
  · intro a ha
    obtain ⟨φs, rfl, hφs⟩ := ha
    simp [p]
    rw [superCommute_ofCrAnList_ofCrAnList_eq_sum]
    congr
    funext n
    simp [hφs]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all [p]
    rw [← Finset.sum_add_distrib]
    congr
    funext n
    simp [mul_add, add_mul]
  · intro c x hx hpx
    simp_all [p, Finset.smul_sum]
    congr
    funext x
    simp [smul_smul, mul_comm]
  · exact ha


lemma statistic_neq_of_superCommute_fermionic {φs φs' : List 𝓕.CrAnStates}
    (h : [ofCrAnList φs, ofCrAnList φs']ₛca ∈ statisticSubmodule fermionic) :
    (𝓕 |>ₛ φs) ≠ (𝓕 |>ₛ φs') ∨ [ofCrAnList φs, ofCrAnList φs']ₛca = 0 := by
  by_cases h0 : [ofCrAnList φs, ofCrAnList φs']ₛca = 0
  · simp [h0]
  simp [h0]
  by_contra hn
  refine h0 (eq_zero_of_bosonic_and_fermionic ?_ h)
  by_cases hc : (𝓕 |>ₛ φs) = bosonic
  · have h1 : bosonic = bosonic + bosonic := by
      simp
      rfl
    rw [h1]
    apply superCommute_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _ hc
    apply ofCrAnList_mem_statisticSubmodule_of _ _
    rw [← hn, hc]
  · have h1 : bosonic = fermionic + fermionic := by
      simp
      rfl
    rw [h1]
    apply superCommute_grade
    apply ofCrAnList_mem_statisticSubmodule_of _ _
    simpa using hc
    apply ofCrAnList_mem_statisticSubmodule_of _ _
    rw [← hn]
    simpa using hc

end CrAnAlgebra

end FieldSpecification
