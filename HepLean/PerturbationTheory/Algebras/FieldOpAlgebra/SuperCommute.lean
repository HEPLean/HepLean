/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.TimeOrder
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.Basic
/-!

# SuperCommute on Field operator algebra

-/

namespace FieldSpecification
open CrAnAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

lemma ι_superCommuteF_eq_zero_of_ι_right_zero (a b : 𝓕.CrAnAlgebra) (h : ι b = 0) :
    ι [a, b]ₛca = 0 := by
  rw [superCommuteF_expand_bosonicProj_fermionicProj]
  rw [ι_eq_zero_iff_ι_bosonicProj_fermonicProj_zero] at h
  simp_all

lemma ι_superCommuteF_eq_zero_of_ι_left_zero (a b : 𝓕.CrAnAlgebra) (h : ι a = 0) :
    ι [a, b]ₛca = 0 := by
  rw [superCommuteF_expand_bosonicProj_fermionicProj]
  rw [ι_eq_zero_iff_ι_bosonicProj_fermonicProj_zero] at h
  simp_all

/-!

## Defining normal order for `FiedOpAlgebra`.

-/

lemma ι_superCommuteF_right_zero_of_mem_ideal (a b : 𝓕.CrAnAlgebra)
    (h : b ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) : ι [a, b]ₛca = 0 := by
  apply ι_superCommuteF_eq_zero_of_ι_right_zero
  exact (ι_eq_zero_iff_mem_ideal b).mpr h

lemma ι_superCommuteF_eq_of_equiv_right (a b1 b2 : 𝓕.CrAnAlgebra) (h : b1 ≈ b2) :
    ι [a, b1]ₛca = ι [a, b2]ₛca := by
  rw [equiv_iff_sub_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker, ← map_sub]
  exact ι_superCommuteF_right_zero_of_mem_ideal a (b1 - b2) h

/-- The super commutor on the `FieldOpAlgebra` defined as a linear map `[a,_]ₛ`. -/
noncomputable def superCommuteRight (a : 𝓕.CrAnAlgebra) :
  FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := Quotient.lift (ι.toLinearMap ∘ₗ superCommuteF a)
    (ι_superCommuteF_eq_of_equiv_right a)
  map_add' x y := by
    obtain ⟨x, hx⟩ := ι_surjective x
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hx hy
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hy
    rw [← map_smul, ι_apply, ι_apply]
    simp

lemma superCommuteRight_apply_ι (a b : 𝓕.CrAnAlgebra) :
    superCommuteRight a (ι b) = ι [a, b]ₛca := by rfl

lemma superCommuteRight_apply_quot (a b : 𝓕.CrAnAlgebra) :
    superCommuteRight a ⟦b⟧= ι [a, b]ₛca := by rfl

lemma superCommuteRight_eq_of_equiv (a1 a2 : 𝓕.CrAnAlgebra) (h : a1 ≈ a2) :
    superCommuteRight a1 = superCommuteRight a2 := by
  rw [equiv_iff_sub_mem_ideal] at h
  ext b
  obtain ⟨b, rfl⟩ := ι_surjective b
  have ha1b1 : (superCommuteRight (a1 - a2)) (ι b) = 0 := by
    rw [superCommuteRight_apply_ι]
    apply ι_superCommuteF_eq_zero_of_ι_left_zero
    exact (ι_eq_zero_iff_mem_ideal (a1 - a2)).mpr h
  simp_all only [superCommuteRight_apply_ι, map_sub, LinearMap.sub_apply]
  trans ι ((superCommuteF a2) b) + 0
  rw [← ha1b1]
  simp only [add_sub_cancel]
  simp

/-- The super commutor on the `FieldOpAlgebra`. -/
noncomputable def superCommute : FieldOpAlgebra 𝓕 →ₗ[ℂ]
    FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := Quotient.lift superCommuteRight superCommuteRight_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, rfl⟩ := ι_surjective x
    obtain ⟨y, rfl⟩ := ι_surjective y
    ext b
    obtain ⟨b, rfl⟩ := ι_surjective b
    rw [← map_add, ι_apply, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp only [LinearMap.add_apply]
    rw [superCommuteRight_apply_quot, superCommuteRight_apply_quot, superCommuteRight_apply_quot]
    simp
  map_smul' c y := by
    obtain ⟨y, rfl⟩ := ι_surjective y
    ext b
    obtain ⟨b, rfl⟩ := ι_surjective b
    rw [← map_smul, ι_apply, ι_apply, ι_apply]
    simp only [Quotient.lift_mk, RingHom.id_apply, LinearMap.smul_apply]
    rw [superCommuteRight_apply_quot, superCommuteRight_apply_quot]
    simp

@[inherit_doc superCommute]
scoped[FieldSpecification.FieldOpAlgebra] notation "[" a "," b "]ₛ" => superCommute a b

lemma superCommute_eq_ι_superCommuteF (a b : 𝓕.CrAnAlgebra) :
    [ι a, ι b]ₛ = ι [a, b]ₛca := rfl

/-!

## Properties of `superCommute`.

-/

/-!

## Properties from the definition of FieldOpAlgebra

-/


lemma superCommute_create_create {φ φ' : 𝓕.CrAnStates}
    (h : 𝓕 |>ᶜ φ = .create) (h' : 𝓕 |>ᶜ φ' = .create) :
    [ofCrAnFieldOp φ, ofCrAnFieldOp φ']ₛ = 0 := by
  rw [ofCrAnFieldOp, ofCrAnFieldOp]
  rw [superCommute_eq_ι_superCommuteF, ι_superCommuteF_of_create_create _ _ h h']

lemma superCommute_annihilate_annihilate {φ φ' : 𝓕.CrAnStates}
    (h : 𝓕 |>ᶜ φ = .annihilate) (h' : 𝓕 |>ᶜ φ' = .annihilate) :
    [ofCrAnFieldOp φ, ofCrAnFieldOp φ']ₛ = 0 := by
  rw [ofCrAnFieldOp, ofCrAnFieldOp]
  rw [superCommute_eq_ι_superCommuteF, ι_superCommuteF_of_annihilate_annihilate _ _ h h']

lemma superCommute_diff_statistic {φ φ' : 𝓕.CrAnStates} (h : (𝓕 |>ₛ φ) ≠ 𝓕 |>ₛ φ') :
    [ofCrAnFieldOp φ, ofCrAnFieldOp φ']ₛ = 0 := by
  rw [ofCrAnFieldOp, ofCrAnFieldOp]
  rw [superCommute_eq_ι_superCommuteF, ι_superCommuteF_of_diff_statistic h]

lemma superCommute_ofCrAnFieldOp_ofCrAnFieldOp_mem_center (φ φ' : 𝓕.CrAnStates) :
    [ofCrAnFieldOp φ, ofCrAnFieldOp φ']ₛ ∈ Subalgebra.center ℂ (FieldOpAlgebra 𝓕) := by
  rw [ofCrAnFieldOp, ofCrAnFieldOp, superCommute_eq_ι_superCommuteF]
  exact ι_superCommuteF_ofCrAnState_ofCrAnState_mem_center φ φ'

/-!

### `superCommute` on different constructors.

-/

lemma superCommute_ofCrAnFieldOpList_ofCrAnFieldOpList (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnFieldOpList φs, ofCrAnFieldOpList φs']ₛ =
    ofCrAnFieldOpList (φs ++ φs') - 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnFieldOpList (φs' ++ φs) := by
  rw [ofCrAnFieldOpList_eq_ι_ofCrAnList, ofCrAnFieldOpList_eq_ι_ofCrAnList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofCrAnList_ofCrAnList]
  rfl

lemma superCommute_ofCrAnFieldOp_ofCrAnFieldOp (φ φ' : 𝓕.CrAnStates) :
    [ofCrAnFieldOp φ, ofCrAnFieldOp φ']ₛ = ofCrAnFieldOp φ * ofCrAnFieldOp φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofCrAnFieldOp φ' * ofCrAnFieldOp φ := by
  rw [ofCrAnFieldOp, ofCrAnFieldOp]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofCrAnState_ofCrAnState]
  rfl

lemma superCommute_ofCrAnFieldOpList_ofFieldOpList (φcas : List 𝓕.CrAnStates)
    (φs : List 𝓕.States) :
    [ofCrAnFieldOpList φcas, ofFieldOpList φs]ₛ = ofCrAnFieldOpList φcas * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φcas, 𝓕 |>ₛ φs) • ofFieldOpList φs * ofCrAnFieldOpList φcas := by
  rw [ofCrAnFieldOpList, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofCrAnList_ofStatesList]
  rfl

lemma superCommute_ofFieldOpList_ofFieldOpList (φs φs' : List 𝓕.States) :
    [ofFieldOpList φs, ofFieldOpList φs']ₛ = ofFieldOpList φs * ofFieldOpList φs' -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofFieldOpList φs := by
  rw [ofFieldOpList, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofStateList_ofStatesList]
  rfl

lemma superCommute_ofFieldOp_ofFieldOpList (φ : 𝓕.States) (φs : List 𝓕.States) :
    [ofFieldOp φ, ofFieldOpList φs]ₛ = ofFieldOp φ * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpList φs * ofFieldOp φ := by
  rw [ofFieldOp, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofState_ofStatesList]
  rfl

lemma superCommute_ofFieldOpList_ofFieldOp (φs : List 𝓕.States) (φ : 𝓕.States) :
    [ofFieldOpList φs, ofFieldOp φ]ₛ = ofFieldOpList φs * ofFieldOp φ -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofFieldOp φ * ofFieldOpList φs := by
  rw [ofFieldOpList, ofFieldOp]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_ofStateList_ofState]
  rfl

lemma superCommute_anPart_crPart (φ φ' : 𝓕.States) :
    [anPart φ, crPart φ']ₛ = anPart φ * crPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * anPart φ := by
  rw [anPart, crPart]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_anPartF_crPartF]
  rfl

lemma superCommute_crPart_anPart (φ φ' : 𝓕.States) :
    [crPart φ, anPart φ']ₛ = crPart φ * anPart φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * crPart φ := by
  rw [anPart, crPart]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_crPartF_anPartF]
  rfl

@[simp]
lemma superCommute_crPart_crPart (φ φ' : 𝓕.States) : [crPart φ, crPart φ']ₛ = 0 := by
  match φ, φ' with
  | States.outAsymp φ, _ =>
    simp
  | _, States.outAsymp φ =>
    simp
  | States.position φ, States.position φ' =>
    simp only [crPart_position]
    apply superCommute_create_create
    · rfl
    · rfl
  | States.position φ, States.inAsymp φ' =>
    simp only [crPart_position, crPart_negAsymp]
    apply superCommute_create_create
    · rfl
    · rfl
  | States.inAsymp φ, States.inAsymp φ' =>
    simp only [crPart_negAsymp]
    apply superCommute_create_create
    · rfl
    · rfl
  | States.inAsymp φ, States.position φ' =>
    simp only [crPart_negAsymp, crPart_position]
    apply superCommute_create_create
    · rfl
    · rfl

@[simp]
lemma superCommute_anPart_anPart (φ φ' : 𝓕.States) : [anPart φ, anPart φ']ₛ = 0 := by
  match φ, φ' with
  | States.inAsymp φ, _ =>
    simp
  | _, States.inAsymp φ =>
    simp
  | States.position φ, States.position φ' =>
    simp only [anPart_position]
    apply superCommute_annihilate_annihilate
    · rfl
    · rfl
  | States.position φ, States.outAsymp φ' =>
    simp only [anPart_position, anPart_posAsymp]
    apply superCommute_annihilate_annihilate
    · rfl
    · rfl
  | States.outAsymp φ, States.outAsymp φ' =>
    simp only [anPart_posAsymp]
    apply superCommute_annihilate_annihilate
    · rfl
    · rfl
  | States.outAsymp φ, States.position φ' =>
    simp only [anPart_posAsymp, anPart_position]
    apply superCommute_annihilate_annihilate
    · rfl
    · rfl

lemma superCommute_crPart_ofFieldOpList (φ : 𝓕.States) (φs : List 𝓕.States) :
    [crPart φ, ofFieldOpList φs]ₛ = crPart φ * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpList φs * crPart φ := by
  rw [crPart, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_crPartF_ofStateList]
  rfl

lemma superCommute_anPart_ofFieldOpList (φ : 𝓕.States) (φs : List 𝓕.States) :
    [anPart φ, ofFieldOpList φs]ₛ = anPart φ * ofFieldOpList φs -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs) • ofFieldOpList φs * anPart φ := by
  rw [anPart, ofFieldOpList]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_anPartF_ofStateList]
  rfl

lemma superCommute_crPart_ofFieldOp (φ φ' : 𝓕.States) :
    [crPart φ, ofFieldOp φ']ₛ = crPart φ * ofFieldOp φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOp φ' * crPart φ := by
  rw [crPart, ofFieldOp]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_crPartF_ofState]
  rfl

lemma superCommute_anPart_ofFieldOp (φ φ' : 𝓕.States) :
    [anPart φ, ofFieldOp φ']ₛ = anPart φ * ofFieldOp φ' -
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • ofFieldOp φ' * anPart φ := by
  rw [anPart, ofFieldOp]
  rw [superCommute_eq_ι_superCommuteF, superCommuteF_anPartF_ofState]
  rfl


/-!

## Mul equal superCommute

Lemmas which rewrite a multiplication of two elements of the algebra as their commuted
multiplication with a sign plus the super commutor.

-/

lemma ofCrAnFieldOpList_mul_ofCrAnFieldOpList_eq_superCommute (φs φs' : List 𝓕.CrAnStates) :
    ofCrAnFieldOpList φs * ofCrAnFieldOpList φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofCrAnFieldOpList φs' * ofCrAnFieldOpList φs
    + [ofCrAnFieldOpList φs, ofCrAnFieldOpList φs']ₛ := by
  rw [superCommute_ofCrAnFieldOpList_ofCrAnFieldOpList]
  simp [ofCrAnFieldOpList_append]

lemma ofCrAnFieldOp_mul_ofCrAnFieldOpList_eq_superCommute (φ : 𝓕.CrAnStates)
    (φs' : List 𝓕.CrAnStates) : ofCrAnFieldOp φ * ofCrAnFieldOpList φs' =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofCrAnFieldOpList φs' * ofCrAnFieldOp φ
    + [ofCrAnFieldOp φ, ofCrAnFieldOpList φs']ₛ := by
  rw [← ofCrAnFieldOpList_singleton, ofCrAnFieldOpList_mul_ofCrAnFieldOpList_eq_superCommute]
  simp

lemma ofFieldOpList_mul_ofFieldOpList_eq_superCommute (φs φs' : List 𝓕.States) :
    ofFieldOpList φs * ofFieldOpList φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofFieldOpList φs
    + [ofFieldOpList φs, ofFieldOpList φs']ₛ := by
  rw [superCommute_ofFieldOpList_ofFieldOpList]
  simp

lemma ofFieldOp_mul_ofFieldOpList_eq_superCommute (φ : 𝓕.States) (φs' : List 𝓕.States) :
    ofFieldOp φ * ofFieldOpList φs' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofFieldOp φ
    + [ofFieldOp φ, ofFieldOpList φs']ₛ := by
  rw [superCommute_ofFieldOp_ofFieldOpList]
  simp

lemma ofFieldOpList_mul_ofFieldOp_eq_superCommute (φs : List 𝓕.States) (φ : 𝓕.States) :
    ofFieldOpList φs * ofFieldOp φ = 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φ) • ofFieldOp φ * ofFieldOpList φs
    + [ofFieldOpList φs, ofFieldOp φ]ₛ := by
  rw [superCommute_ofFieldOpList_ofFieldOp]
  simp

lemma ofCrAnFieldOpList_mul_ofFieldOpList_eq_superCommute (φs : List 𝓕.CrAnStates)
    (φs' : List 𝓕.States) : ofCrAnFieldOpList φs * ofFieldOpList φs' =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • ofFieldOpList φs' * ofCrAnFieldOpList φs
    + [ofCrAnFieldOpList φs, ofFieldOpList φs']ₛ := by
  rw [superCommute_ofCrAnFieldOpList_ofFieldOpList]
  simp

lemma crPart_mul_anPart_eq_superCommute (φ φ' : 𝓕.States) :
    crPart φ * anPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * crPart φ
    + [crPart φ, anPart φ']ₛ := by
  rw [superCommute_crPart_anPart]
  simp

lemma anPart_mul_crPart_eq_superCommute (φ φ' : 𝓕.States) :
    anPart φ * crPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * anPart φ
    + [anPart φ, crPart φ']ₛ := by
  rw [superCommute_anPart_crPart]
  simp

lemma crPart_mul_crPart_swap (φ φ' : 𝓕.States) :
    crPart φ * crPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * crPart φ := by
  trans 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • crPart φ' * crPart φ + [crPart φ, crPart φ']ₛ
  · rw [crPart, crPart, superCommute_eq_ι_superCommuteF, superCommuteF_crPartF_crPartF]
    simp
  · simp

lemma anPart_mul_anPart_swap (φ φ' : 𝓕.States) :
    anPart φ * anPart φ' = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ := by
  trans 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • anPart φ' * anPart φ + [anPart φ, anPart φ']ₛ
  · rw [anPart, anPart, superCommute_eq_ι_superCommuteF, superCommuteF_anPartF_anPartF]
    simp
  · simp

/-!

## Symmetry of the super commutor.

-/

lemma superCommute_ofCrAnFieldOpList_ofCrAnFieldOpList_symm (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnFieldOpList φs, ofCrAnFieldOpList φs']ₛ =
    (- 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs')) • [ofCrAnFieldOpList φs', ofCrAnFieldOpList φs]ₛ := by
  rw [ofCrAnFieldOpList, ofCrAnFieldOpList, superCommute_eq_ι_superCommuteF,
   superCommuteF_ofCrAnList_ofCrAnList_symm]
  rfl

lemma superCommute_ofCrAnFieldOp_ofCrAnFieldOp_symm (φ φ' : 𝓕.CrAnStates) :
    [ofCrAnFieldOp φ, ofCrAnFieldOp φ']ₛ =
    (- 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ')) • [ofCrAnFieldOp φ', ofCrAnFieldOp φ]ₛ := by
  rw [ofCrAnFieldOp, ofCrAnFieldOp, superCommute_eq_ι_superCommuteF,
    superCommuteF_ofCrAnState_ofCrAnState_symm]
  rfl

/-!

## splitting the super commute into sums

-/

lemma superCommute_ofCrAnFieldOpList_ofCrAnFieldOpList_eq_sum (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnFieldOpList φs, ofCrAnFieldOpList φs']ₛ =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
    ofCrAnFieldOpList (φs'.take n) * [ofCrAnFieldOpList φs, ofCrAnFieldOp (φs'.get n)]ₛ *
    ofCrAnFieldOpList (φs'.drop (n + 1)) := by
  conv_lhs =>
    rw [ofCrAnFieldOpList, ofCrAnFieldOpList, superCommute_eq_ι_superCommuteF,
      superCommuteF_ofCrAnList_ofCrAnList_eq_sum]
  rw [map_sum]
  rfl

lemma superCommute_ofCrAnFieldOpList_ofFieldOpList_eq_sum (φs : List 𝓕.CrAnStates)
    (φs' : List 𝓕.States) : [ofCrAnFieldOpList φs, ofFieldOpList φs']ₛ =
    ∑ (n : Fin φs'.length), 𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs'.take n) •
    ofFieldOpList (φs'.take n) * [ofCrAnFieldOpList φs, ofFieldOp (φs'.get n)]ₛ *
    ofFieldOpList (φs'.drop (n + 1)) := by
  conv_lhs =>
    rw [ofCrAnFieldOpList, ofFieldOpList, superCommute_eq_ι_superCommuteF,
      superCommuteF_ofCrAnList_ofStateList_eq_sum]
  rw [map_sum]
  rfl


end FieldOpAlgebra
end FieldSpecification
