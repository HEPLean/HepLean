/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.NormalOrder
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.SuperCommute
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Normal Ordering in the CrAnAlgebra

In the module
`HepLean.PerturbationTheory.FieldSpecification.NormalOrder`
we defined the normal ordering of a list of `CrAnStates`.
In this module we extend the normal ordering to a linear map on `CrAnAlgebra`.

We derive properties of this normal ordering.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace CrAnAlgebra

noncomputable section

/-- The linear map on the free creation and annihlation
  algebra defined as the map taking
  a list of CrAnStates to the normal-ordered list of states multiplied by
  the sign corresponding to the number of fermionic-fermionic
  exchanges done in ordering. -/
def normalOrderF : CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕 :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  normalOrderSign φs • ofCrAnList (normalOrderList φs)

@[inherit_doc normalOrderF]
scoped[FieldSpecification.CrAnAlgebra] notation "𝓝ᶠ(" a ")" => normalOrderF a

lemma normalOrderF_ofCrAnList (φs : List 𝓕.CrAnStates) :
    𝓝ᶠ(ofCrAnList φs) = normalOrderSign φs • ofCrAnList (normalOrderList φs) := by
  rw [← ofListBasis_eq_ofList, normalOrderF, Basis.constr_basis]

lemma ofCrAnList_eq_normalOrderF (φs : List 𝓕.CrAnStates) :
    ofCrAnList (normalOrderList φs) = normalOrderSign φs • 𝓝ᶠ(ofCrAnList φs) := by
  rw [normalOrderF_ofCrAnList, normalOrderList, smul_smul, normalOrderSign, Wick.koszulSign_mul_self,
    one_smul]

lemma normalOrderF_one : normalOrderF (𝓕 := 𝓕) 1 = 1 := by
  rw [← ofCrAnList_nil, normalOrderF_ofCrAnList, normalOrderSign_nil, normalOrderList_nil,
    ofCrAnList_nil, one_smul]

/-!

## Normal ordering with a creation operator on the left or annihilation on the right

-/

lemma normalOrderF_ofCrAnList_cons_create (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnStates) :
    𝓝ᶠ(ofCrAnList (φ :: φs)) = ofCrAnState φ * 𝓝ᶠ(ofCrAnList φs) := by
  rw [normalOrderF_ofCrAnList, normalOrderSign_cons_create φ hφ, normalOrderList_cons_create φ hφ φs]
  rw [ofCrAnList_cons, normalOrderF_ofCrAnList, mul_smul_comm]

lemma normalOrderF_create_mul (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (a : CrAnAlgebra 𝓕) :
    𝓝ᶠ(ofCrAnState φ * a) = ofCrAnState φ * 𝓝ᶠ(a) := by
  change (normalOrderF ∘ₗ mulLinearMap (ofCrAnState φ)) a =
    (mulLinearMap (ofCrAnState φ) ∘ₗ normalOrderF) a
  refine LinearMap.congr_fun (ofCrAnListBasis.ext fun l ↦ ?_) a
  simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
    LinearMap.coe_comp, Function.comp_apply]
  rw [← ofCrAnList_cons, normalOrderF_ofCrAnList_cons_create φ hφ]

lemma normalOrderF_ofCrAnList_append_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnStates) :
    𝓝ᶠ(ofCrAnList (φs ++ [φ])) = 𝓝ᶠ(ofCrAnList φs) * ofCrAnState φ := by
  rw [normalOrderF_ofCrAnList, normalOrderSign_append_annihlate φ hφ φs,
    normalOrderList_append_annihilate φ hφ φs, ofCrAnList_append, ofCrAnList_singleton,
      normalOrderF_ofCrAnList, smul_mul_assoc]

lemma normalOrderF_mul_annihilate (φ : 𝓕.CrAnStates)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate)
    (a : CrAnAlgebra 𝓕) : 𝓝ᶠ(a * ofCrAnState φ) = 𝓝ᶠ(a) * ofCrAnState φ := by
  change (normalOrderF ∘ₗ mulLinearMap.flip (ofCrAnState φ)) a =
    (mulLinearMap.flip (ofCrAnState φ) ∘ₗ normalOrderF) a
  refine LinearMap.congr_fun (ofCrAnListBasis.ext fun l ↦ ?_) a
  simp only [mulLinearMap, ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← ofCrAnList_singleton, ← ofCrAnList_append, ofCrAnList_singleton,
    normalOrderF_ofCrAnList_append_annihilate φ hφ]

lemma normalOrderF_crPart_mul (φ : 𝓕.States) (a : CrAnAlgebra 𝓕) :
    𝓝ᶠ(crPart φ * a) =
    crPart φ * 𝓝ᶠ(a) := by
  match φ with
  | .inAsymp φ =>
    rw [crPart]
    exact normalOrderF_create_mul ⟨States.inAsymp φ, ()⟩ rfl a
  | .position φ =>
    rw [crPart]
    exact normalOrderF_create_mul _ rfl _
  | .outAsymp φ => simp

lemma normalOrderF_mul_anPart (φ : 𝓕.States) (a : CrAnAlgebra 𝓕) :
    𝓝ᶠ(a * anPart φ) =
    𝓝ᶠ(a) * anPart φ := by
  match φ with
  | .inAsymp φ => simp
  | .position φ =>
    rw [anPart]
    exact normalOrderF_mul_annihilate _ rfl _
  | .outAsymp φ =>
    rw [anPart]
    refine normalOrderF_mul_annihilate _ rfl _

/-!

## Normal ordering for an adjacent creation and annihliation state

The main result of this section is `normalOrderF_superCommuteF_annihilate_create`.
-/

lemma normalOrderF_swap_create_annihlate_ofCrAnList_ofCrAnList (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (φs φs' : List 𝓕.CrAnStates) :
    𝓝ᶠ(ofCrAnList φs' * ofCrAnState φc * ofCrAnState φa * ofCrAnList φs) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) •
    𝓝ᶠ(ofCrAnList φs' * ofCrAnState φa * ofCrAnState φc * ofCrAnList φs) := by
  rw [mul_assoc, mul_assoc, ← ofCrAnList_cons, ← ofCrAnList_cons, ← ofCrAnList_append]
  rw [normalOrderF_ofCrAnList, normalOrderSign_swap_create_annihlate φc φa hφc hφa]
  rw [normalOrderList_swap_create_annihlate φc φa hφc hφa, ← smul_smul, ← normalOrderF_ofCrAnList]
  rw [ofCrAnList_append, ofCrAnList_cons, ofCrAnList_cons]
  noncomm_ring

lemma normalOrderF_swap_create_annihlate_ofCrAnList (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnStates) (a : 𝓕.CrAnAlgebra) :
    𝓝ᶠ(ofCrAnList φs * ofCrAnState φc * ofCrAnState φa * a) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) •
    𝓝ᶠ(ofCrAnList φs * ofCrAnState φa * ofCrAnState φc * a) := by
  change (normalOrderF ∘ₗ mulLinearMap (ofCrAnList φs * ofCrAnState φc * ofCrAnState φa)) a =
    (smulLinearMap _ ∘ₗ normalOrderF ∘ₗ
    mulLinearMap (ofCrAnList φs * ofCrAnState φa * ofCrAnState φc)) a
  refine LinearMap.congr_fun (ofCrAnListBasis.ext fun l ↦ ?_) a
  simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
    LinearMap.coe_comp, Function.comp_apply, instCommGroup.eq_1]
  rw [normalOrderF_swap_create_annihlate_ofCrAnList_ofCrAnList φc φa hφc hφa]
  rfl

lemma normalOrderF_swap_create_annihlate (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.CrAnAlgebra) :
    𝓝ᶠ(a * ofCrAnState φc * ofCrAnState φa * b) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) •
    𝓝ᶠ(a * ofCrAnState φa * ofCrAnState φc * b) := by
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  change (normalOrderF ∘ₗ mulLinearMap.flip (ofCrAnState φc * (ofCrAnState φa * b))) a =
    (smulLinearMap (𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa)) ∘ₗ
    normalOrderF ∘ₗ mulLinearMap.flip (ofCrAnState φa * (ofCrAnState φc * b))) a
  refine LinearMap.congr_fun (ofCrAnListBasis.ext fun l ↦ ?_) _
  simp only [mulLinearMap, ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk, instCommGroup.eq_1, ← mul_assoc,
      normalOrderF_swap_create_annihlate_ofCrAnList φc φa hφc hφa]
  rfl

lemma normalOrderF_superCommuteF_create_annihilate (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.CrAnAlgebra) :
    𝓝ᶠ(a * [ofCrAnState φc, ofCrAnState φa]ₛca * b) = 0 := by
  simp only [superCommuteF_ofCrAnState_ofCrAnState, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [mul_sub, sub_mul, map_sub, ← smul_mul_assoc, ← mul_assoc, ← mul_assoc,
    normalOrderF_swap_create_annihlate φc φa hφc hφa]
  simp

lemma normalOrderF_superCommuteF_annihilate_create (φc φa : 𝓕.CrAnStates)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.CrAnAlgebra) :
    𝓝ᶠ(a * [ofCrAnState φa, ofCrAnState φc]ₛca * b) = 0 := by
  rw [superCommuteF_ofCrAnState_ofCrAnState_symm]
  simp only [instCommGroup.eq_1, neg_smul, mul_neg, Algebra.mul_smul_comm, neg_mul,
    Algebra.smul_mul_assoc, map_neg, map_smul, neg_eq_zero, smul_eq_zero]
  exact Or.inr (normalOrderF_superCommuteF_create_annihilate φc φa hφc hφa ..)

lemma normalOrderF_swap_crPart_anPart (φ φ' : 𝓕.States) (a b : CrAnAlgebra 𝓕) :
    𝓝ᶠ(a * (crPart φ) * (anPart φ') * b) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓝ᶠ(a * (anPart φ') * (crPart φ) * b) := by
  match φ, φ' with
  | _, .inAsymp φ' => simp
  | .outAsymp φ, _ => simp
  | .position φ, .position φ' =>
    simp only [crPart_position, anPart_position, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihlate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnStatesToStates_prod]
    rfl; rfl
  | .inAsymp φ, .outAsymp φ' =>
    simp only [crPart_negAsymp, anPart_posAsymp, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihlate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnStatesToStates_prod]
    rfl; rfl
  | .inAsymp φ, .position φ' =>
    simp only [crPart_negAsymp, anPart_position, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihlate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnStatesToStates_prod]
    rfl; rfl
  | .position φ, .outAsymp φ' =>
    simp only [crPart_position, anPart_posAsymp, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihlate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnStatesToStates_prod]
    rfl; rfl

/-!

## Normal ordering for an anPart and crPart

Using the results from above.

-/

lemma normalOrderF_swap_anPart_crPart (φ φ' : 𝓕.States) (a b : CrAnAlgebra 𝓕) :
    𝓝ᶠ(a * (anPart φ) * (crPart φ') * b) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓝ᶠ(a * (crPart φ') *
      (anPart φ) * b) := by
  simp [normalOrderF_swap_crPart_anPart, smul_smul]

lemma normalOrderF_superCommuteF_crPart_anPart (φ φ' : 𝓕.States) (a b : CrAnAlgebra 𝓕) :
    𝓝ᶠ(a * superCommuteF
      (crPart φ) (anPart φ') * b) = 0 := by
  match φ, φ' with
  | _, .inAsymp φ' => simp
  | .outAsymp φ', _ => simp
  | .position φ, .position φ' =>
    rw [crPart_position, anPart_position]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..
  | .inAsymp φ, .outAsymp φ' =>
    rw [crPart_negAsymp, anPart_posAsymp]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..
  | .inAsymp φ, .position φ' =>
    rw [crPart_negAsymp, anPart_position]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..
  | .position φ, .outAsymp φ' =>
    rw [crPart_position, anPart_posAsymp]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..

lemma normalOrderF_superCommuteF_anPart_crPart (φ φ' : 𝓕.States) (a b : CrAnAlgebra 𝓕) :
    𝓝ᶠ(a * superCommuteF
    (anPart φ) (crPart φ') * b) = 0 := by
  match φ, φ' with
  | .inAsymp φ', _ => simp
  | _, .outAsymp φ' => simp
  | .position φ, .position φ' =>
    rw [anPart_position, crPart_position]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..
  | .outAsymp φ', .inAsymp φ =>
    simp only [anPart_posAsymp, crPart_negAsymp]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..
  | .position φ', .inAsymp φ =>
    simp only [anPart_position, crPart_negAsymp]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..
  | .outAsymp φ, .position φ' =>
    simp only [anPart_posAsymp, crPart_position]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..

/-!

## The normal ordering of a product of two states

-/

@[simp]
lemma normalOrderF_crPart_mul_crPart (φ φ' : 𝓕.States) :
    𝓝ᶠ(crPart φ * crPart φ') =
    crPart φ * crPart φ' := by
  rw [normalOrderF_crPart_mul]
  conv_lhs => rw [← mul_one (crPart φ')]
  rw [normalOrderF_crPart_mul, normalOrderF_one]
  simp

@[simp]
lemma normalOrderF_anPart_mul_anPart (φ φ' : 𝓕.States) :
    𝓝ᶠ(anPart φ * anPart φ') =
    anPart φ * anPart φ' := by
  rw [normalOrderF_mul_anPart]
  conv_lhs => rw [← one_mul (anPart φ)]
  rw [normalOrderF_mul_anPart, normalOrderF_one]
  simp

@[simp]
lemma normalOrderF_crPart_mul_anPart (φ φ' : 𝓕.States) :
    𝓝ᶠ(crPart φ * anPart φ') =
    crPart φ * anPart φ' := by
  rw [normalOrderF_crPart_mul]
  conv_lhs => rw [← one_mul (anPart φ')]
  rw [normalOrderF_mul_anPart, normalOrderF_one]
  simp

@[simp]
lemma normalOrderF_anPart_mul_crPart (φ φ' : 𝓕.States) :
    𝓝ᶠ(anPart φ * crPart φ') =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    (crPart φ' * anPart φ) := by
  conv_lhs => rw [← one_mul (anPart φ * crPart φ')]
  conv_lhs => rw [← mul_one (1 * (anPart φ *
    crPart φ'))]
  rw [← mul_assoc, normalOrderF_swap_anPart_crPart]
  simp

lemma normalOrderF_ofState_mul_ofState (φ φ' : 𝓕.States) :
    𝓝ᶠ(ofState φ * ofState φ') =
    crPart φ * crPart φ' +
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    (crPart φ' * anPart φ) +
    crPart φ * anPart φ' +
    anPart φ * anPart φ' := by
  rw [ofState_eq_crPart_add_anPart, ofState_eq_crPart_add_anPart, mul_add, add_mul, add_mul]
  simp only [map_add, normalOrderF_crPart_mul_crPart, normalOrderF_anPart_mul_crPart,
    instCommGroup.eq_1, normalOrderF_crPart_mul_anPart, normalOrderF_anPart_mul_anPart]
  abel

/-!

## Normal order with super commutors

-/

TODO "Split the following two lemmas up into smaller parts."

lemma normalOrderF_superCommuteF_ofCrAnList_create_create_ofCrAnList
    (φc φc' : 𝓕.CrAnStates) (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create)
    (hφc' : 𝓕 |>ᶜ φc' = CreateAnnihilate.create) (φs φs' : List 𝓕.CrAnStates) :
    (𝓝ᶠ(ofCrAnList φs * [ofCrAnState φc, ofCrAnState φc']ₛca * ofCrAnList φs')) =
      normalOrderSign (φs ++ φc' :: φc :: φs') •
    (ofCrAnList (createFilter φs) * [ofCrAnState φc, ofCrAnState φc']ₛca *
      ofCrAnList (createFilter φs') * ofCrAnList (annihilateFilter (φs ++ φs'))) := by
  rw [superCommuteF_ofCrAnState_ofCrAnState, mul_sub, sub_mul, map_sub]
  conv_lhs =>
    lhs; rhs
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_append, ← ofCrAnList_append,
      ← ofCrAnList_append]
  conv_lhs =>
    lhs
    rw [normalOrderF_ofCrAnList, normalOrderList_eq_createFilter_append_annihilateFilter]
    rw [createFilter_append, createFilter_append, createFilter_append,
      createFilter_singleton_create _ hφc, createFilter_singleton_create _ hφc']
    rw [annihilateFilter_append, annihilateFilter_append, annihilateFilter_append,
      annihilateFilter_singleton_create _ hφc, annihilateFilter_singleton_create _ hφc']
    enter [2, 1, 2]
    simp only [List.singleton_append, List.append_assoc, List.cons_append, List.append_nil,
      instCommGroup.eq_1, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smul]
    rw [← annihilateFilter_append]
  conv_lhs =>
    rhs; rhs
    rw [smul_mul_assoc, Algebra.mul_smul_comm, smul_mul_assoc]
    rhs
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_append, ← ofCrAnList_append,
      ← ofCrAnList_append]
  conv_lhs =>
    rhs
    rw [map_smul]
    rhs
    rw [normalOrderF_ofCrAnList, normalOrderList_eq_createFilter_append_annihilateFilter]
    rw [createFilter_append, createFilter_append, createFilter_append,
      createFilter_singleton_create _ hφc, createFilter_singleton_create _ hφc']
    rw [annihilateFilter_append, annihilateFilter_append, annihilateFilter_append,
      annihilateFilter_singleton_create _ hφc, annihilateFilter_singleton_create _ hφc']
    enter [2, 1, 2]
    simp only [List.singleton_append, List.append_assoc, List.cons_append, instCommGroup.eq_1,
      List.append_nil, Algebra.smul_mul_assoc]
    rw [← annihilateFilter_append]
  conv_lhs =>
    lhs; lhs
    simp
  conv_lhs =>
    rhs; rhs; lhs
    simp
  rw [normalOrderSign_swap_create_create φc φc' hφc hφc']
  rw [smul_smul, mul_comm, ← smul_smul]
  rw [← smul_sub, ofCrAnList_append, ofCrAnList_append, ofCrAnList_append]
  conv_lhs =>
    rhs; rhs
    rw [ofCrAnList_append, ofCrAnList_append, ofCrAnList_append]
    rw [← smul_mul_assoc, ← smul_mul_assoc, ← Algebra.mul_smul_comm]
  rw [← sub_mul, ← sub_mul, ← mul_sub, ofCrAnList_append, ofCrAnList_singleton,
    ofCrAnList_singleton]
  rw [ofCrAnList_append, ofCrAnList_singleton, ofCrAnList_singleton, smul_mul_assoc]

lemma normalOrderF_superCommuteF_ofCrAnList_annihilate_annihilate_ofCrAnList
    (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕 |>ᶜ φa' = CreateAnnihilate.annihilate)
    (φs φs' : List 𝓕.CrAnStates) :
    𝓝ᶠ(ofCrAnList φs * [ofCrAnState φa, ofCrAnState φa']ₛca * ofCrAnList φs') =
      normalOrderSign (φs ++ φa' :: φa :: φs') •
    (ofCrAnList (createFilter (φs ++ φs'))
      * ofCrAnList (annihilateFilter φs) * [ofCrAnState φa, ofCrAnState φa']ₛca
      * ofCrAnList (annihilateFilter φs')) := by
  rw [superCommuteF_ofCrAnState_ofCrAnState, mul_sub, sub_mul, map_sub]
  conv_lhs =>
    lhs; rhs
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_append, ← ofCrAnList_append,
      ← ofCrAnList_append]
  conv_lhs =>
    lhs
    rw [normalOrderF_ofCrAnList, normalOrderList_eq_createFilter_append_annihilateFilter]
    rw [createFilter_append, createFilter_append, createFilter_append,
      createFilter_singleton_annihilate _ hφa, createFilter_singleton_annihilate _ hφa']
    rw [annihilateFilter_append, annihilateFilter_append, annihilateFilter_append,
      annihilateFilter_singleton_annihilate _ hφa, annihilateFilter_singleton_annihilate _ hφa']
    enter [2, 1, 1]
    simp only [List.singleton_append, List.append_assoc, List.cons_append, List.append_nil,
      instCommGroup.eq_1, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, map_smul]
    rw [← createFilter_append]
  conv_lhs =>
    rhs; rhs
    rw [smul_mul_assoc]
    rw [Algebra.mul_smul_comm, smul_mul_assoc]
    rhs
    rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_append, ← ofCrAnList_append,
      ← ofCrAnList_append]
  conv_lhs =>
    rhs
    rw [map_smul]
    rhs
    rw [normalOrderF_ofCrAnList, normalOrderList_eq_createFilter_append_annihilateFilter]
    rw [createFilter_append, createFilter_append, createFilter_append,
      createFilter_singleton_annihilate _ hφa, createFilter_singleton_annihilate _ hφa']
    rw [annihilateFilter_append, annihilateFilter_append, annihilateFilter_append,
      annihilateFilter_singleton_annihilate _ hφa, annihilateFilter_singleton_annihilate _ hφa']
    enter [2, 1, 1]
    simp only [List.singleton_append, List.append_assoc, List.cons_append, instCommGroup.eq_1,
      List.append_nil, Algebra.smul_mul_assoc]
    rw [← createFilter_append]
  conv_lhs =>
    lhs; lhs
    simp
  conv_lhs =>
    rhs; rhs; lhs
    simp
  rw [normalOrderSign_swap_annihilate_annihilate φa φa' hφa hφa']
  rw [smul_smul, mul_comm, ← smul_smul]
  rw [← smul_sub, ofCrAnList_append, ofCrAnList_append, ofCrAnList_append]
  conv_lhs =>
    rhs; rhs
    rw [ofCrAnList_append, ofCrAnList_append, ofCrAnList_append]
    rw [← Algebra.mul_smul_comm, ← smul_mul_assoc, ← Algebra.mul_smul_comm]
  rw [← mul_sub, ← sub_mul, ← mul_sub]
  apply congrArg
  conv_rhs => rw [mul_assoc, mul_assoc]
  apply congrArg
  rw [mul_assoc]
  apply congrArg
  rw [ofCrAnList_append, ofCrAnList_singleton, ofCrAnList_singleton]
  rw [ofCrAnList_append, ofCrAnList_singleton, ofCrAnList_singleton, smul_mul_assoc]

/-!

## Super commututators involving a normal order.

-/

lemma ofCrAnList_superCommuteF_normalOrderF_ofCrAnList (φs φs' : List 𝓕.CrAnStates) :
    [ofCrAnList φs, 𝓝ᶠ(ofCrAnList φs')]ₛca =
    ofCrAnList φs * 𝓝ᶠ(ofCrAnList φs') -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofCrAnList φs') * ofCrAnList φs := by
  simp [normalOrderF_ofCrAnList, map_smul, superCommuteF_ofCrAnList_ofCrAnList, ofCrAnList_append,
    smul_sub, smul_smul, mul_comm]

lemma ofCrAnList_superCommuteF_normalOrderF_ofStateList (φs : List 𝓕.CrAnStates)
    (φs' : List 𝓕.States) : [ofCrAnList φs, 𝓝ᶠ(ofStateList φs')]ₛca =
    ofCrAnList φs * 𝓝ᶠ(ofStateList φs') -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofStateList φs') * ofCrAnList φs := by
  rw [ofStateList_sum, map_sum, Finset.mul_sum, Finset.smul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib, map_sum]
  congr
  funext n
  rw [ofCrAnList_superCommuteF_normalOrderF_ofCrAnList,
    CrAnSection.statistics_eq_state_statistics]

/-!

## Multiplications with normal order written in terms of super commute.

-/

lemma ofCrAnList_mul_normalOrderF_ofStateList_eq_superCommuteF (φs : List 𝓕.CrAnStates)
    (φs' : List 𝓕.States) :
    ofCrAnList φs * 𝓝ᶠ(ofStateList φs') =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofStateList φs') * ofCrAnList φs
    + [ofCrAnList φs, 𝓝ᶠ(ofStateList φs')]ₛca := by
  simp [ofCrAnList_superCommuteF_normalOrderF_ofStateList]

lemma ofCrAnState_mul_normalOrderF_ofStateList_eq_superCommuteF (φ : 𝓕.CrAnStates)
    (φs' : List 𝓕.States) : ofCrAnState φ * 𝓝ᶠ(ofStateList φs') =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofStateList φs') * ofCrAnState φ
    + [ofCrAnState φ, 𝓝ᶠ(ofStateList φs')]ₛca := by
  simp [← ofCrAnList_singleton, ofCrAnList_mul_normalOrderF_ofStateList_eq_superCommuteF]

lemma anPart_mul_normalOrderF_ofStateList_eq_superCommuteF (φ : 𝓕.States)
    (φs' : List 𝓕.States) :
    anPart φ * 𝓝ᶠ(ofStateList φs') =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofStateList φs' * anPart φ)
    + [anPart φ, 𝓝ᶠ(ofStateList φs')]ₛca := by
  rw [normalOrderF_mul_anPart]
  match φ with
  | .inAsymp φ => simp
  | .position φ => simp [ofCrAnState_mul_normalOrderF_ofStateList_eq_superCommuteF, crAnStatistics]
  | .outAsymp φ => simp [ofCrAnState_mul_normalOrderF_ofStateList_eq_superCommuteF, crAnStatistics]

end

end CrAnAlgebra

end FieldSpecification
