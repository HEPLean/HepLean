/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.NormalOrder
import HepLean.PerturbationTheory.Algebras.FieldOpFreeAlgebra.SuperCommute
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Normal Ordering in the FieldOpFreeAlgebra

In the module
`HepLean.PerturbationTheory.FieldSpecification.NormalOrder`
we defined the normal ordering of a list of `CrAnFieldOp`.
In this module we extend the normal ordering to a linear map on `FieldOpFreeAlgebra`.

We derive properties of this normal ordering.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace FieldOpFreeAlgebra

noncomputable section

/-- The linear map on the free creation and annihlation
  algebra defined as the map taking
  a list of CrAnFieldOp to the normal-ordered list of states multiplied by
  the sign corresponding to the number of fermionic-fermionic
  exchanges done in ordering. -/
def normalOrderF : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕 :=
  Basis.constr ofCrAnListFBasis ℂ fun φs =>
  normalOrderSign φs • ofCrAnListF (normalOrderList φs)

@[inherit_doc normalOrderF]
scoped[FieldSpecification.FieldOpFreeAlgebra] notation "𝓝ᶠ(" a ")" => normalOrderF a

lemma normalOrderF_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    𝓝ᶠ(ofCrAnListF φs) = normalOrderSign φs • ofCrAnListF (normalOrderList φs) := by
  rw [← ofListBasis_eq_ofList, normalOrderF, Basis.constr_basis]

lemma ofCrAnListF_eq_normalOrderF (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnListF (normalOrderList φs) = normalOrderSign φs • 𝓝ᶠ(ofCrAnListF φs) := by
  rw [normalOrderF_ofCrAnListF, normalOrderList, smul_smul, normalOrderSign,
    Wick.koszulSign_mul_self, one_smul]

lemma normalOrderF_one : normalOrderF (𝓕 := 𝓕) 1 = 1 := by
  rw [← ofCrAnListF_nil, normalOrderF_ofCrAnListF, normalOrderSign_nil, normalOrderList_nil,
    ofCrAnListF_nil, one_smul]

lemma normalOrderF_normalOrderF_mid (a b c : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * b * c) = 𝓝ᶠ(a * 𝓝ᶠ(b) * c) := by
  let pc (c : 𝓕.FieldOpFreeAlgebra) (hc : c ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
    Prop := 𝓝ᶠ(a * b * c) = 𝓝ᶠ(a * 𝓝ᶠ(b) * c)
  change pc c (Basis.mem_span _ c)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl⟩ := hx
    simp only [ofListBasis_eq_ofList, pc]
    let pb (b : 𝓕.FieldOpFreeAlgebra) (hb : b ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
      Prop := 𝓝ᶠ(a * b * ofCrAnListF φs) = 𝓝ᶠ(a * 𝓝ᶠ(b) * ofCrAnListF φs)
    change pb b (Basis.mem_span _ b)
    apply Submodule.span_induction
    · intro x hx
      obtain ⟨φs', rfl⟩ := hx
      simp only [ofListBasis_eq_ofList, pb]
      let pa (a : 𝓕.FieldOpFreeAlgebra) (ha : a ∈ Submodule.span ℂ (Set.range ofCrAnListFBasis)) :
        Prop := 𝓝ᶠ(a * ofCrAnListF φs' * ofCrAnListF φs) = 𝓝ᶠ(a * 𝓝ᶠ(ofCrAnListF φs') * ofCrAnListF φs)
      change pa a (Basis.mem_span _ a)
      apply Submodule.span_induction
      · intro x hx
        obtain ⟨φs'', rfl⟩ := hx
        simp only [ofListBasis_eq_ofList, pa]
        rw [normalOrderF_ofCrAnListF]
        simp only [← ofCrAnListF_append, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, map_smul]
        rw [normalOrderF_ofCrAnListF, normalOrderF_ofCrAnListF, smul_smul]
        congr 1
        · simp only [normalOrderSign, normalOrderList]
          rw [Wick.koszulSign_of_append_eq_insertionSort, mul_comm]
        · congr 1
          simp only [normalOrderList]
          rw [HepLean.List.insertionSort_append_insertionSort_append]
      · simp [pa]
      · intro x y hx hy h1 h2
        simp_all [pa, add_mul]
      · intro x hx h
        simp_all [pa]
    · simp [pb]
    · intro x y hx hy h1 h2
      simp_all [pb, mul_add, add_mul]
    · intro x hx h
      simp_all [pb]
  · simp [pc]
  · intro x y hx hy h1 h2
    simp_all [pc, mul_add]
  · intro x hx h hp
    simp_all [pc]

lemma normalOrderF_normalOrderF_right (a b : 𝓕.FieldOpFreeAlgebra) : 𝓝ᶠ(a * b) = 𝓝ᶠ(a * 𝓝ᶠ(b)) := by
  trans 𝓝ᶠ(a * b * 1)
  · simp
  · rw [normalOrderF_normalOrderF_mid]
    simp

lemma normalOrderF_normalOrderF_left (a b : 𝓕.FieldOpFreeAlgebra) : 𝓝ᶠ(a * b) = 𝓝ᶠ(𝓝ᶠ(a) * b) := by
  trans 𝓝ᶠ(1 * a * b)
  · simp
  · rw [normalOrderF_normalOrderF_mid]
    simp

/-!

## Normal ordering with a creation operator on the left or annihilation on the right

-/

lemma normalOrderF_ofCrAnListF_cons_create (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (φs : List 𝓕.CrAnFieldOp) :
    𝓝ᶠ(ofCrAnListF (φ :: φs)) = ofCrAnOpF φ * 𝓝ᶠ(ofCrAnListF φs) := by
  rw [normalOrderF_ofCrAnListF, normalOrderSign_cons_create φ hφ,
    normalOrderList_cons_create φ hφ φs]
  rw [ofCrAnListF_cons, normalOrderF_ofCrAnListF, mul_smul_comm]

lemma normalOrderF_create_mul (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.create) (a : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(ofCrAnOpF φ * a) = ofCrAnOpF φ * 𝓝ᶠ(a) := by
  change (normalOrderF ∘ₗ mulLinearMap (ofCrAnOpF φ)) a =
    (mulLinearMap (ofCrAnOpF φ) ∘ₗ normalOrderF) a
  refine LinearMap.congr_fun (ofCrAnListFBasis.ext fun l ↦ ?_) a
  simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
    LinearMap.coe_comp, Function.comp_apply]
  rw [← ofCrAnListF_cons, normalOrderF_ofCrAnListF_cons_create φ hφ]

lemma normalOrderF_ofCrAnListF_append_annihilate (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate) (φs : List 𝓕.CrAnFieldOp) :
    𝓝ᶠ(ofCrAnListF (φs ++ [φ])) = 𝓝ᶠ(ofCrAnListF φs) * ofCrAnOpF φ := by
  rw [normalOrderF_ofCrAnListF, normalOrderSign_append_annihlate φ hφ φs,
    normalOrderList_append_annihilate φ hφ φs, ofCrAnListF_append, ofCrAnListF_singleton,
      normalOrderF_ofCrAnListF, smul_mul_assoc]

lemma normalOrderF_mul_annihilate (φ : 𝓕.CrAnFieldOp)
    (hφ : 𝓕 |>ᶜ φ = CreateAnnihilate.annihilate)
    (a : FieldOpFreeAlgebra 𝓕) : 𝓝ᶠ(a * ofCrAnOpF φ) = 𝓝ᶠ(a) * ofCrAnOpF φ := by
  change (normalOrderF ∘ₗ mulLinearMap.flip (ofCrAnOpF φ)) a =
    (mulLinearMap.flip (ofCrAnOpF φ) ∘ₗ normalOrderF) a
  refine LinearMap.congr_fun (ofCrAnListFBasis.ext fun l ↦ ?_) a
  simp only [mulLinearMap, ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_append, ofCrAnListF_singleton,
    normalOrderF_ofCrAnListF_append_annihilate φ hφ]

lemma normalOrderF_crPartF_mul (φ : 𝓕.FieldOp) (a : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(crPartF φ * a) =
    crPartF φ * 𝓝ᶠ(a) := by
  match φ with
  | .inAsymp φ =>
    rw [crPartF]
    exact normalOrderF_create_mul ⟨FieldOp.inAsymp φ, ()⟩ rfl a
  | .position φ =>
    rw [crPartF]
    exact normalOrderF_create_mul _ rfl _
  | .outAsymp φ => simp

lemma normalOrderF_mul_anPartF (φ : 𝓕.FieldOp) (a : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * anPartF φ) =
    𝓝ᶠ(a) * anPartF φ := by
  match φ with
  | .inAsymp φ => simp
  | .position φ =>
    rw [anPartF]
    exact normalOrderF_mul_annihilate _ rfl _
  | .outAsymp φ =>
    rw [anPartF]
    refine normalOrderF_mul_annihilate _ rfl _

/-!

## Normal ordering for an adjacent creation and annihliation state

The main result of this section is `normalOrderF_superCommuteF_annihilate_create`.
-/

lemma normalOrderF_swap_create_annihlate_ofCrAnListF_ofCrAnListF (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (φs φs' : List 𝓕.CrAnFieldOp) :
    𝓝ᶠ(ofCrAnListF φs' * ofCrAnOpF φc * ofCrAnOpF φa * ofCrAnListF φs) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) •
    𝓝ᶠ(ofCrAnListF φs' * ofCrAnOpF φa * ofCrAnOpF φc * ofCrAnListF φs) := by
  rw [mul_assoc, mul_assoc, ← ofCrAnListF_cons, ← ofCrAnListF_cons, ← ofCrAnListF_append]
  rw [normalOrderF_ofCrAnListF, normalOrderSign_swap_create_annihlate φc φa hφc hφa]
  rw [normalOrderList_swap_create_annihlate φc φa hφc hφa, ← smul_smul, ← normalOrderF_ofCrAnListF]
  rw [ofCrAnListF_append, ofCrAnListF_cons, ofCrAnListF_cons]
  noncomm_ring

lemma normalOrderF_swap_create_annihlate_ofCrAnListF (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (φs : List 𝓕.CrAnFieldOp) (a : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(ofCrAnListF φs * ofCrAnOpF φc * ofCrAnOpF φa * a) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) •
    𝓝ᶠ(ofCrAnListF φs * ofCrAnOpF φa * ofCrAnOpF φc * a) := by
  change (normalOrderF ∘ₗ mulLinearMap (ofCrAnListF φs * ofCrAnOpF φc * ofCrAnOpF φa)) a =
    (smulLinearMap _ ∘ₗ normalOrderF ∘ₗ
    mulLinearMap (ofCrAnListF φs * ofCrAnOpF φa * ofCrAnOpF φc)) a
  refine LinearMap.congr_fun (ofCrAnListFBasis.ext fun l ↦ ?_) a
  simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
    LinearMap.coe_comp, Function.comp_apply, instCommGroup.eq_1]
  rw [normalOrderF_swap_create_annihlate_ofCrAnListF_ofCrAnListF φc φa hφc hφa]
  rfl

lemma normalOrderF_swap_create_annihlate (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * ofCrAnOpF φc * ofCrAnOpF φa * b) = 𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa) •
    𝓝ᶠ(a * ofCrAnOpF φa * ofCrAnOpF φc * b) := by
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  change (normalOrderF ∘ₗ mulLinearMap.flip (ofCrAnOpF φc * (ofCrAnOpF φa * b))) a =
    (smulLinearMap (𝓢(𝓕 |>ₛ φc, 𝓕 |>ₛ φa)) ∘ₗ
    normalOrderF ∘ₗ mulLinearMap.flip (ofCrAnOpF φa * (ofCrAnOpF φc * b))) a
  refine LinearMap.congr_fun (ofCrAnListFBasis.ext fun l ↦ ?_) _
  simp only [mulLinearMap, ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk, instCommGroup.eq_1, ← mul_assoc,
      normalOrderF_swap_create_annihlate_ofCrAnListF φc φa hφc hφa]
  rfl

lemma normalOrderF_superCommuteF_create_annihilate (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * [ofCrAnOpF φc, ofCrAnOpF φa]ₛca * b) = 0 := by
  simp only [superCommuteF_ofCrAnOpF_ofCrAnOpF, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [mul_sub, sub_mul, map_sub, ← smul_mul_assoc, ← mul_assoc, ← mul_assoc,
    normalOrderF_swap_create_annihlate φc φa hφc hφa]
  simp

lemma normalOrderF_superCommuteF_annihilate_create (φc φa : 𝓕.CrAnFieldOp)
    (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create) (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnOpF φc]ₛca * b) = 0 := by
  rw [superCommuteF_ofCrAnOpF_ofCrAnOpF_symm]
  simp only [instCommGroup.eq_1, neg_smul, mul_neg, Algebra.mul_smul_comm, neg_mul,
    Algebra.smul_mul_assoc, map_neg, map_smul, neg_eq_zero, smul_eq_zero]
  exact Or.inr (normalOrderF_superCommuteF_create_annihilate φc φa hφc hφa ..)

lemma normalOrderF_swap_crPartF_anPartF (φ φ' : 𝓕.FieldOp) (a b : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * (crPartF φ) * (anPartF φ') * b) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    𝓝ᶠ(a * (anPartF φ') * (crPartF φ) * b) := by
  match φ, φ' with
  | _, .inAsymp φ' => simp
  | .outAsymp φ, _ => simp
  | .position φ, .position φ' =>
    simp only [crPartF_position, anPartF_position, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihlate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod]
    rfl; rfl
  | .inAsymp φ, .outAsymp φ' =>
    simp only [crPartF_negAsymp, anPartF_posAsymp, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihlate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod]
    rfl; rfl
  | .inAsymp φ, .position φ' =>
    simp only [crPartF_negAsymp, anPartF_position, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihlate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod]
    rfl; rfl
  | .position φ, .outAsymp φ' =>
    simp only [crPartF_position, anPartF_posAsymp, instCommGroup.eq_1]
    rw [normalOrderF_swap_create_annihlate]
    simp only [instCommGroup.eq_1, crAnStatistics, Function.comp_apply, crAnFieldOpToFieldOp_prod]
    rfl; rfl

/-!

## Normal ordering for an anPartF and crPartF

Using the results from above.

-/

lemma normalOrderF_swap_anPartF_crPartF (φ φ' : 𝓕.FieldOp) (a b : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * (anPartF φ) * (crPartF φ') * b) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') • 𝓝ᶠ(a * (crPartF φ') *
      (anPartF φ) * b) := by
  simp [normalOrderF_swap_crPartF_anPartF, smul_smul]

lemma normalOrderF_superCommuteF_crPartF_anPartF (φ φ' : 𝓕.FieldOp) (a b : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * superCommuteF
      (crPartF φ) (anPartF φ') * b) = 0 := by
  match φ, φ' with
  | _, .inAsymp φ' => simp
  | .outAsymp φ', _ => simp
  | .position φ, .position φ' =>
    rw [crPartF_position, anPartF_position]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..
  | .inAsymp φ, .outAsymp φ' =>
    rw [crPartF_negAsymp, anPartF_posAsymp]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..
  | .inAsymp φ, .position φ' =>
    rw [crPartF_negAsymp, anPartF_position]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..
  | .position φ, .outAsymp φ' =>
    rw [crPartF_position, anPartF_posAsymp]
    exact normalOrderF_superCommuteF_create_annihilate _ _ rfl rfl ..

lemma normalOrderF_superCommuteF_anPartF_crPartF (φ φ' : 𝓕.FieldOp) (a b : FieldOpFreeAlgebra 𝓕) :
    𝓝ᶠ(a * superCommuteF
    (anPartF φ) (crPartF φ') * b) = 0 := by
  match φ, φ' with
  | .inAsymp φ', _ => simp
  | _, .outAsymp φ' => simp
  | .position φ, .position φ' =>
    rw [anPartF_position, crPartF_position]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..
  | .outAsymp φ', .inAsymp φ =>
    simp only [anPartF_posAsymp, crPartF_negAsymp]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..
  | .position φ', .inAsymp φ =>
    simp only [anPartF_position, crPartF_negAsymp]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..
  | .outAsymp φ, .position φ' =>
    simp only [anPartF_posAsymp, crPartF_position]
    exact normalOrderF_superCommuteF_annihilate_create _ _ rfl rfl ..

/-!

## The normal ordering of a product of two states

-/

@[simp]
lemma normalOrderF_crPartF_mul_crPartF (φ φ' : 𝓕.FieldOp) :
    𝓝ᶠ(crPartF φ * crPartF φ') =
    crPartF φ * crPartF φ' := by
  rw [normalOrderF_crPartF_mul]
  conv_lhs => rw [← mul_one (crPartF φ')]
  rw [normalOrderF_crPartF_mul, normalOrderF_one]
  simp

@[simp]
lemma normalOrderF_anPartF_mul_anPartF (φ φ' : 𝓕.FieldOp) :
    𝓝ᶠ(anPartF φ * anPartF φ') =
    anPartF φ * anPartF φ' := by
  rw [normalOrderF_mul_anPartF]
  conv_lhs => rw [← one_mul (anPartF φ)]
  rw [normalOrderF_mul_anPartF, normalOrderF_one]
  simp

@[simp]
lemma normalOrderF_crPartF_mul_anPartF (φ φ' : 𝓕.FieldOp) :
    𝓝ᶠ(crPartF φ * anPartF φ') =
    crPartF φ * anPartF φ' := by
  rw [normalOrderF_crPartF_mul]
  conv_lhs => rw [← one_mul (anPartF φ')]
  rw [normalOrderF_mul_anPartF, normalOrderF_one]
  simp

@[simp]
lemma normalOrderF_anPartF_mul_crPartF (φ φ' : 𝓕.FieldOp) :
    𝓝ᶠ(anPartF φ * crPartF φ') =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    (crPartF φ' * anPartF φ) := by
  conv_lhs => rw [← one_mul (anPartF φ * crPartF φ')]
  conv_lhs => rw [← mul_one (1 * (anPartF φ *
    crPartF φ'))]
  rw [← mul_assoc, normalOrderF_swap_anPartF_crPartF]
  simp

lemma normalOrderF_ofFieldOpF_mul_ofFieldOpF (φ φ' : 𝓕.FieldOp) :
    𝓝ᶠ(ofFieldOpF φ * ofFieldOpF φ') =
    crPartF φ * crPartF φ' +
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φ') •
    (crPartF φ' * anPartF φ) +
    crPartF φ * anPartF φ' +
    anPartF φ * anPartF φ' := by
  rw [ofFieldOpF_eq_crPartF_add_anPartF, ofFieldOpF_eq_crPartF_add_anPartF, mul_add, add_mul, add_mul]
  simp only [map_add, normalOrderF_crPartF_mul_crPartF, normalOrderF_anPartF_mul_crPartF,
    instCommGroup.eq_1, normalOrderF_crPartF_mul_anPartF, normalOrderF_anPartF_mul_anPartF]
  abel

/-!

## Normal order with super commutors

-/

TODO "Split the following two lemmas up into smaller parts."

lemma normalOrderF_superCommuteF_ofCrAnListF_create_create_ofCrAnListF
    (φc φc' : 𝓕.CrAnFieldOp) (hφc : 𝓕 |>ᶜ φc = CreateAnnihilate.create)
    (hφc' : 𝓕 |>ᶜ φc' = CreateAnnihilate.create) (φs φs' : List 𝓕.CrAnFieldOp) :
    (𝓝ᶠ(ofCrAnListF φs * [ofCrAnOpF φc, ofCrAnOpF φc']ₛca * ofCrAnListF φs')) =
      normalOrderSign (φs ++ φc' :: φc :: φs') •
    (ofCrAnListF (createFilter φs) * [ofCrAnOpF φc, ofCrAnOpF φc']ₛca *
      ofCrAnListF (createFilter φs') * ofCrAnListF (annihilateFilter (φs ++ φs'))) := by
  rw [superCommuteF_ofCrAnOpF_ofCrAnOpF, mul_sub, sub_mul, map_sub]
  conv_lhs =>
    lhs; rhs
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_append, ← ofCrAnListF_append,
      ← ofCrAnListF_append]
  conv_lhs =>
    lhs
    rw [normalOrderF_ofCrAnListF, normalOrderList_eq_createFilter_append_annihilateFilter]
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
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_append, ← ofCrAnListF_append,
      ← ofCrAnListF_append]
  conv_lhs =>
    rhs
    rw [map_smul]
    rhs
    rw [normalOrderF_ofCrAnListF, normalOrderList_eq_createFilter_append_annihilateFilter]
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
  rw [← smul_sub, ofCrAnListF_append, ofCrAnListF_append, ofCrAnListF_append]
  conv_lhs =>
    rhs; rhs
    rw [ofCrAnListF_append, ofCrAnListF_append, ofCrAnListF_append]
    rw [← smul_mul_assoc, ← smul_mul_assoc, ← Algebra.mul_smul_comm]
  rw [← sub_mul, ← sub_mul, ← mul_sub, ofCrAnListF_append, ofCrAnListF_singleton,
    ofCrAnListF_singleton]
  rw [ofCrAnListF_append, ofCrAnListF_singleton, ofCrAnListF_singleton, smul_mul_assoc]

lemma normalOrderF_superCommuteF_ofCrAnListF_annihilate_annihilate_ofCrAnListF
    (φa φa' : 𝓕.CrAnFieldOp)
    (hφa : 𝓕 |>ᶜ φa = CreateAnnihilate.annihilate)
    (hφa' : 𝓕 |>ᶜ φa' = CreateAnnihilate.annihilate)
    (φs φs' : List 𝓕.CrAnFieldOp) :
    𝓝ᶠ(ofCrAnListF φs * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca * ofCrAnListF φs') =
      normalOrderSign (φs ++ φa' :: φa :: φs') •
    (ofCrAnListF (createFilter (φs ++ φs'))
      * ofCrAnListF (annihilateFilter φs) * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca
      * ofCrAnListF (annihilateFilter φs')) := by
  rw [superCommuteF_ofCrAnOpF_ofCrAnOpF, mul_sub, sub_mul, map_sub]
  conv_lhs =>
    lhs; rhs
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_append, ← ofCrAnListF_append,
      ← ofCrAnListF_append]
  conv_lhs =>
    lhs
    rw [normalOrderF_ofCrAnListF, normalOrderList_eq_createFilter_append_annihilateFilter]
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
    rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_append, ← ofCrAnListF_append,
      ← ofCrAnListF_append]
  conv_lhs =>
    rhs
    rw [map_smul]
    rhs
    rw [normalOrderF_ofCrAnListF, normalOrderList_eq_createFilter_append_annihilateFilter]
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
  rw [← smul_sub, ofCrAnListF_append, ofCrAnListF_append, ofCrAnListF_append]
  conv_lhs =>
    rhs; rhs
    rw [ofCrAnListF_append, ofCrAnListF_append, ofCrAnListF_append]
    rw [← Algebra.mul_smul_comm, ← smul_mul_assoc, ← Algebra.mul_smul_comm]
  rw [← mul_sub, ← sub_mul, ← mul_sub]
  apply congrArg
  conv_rhs => rw [mul_assoc, mul_assoc]
  apply congrArg
  rw [mul_assoc]
  apply congrArg
  rw [ofCrAnListF_append, ofCrAnListF_singleton, ofCrAnListF_singleton]
  rw [ofCrAnListF_append, ofCrAnListF_singleton, ofCrAnListF_singleton, smul_mul_assoc]

/-!

## Super commututators involving a normal order.

-/

lemma ofCrAnListF_superCommuteF_normalOrderF_ofCrAnListF (φs φs' : List 𝓕.CrAnFieldOp) :
    [ofCrAnListF φs, 𝓝ᶠ(ofCrAnListF φs')]ₛca =
    ofCrAnListF φs * 𝓝ᶠ(ofCrAnListF φs') -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofCrAnListF φs') * ofCrAnListF φs := by
  simp [normalOrderF_ofCrAnListF, map_smul, superCommuteF_ofCrAnListF_ofCrAnListF, ofCrAnListF_append,
    smul_sub, smul_smul, mul_comm]

lemma ofCrAnListF_superCommuteF_normalOrderF_ofFieldOpListF (φs : List 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.FieldOp) : [ofCrAnListF φs, 𝓝ᶠ(ofFieldOpListF φs')]ₛca =
    ofCrAnListF φs * 𝓝ᶠ(ofFieldOpListF φs') -
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofFieldOpListF φs') * ofCrAnListF φs := by
  rw [ofFieldOpListF_sum, map_sum, Finset.mul_sum, Finset.smul_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib, map_sum]
  congr
  funext n
  rw [ofCrAnListF_superCommuteF_normalOrderF_ofCrAnListF,
    CrAnSection.statistics_eq_state_statistics]

/-!

## Multiplications with normal order written in terms of super commute.

-/

lemma ofCrAnListF_mul_normalOrderF_ofFieldOpListF_eq_superCommuteF (φs : List 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.FieldOp) :
    ofCrAnListF φs * 𝓝ᶠ(ofFieldOpListF φs') =
    𝓢(𝓕 |>ₛ φs, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofFieldOpListF φs') * ofCrAnListF φs
    + [ofCrAnListF φs, 𝓝ᶠ(ofFieldOpListF φs')]ₛca := by
  simp [ofCrAnListF_superCommuteF_normalOrderF_ofFieldOpListF]

lemma ofCrAnOpF_mul_normalOrderF_ofFieldOpListF_eq_superCommuteF (φ : 𝓕.CrAnFieldOp)
    (φs' : List 𝓕.FieldOp) : ofCrAnOpF φ * 𝓝ᶠ(ofFieldOpListF φs') =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofFieldOpListF φs') * ofCrAnOpF φ
    + [ofCrAnOpF φ, 𝓝ᶠ(ofFieldOpListF φs')]ₛca := by
  simp [← ofCrAnListF_singleton, ofCrAnListF_mul_normalOrderF_ofFieldOpListF_eq_superCommuteF]

lemma anPartF_mul_normalOrderF_ofFieldOpListF_eq_superCommuteF (φ : 𝓕.FieldOp)
    (φs' : List 𝓕.FieldOp) :
    anPartF φ * 𝓝ᶠ(ofFieldOpListF φs') =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs') • 𝓝ᶠ(ofFieldOpListF φs' * anPartF φ)
    + [anPartF φ, 𝓝ᶠ(ofFieldOpListF φs')]ₛca := by
  rw [normalOrderF_mul_anPartF]
  match φ with
  | .inAsymp φ => simp
  | .position φ => simp [ofCrAnOpF_mul_normalOrderF_ofFieldOpListF_eq_superCommuteF, crAnStatistics]
  | .outAsymp φ => simp [ofCrAnOpF_mul_normalOrderF_ofFieldOpListF_eq_superCommuteF, crAnStatistics]

end

end FieldOpFreeAlgebra

end FieldSpecification
