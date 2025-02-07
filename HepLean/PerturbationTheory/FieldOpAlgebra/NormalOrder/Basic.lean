/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpFreeAlgebra.NormalOrder
import HepLean.PerturbationTheory.FieldOpAlgebra.SuperCommute
/-!

# Normal Ordering on Field operator algebra

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-!

## Normal order on super-commutators.

The main result of this is
`ι_normalOrderF_superCommuteF_eq_zero_mul`
which states that applying `ι` to the normal order of something containing a super-commutator
is zero.

-/

lemma ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero
    (φa φa' : 𝓕.CrAnFieldOp) (φs φs' : List 𝓕.CrAnFieldOp) :
    ι 𝓝ᶠ(ofCrAnListF φs * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca * ofCrAnListF φs') = 0 := by
  rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa) with hφa | hφa
  <;> rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa') with hφa' | hφa'
  · rw [normalOrderF_superCommuteF_ofCrAnListF_create_create_ofCrAnListF φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul, ι_superCommuteF_of_create_create φa φa' hφa hφa']
    simp
  · rw [normalOrderF_superCommuteF_create_annihilate φa φa' hφa hφa' (ofCrAnListF φs)
      (ofCrAnListF φs')]
    simp
  · rw [normalOrderF_superCommuteF_annihilate_create φa' φa hφa' hφa (ofCrAnListF φs)
      (ofCrAnListF φs')]
    simp
  · rw [normalOrderF_superCommuteF_ofCrAnListF_annihilate_annihilate_ofCrAnListF
      φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul,
      ι_superCommuteF_of_annihilate_annihilate φa φa' hφa hφa']
    simp

lemma ι_normalOrderF_superCommuteF_ofCrAnListF_eq_zero
    (φa φa' : 𝓕.CrAnFieldOp) (φs : List 𝓕.CrAnFieldOp)
    (a : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(ofCrAnListF φs * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca * a) = 0 := by
  have hf : ι.toLinearMap ∘ₗ normalOrderF ∘ₗ
      mulLinearMap (ofCrAnListF φs * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca) = 0 := by
    apply ofCrAnListFBasis.ext
    intro l
    simp only [FieldOpFreeAlgebra.ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    exact ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero φa φa' φs l
  change (ι.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap ((ofCrAnListF φs * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca))) a = 0
  rw [hf]
  simp

lemma ι_normalOrderF_superCommuteF_ofCrAnOpF_eq_zero_mul (φa φa' : 𝓕.CrAnFieldOp)
    (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnOpF φa']ₛca * b) = 0 := by
  rw [mul_assoc]
  change (ι.toLinearMap ∘ₗ normalOrderF ∘ₗ mulLinearMap.flip
    ([ofCrAnOpF φa, ofCrAnOpF φa']ₛca * b)) a = 0
  have hf : ι.toLinearMap ∘ₗ normalOrderF ∘ₗ mulLinearMap.flip
      ([ofCrAnOpF φa, ofCrAnOpF φa']ₛca * b) = 0 := by
    apply ofCrAnListFBasis.ext
    intro l
    simp only [mulLinearMap, FieldOpFreeAlgebra.ofListBasis_eq_ofList, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk,
      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    rw [← mul_assoc]
    exact ι_normalOrderF_superCommuteF_ofCrAnListF_eq_zero φa φa' _ _
  rw [hf]
  simp

lemma ι_normalOrderF_superCommuteF_ofCrAnOpF_ofCrAnListF_eq_zero_mul (φa : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.CrAnFieldOp) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnOpF φa, ofCrAnListF φs]ₛca * b) = 0 := by
  rw [← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b, ofCrAnListF_singleton]
  rw [ι_normalOrderF_superCommuteF_ofCrAnOpF_eq_zero_mul]

lemma ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnOpF_eq_zero_mul (φa : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.CrAnFieldOp) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnListF φs, ofCrAnOpF φa]ₛca * b) = 0 := by
  rw [← ofCrAnListF_singleton, superCommuteF_ofCrAnListF_ofCrAnListF_symm, ofCrAnListF_singleton]
  simp only [FieldStatistic.instCommGroup.eq_1, FieldStatistic.ofList_singleton, mul_neg,
    Algebra.mul_smul_comm, neg_mul, Algebra.smul_mul_assoc, map_neg, map_smul]
  rw [ι_normalOrderF_superCommuteF_ofCrAnOpF_ofCrAnListF_eq_zero_mul]
  simp

lemma ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero_mul
    (φs φs' : List 𝓕.CrAnFieldOp) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnListF φs, ofCrAnListF φs']ₛca * b) = 0 := by
  rw [superCommuteF_ofCrAnListF_ofCrAnListF_eq_sum, Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b]
  rw [ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnOpF_eq_zero_mul]

lemma ι_normalOrderF_superCommuteF_ofCrAnListF_eq_zero_mul
    (φs : List 𝓕.CrAnFieldOp)
    (a b c : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [ofCrAnListF φs, c]ₛca * b) = 0 := by
  change (ι.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF (ofCrAnListF φs)) c = 0
  have hf : (ι.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF (ofCrAnListF φs)) = 0 := by
    apply ofCrAnListFBasis.ext
    intro φs'
    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma ι_normalOrderF_superCommuteF_eq_zero_mul
    (a b c d : 𝓕.FieldOpFreeAlgebra) : ι 𝓝ᶠ(a * [d, c]ₛca * b) = 0 := by
  change (ι.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF.flip c) d = 0
  have hf : (ι.toLinearMap ∘ₗ normalOrderF ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF.flip c) = 0 := by
    apply ofCrAnListFBasis.ext
    intro φs
    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [ι_normalOrderF_superCommuteF_ofCrAnListF_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma ι_normalOrder_superCommuteF_eq_zero_mul_right (b c d : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ([d, c]ₛca * b) = 0 := by
  rw [← ι_normalOrderF_superCommuteF_eq_zero_mul 1 b c d]
  simp

@[simp]
lemma ι_normalOrderF_superCommuteF_eq_zero_mul_left (a c d : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [d, c]ₛca) = 0 := by
  rw [← ι_normalOrderF_superCommuteF_eq_zero_mul a 1 c d]
  simp

@[simp]
lemma ι_normalOrderF_superCommuteF_eq_zero_mul_mul_right (a b1 b2 c d: 𝓕.FieldOpFreeAlgebra) :
    ι 𝓝ᶠ(a * [d, c]ₛca * b1 * b2) = 0 := by
  rw [← ι_normalOrderF_superCommuteF_eq_zero_mul a (b1 * b2) c d]
  congr 2
  noncomm_ring

@[simp]
lemma ι_normalOrderF_superCommuteF_eq_zero (c d : 𝓕.FieldOpFreeAlgebra) : ι 𝓝ᶠ([d, c]ₛca) = 0 := by
  rw [← ι_normalOrderF_superCommuteF_eq_zero_mul 1 1 c d]
  simp

/-!

## Defining normal order for `FiedOpAlgebra`.

-/

lemma ι_normalOrderF_zero_of_mem_ideal (a : 𝓕.FieldOpFreeAlgebra)
    (h : a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) : ι 𝓝ᶠ(a) = 0 := by
  rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at h
  let p {k : Set 𝓕.FieldOpFreeAlgebra} (a : FieldOpFreeAlgebra 𝓕)
    (h : a ∈ AddSubgroup.closure k) := ι 𝓝ᶠ(a) = 0
  change p a h
  apply AddSubgroup.closure_induction
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨a, ha, c, hc, rfl⟩ := ha
    simp only [p]
    simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq] at hc
    match hc with
    | Or.inl hc =>
      obtain ⟨φa, φa', hφa, hφa', rfl⟩ := hc
      simp [mul_sub, sub_mul, ← mul_assoc]
    | Or.inr (Or.inl hc) =>
      obtain ⟨φa, φa', hφa, hφa', rfl⟩ := hc
      simp [mul_sub, sub_mul, ← mul_assoc]
    | Or.inr (Or.inr (Or.inl hc)) =>
      obtain ⟨φa, φa', hφa, hφa', rfl⟩ := hc
      simp [mul_sub, sub_mul, ← mul_assoc]
    | Or.inr (Or.inr (Or.inr hc)) =>
      obtain ⟨φa, φa', hφa, hφa', rfl⟩ := hc
      simp [mul_sub, sub_mul, ← mul_assoc]
  · simp [p]
  · intro x y hx hy
    simp only [map_add, p]
    intro h1 h2
    simp [h1, h2]
  · intro x hx
    simp [p]

lemma ι_normalOrderF_eq_of_equiv (a b : 𝓕.FieldOpFreeAlgebra) (h : a ≈ b) :
    ι 𝓝ᶠ(a) = ι 𝓝ᶠ(b) := by
  rw [equiv_iff_sub_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker, ← map_sub]
  exact ι_normalOrderF_zero_of_mem_ideal (a - b) h

/-- For a field specification `𝓕`, `normalOrder` is the linera map

  `FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕`

  defined as the decent of `ι ∘ₗ normalOrderF` from `FieldOpFreeAlgebra 𝓕` to `FieldOpAlgebra 𝓕`.
  This decent exists because `ι ∘ₗ normalOrderF` is well-defined on equivalence classes.

  The notation `𝓝(a)` is used for `normalOrder a`. -/
noncomputable def normalOrder : FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := Quotient.lift (ι.toLinearMap ∘ₗ normalOrderF) ι_normalOrderF_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, rfl⟩ := ι_surjective x
    obtain ⟨y, rfl⟩ := ι_surjective y
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, rfl⟩ := ι_surjective y
    rw [← map_smul, ι_apply, ι_apply]
    simp

@[inherit_doc normalOrder]
scoped[FieldSpecification.FieldOpAlgebra] notation "𝓝(" a ")" => normalOrder a

end FieldOpAlgebra
end FieldSpecification
