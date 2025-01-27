/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.Basic
/-!

# Normal Ordering on Field operator algebra

-/

namespace FieldSpecification
open CrAnAlgebra
open StateAlgebra
open ProtoOperatorAlgebra
open HepLean.List
open WickContraction
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-!

## Normal order on super-commutators.

The main result of this is
`ι_normalOrder_superCommute_eq_zero_mul`
which states that applying `ι` to the normal order of something containing a super-commutator
is zero.

-/

lemma ι_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero
    (φa φa' : 𝓕.CrAnStates) (φs φs' : List 𝓕.CrAnStates) :
    ι 𝓝(ofCrAnList φs * [ofCrAnState φa, ofCrAnState φa']ₛca * ofCrAnList φs') = 0 := by
  rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa) with hφa | hφa
  <;> rcases CreateAnnihilate.eq_create_or_annihilate (𝓕 |>ᶜ φa') with hφa' | hφa'
  · rw [normalOrder_superCommute_ofCrAnList_create_create_ofCrAnList φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul, ι_superCommute_of_create_create φa φa' hφa hφa']
    simp
  · rw [normalOrder_superCommute_create_annihilate φa φa' hφa hφa' (ofCrAnList φs)
      (ofCrAnList φs')]
    simp
  · rw [normalOrder_superCommute_annihilate_create φa' φa hφa' hφa (ofCrAnList φs)
      (ofCrAnList φs')]
    simp
  · rw [normalOrder_superCommute_ofCrAnList_annihilate_annihilate_ofCrAnList φa φa' hφa hφa' φs φs']
    rw [map_smul, map_mul, map_mul, map_mul,
      ι_superCommute_of_annihilate_annihilate φa φa' hφa hφa']
    simp

lemma ι_normalOrder_superCommute_ofCrAnList_eq_zero
    (φa φa' : 𝓕.CrAnStates) (φs : List 𝓕.CrAnStates)
    (a : 𝓕.CrAnAlgebra) : ι 𝓝(ofCrAnList φs * [ofCrAnState φa, ofCrAnState φa']ₛca * a) = 0 := by
  have hf : ι.toLinearMap ∘ₗ normalOrder ∘ₗ
      mulLinearMap (ofCrAnList φs * [ofCrAnState φa, ofCrAnState φa']ₛca) = 0 := by
    apply ofCrAnListBasis.ext
    intro l
    simp only [CrAnAlgebra.ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply,
      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    exact ι_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero φa φa' φs l
  change (ι.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap ((ofCrAnList φs * [ofCrAnState φa, ofCrAnState φa']ₛca))) a = 0
  rw [hf]
  simp

lemma ι_normalOrder_superCommute_ofCrAnState_eq_zero_mul (φa φa' : 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    ι 𝓝(a * [ofCrAnState φa, ofCrAnState φa']ₛca * b) = 0 := by
  rw [mul_assoc]
  change (ι.toLinearMap ∘ₗ normalOrder ∘ₗ mulLinearMap.flip
    ([ofCrAnState φa, ofCrAnState φa']ₛca * b)) a = 0
  have hf : ι.toLinearMap ∘ₗ normalOrder ∘ₗ mulLinearMap.flip
      ([ofCrAnState φa, ofCrAnState φa']ₛca * b) = 0 := by
    apply ofCrAnListBasis.ext
    intro l
    simp only [mulLinearMap, CrAnAlgebra.ofListBasis_eq_ofList, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk,
      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
    rw [← mul_assoc]
    exact ι_normalOrder_superCommute_ofCrAnList_eq_zero φa φa' _ _
  rw [hf]
  simp

lemma ι_normalOrder_superCommute_ofCrAnState_ofCrAnList_eq_zero_mul (φa : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates)
    (a b : 𝓕.CrAnAlgebra) :
    ι 𝓝(a * [ofCrAnState φa, ofCrAnList φs]ₛca * b) = 0 := by
  rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList_eq_sum]
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b, ofCrAnList_singleton]
  rw [ι_normalOrder_superCommute_ofCrAnState_eq_zero_mul]

lemma ι_normalOrder_superCommute_ofCrAnList_ofCrAnState_eq_zero_mul (φa : 𝓕.CrAnStates)
    (φs : List 𝓕.CrAnStates) (a b : 𝓕.CrAnAlgebra) :
    ι 𝓝(a * [ofCrAnList φs, ofCrAnState φa]ₛca * b) = 0 := by
  rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList_symm, ofCrAnList_singleton]
  simp only [FieldStatistic.instCommGroup.eq_1, FieldStatistic.ofList_singleton, mul_neg,
    Algebra.mul_smul_comm, neg_mul, Algebra.smul_mul_assoc, map_neg, map_smul]
  rw [ι_normalOrder_superCommute_ofCrAnState_ofCrAnList_eq_zero_mul]
  simp

lemma ι_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero_mul
    (φs φs' : List 𝓕.CrAnStates) (a b : 𝓕.CrAnAlgebra) :
    ι 𝓝(a * [ofCrAnList φs, ofCrAnList φs']ₛca * b) = 0 := by
  rw [superCommute_ofCrAnList_ofCrAnList_eq_sum, Finset.mul_sum, Finset.sum_mul]
  rw [map_sum, map_sum]
  apply Fintype.sum_eq_zero
  intro n
  rw [← mul_assoc, ← mul_assoc]
  rw [mul_assoc _ _ b]
  rw [ι_normalOrder_superCommute_ofCrAnList_ofCrAnState_eq_zero_mul]

lemma ι_normalOrder_superCommute_ofCrAnList_eq_zero_mul
    (φs : List 𝓕.CrAnStates)
    (a b c : 𝓕.CrAnAlgebra) :
    ι 𝓝(a * [ofCrAnList φs, c]ₛca * b) = 0 := by
  change (ι.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute (ofCrAnList φs)) c = 0
  have hf : (ι.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute (ofCrAnList φs)) = 0 := by
    apply ofCrAnListBasis.ext
    intro φs'
    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, CrAnAlgebra.ofListBasis_eq_ofList,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [ι_normalOrder_superCommute_ofCrAnList_ofCrAnList_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma ι_normalOrder_superCommute_eq_zero_mul
    (a b c d : 𝓕.CrAnAlgebra) : ι 𝓝(a * [d, c]ₛca * b) = 0 := by
  change (ι.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute.flip c) d = 0
  have hf : (ι.toLinearMap ∘ₗ normalOrder ∘ₗ
    mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommute.flip c) = 0 := by
    apply ofCrAnListBasis.ext
    intro φs
    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, CrAnAlgebra.ofListBasis_eq_ofList,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
      LinearMap.zero_apply]
    rw [ι_normalOrder_superCommute_ofCrAnList_eq_zero_mul]
  rw [hf]
  simp

@[simp]
lemma ι_normalOrder_superCommute_eq_zero_mul_right (b c d : 𝓕.CrAnAlgebra) :
    ι 𝓝([d, c]ₛca * b) = 0 := by
  rw [← ι_normalOrder_superCommute_eq_zero_mul 1 b c d]
  simp

@[simp]
lemma ι_normalOrder_superCommute_eq_zero_mul_left (a c d : 𝓕.CrAnAlgebra) :
    ι 𝓝(a * [d, c]ₛca) = 0 := by
  rw [← ι_normalOrder_superCommute_eq_zero_mul a 1 c d]
  simp

@[simp]
lemma ι_normalOrder_superCommute_eq_zero_mul_mul_right (a b1 b2 c d: 𝓕.CrAnAlgebra) :
    ι 𝓝(a * [d, c]ₛca * b1 * b2) = 0 := by
  rw [← ι_normalOrder_superCommute_eq_zero_mul a (b1 * b2) c d]
  congr 2
  noncomm_ring

@[simp]
lemma ι_normalOrder_superCommute_eq_zero (c d : 𝓕.CrAnAlgebra) : ι 𝓝([d, c]ₛca) = 0 := by
  rw [← ι_normalOrder_superCommute_eq_zero_mul 1 1 c d]
  simp

/-!

## Defining normal order for `FiedOpAlgebra`.

-/

lemma ι_normalOrder_zero_of_mem_ideal (a : 𝓕.CrAnAlgebra)
    (h : a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) : ι 𝓝(a) = 0 := by
  rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at h
  let p {k : Set 𝓕.CrAnAlgebra} (a : CrAnAlgebra 𝓕) (h : a ∈ AddSubgroup.closure k) := ι 𝓝(a) = 0
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

lemma ι_normalOrder_eq_of_equiv (a b : 𝓕.CrAnAlgebra) (h : a ≈ b) :
    ι 𝓝(a) = ι 𝓝(b) := by
  rw [equiv_iff_sub_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker, ← map_sub]
  exact ι_normalOrder_zero_of_mem_ideal (a - b) h

/-- Normal ordering on `FieldOpAlgebra`. -/
noncomputable def normalOrder : FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := Quotient.lift (ι.toLinearMap ∘ₗ CrAnAlgebra.normalOrder) ι_normalOrder_eq_of_equiv
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

end FieldOpAlgebra
end FieldSpecification
