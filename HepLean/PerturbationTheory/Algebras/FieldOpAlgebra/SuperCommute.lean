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

lemma ι_superCommute_eq_zero_of_ι_right_zero (a b : 𝓕.CrAnAlgebra) (h : ι b = 0) :
    ι [a, b]ₛca = 0 := by
  rw [superCommute_expand_bosonicProj_fermionicProj]
  rw [ι_eq_zero_iff_ι_bosonicProj_fermonicProj_zero] at h
  simp_all

lemma ι_superCommute_eq_zero_of_ι_left_zero (a b : 𝓕.CrAnAlgebra) (h : ι a = 0) :
    ι [a, b]ₛca = 0 := by
  rw [superCommute_expand_bosonicProj_fermionicProj]
  rw [ι_eq_zero_iff_ι_bosonicProj_fermonicProj_zero] at h
  simp_all

/-!

## Defining normal order for `FiedOpAlgebra`.

-/

lemma ι_superCommute_right_zero_of_mem_ideal (a b : 𝓕.CrAnAlgebra)
    (h : b ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) : ι [a, b]ₛca = 0 := by
  apply ι_superCommute_eq_zero_of_ι_right_zero
  exact (ι_eq_zero_iff_mem_ideal b).mpr h

lemma ι_superCommute_eq_of_equiv_right (a b1 b2 : 𝓕.CrAnAlgebra) (h : b1 ≈ b2) :
    ι [a, b1]ₛca = ι [a, b2]ₛca := by
  rw [equiv_iff_sub_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker, ← map_sub]
  exact ι_superCommute_right_zero_of_mem_ideal a (b1 - b2) h

noncomputable def superCommuteRight (a : 𝓕.CrAnAlgebra) : FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := Quotient.lift (ι.toLinearMap ∘ₗ CrAnAlgebra.superCommute a) (ι_superCommute_eq_of_equiv_right a)
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

lemma superCommuteRight_apply_ι (a b : 𝓕.CrAnAlgebra) : superCommuteRight a (ι b) = ι [a, b]ₛca := by
  rfl

lemma superCommuteRight_apply_quot (a b : 𝓕.CrAnAlgebra) : superCommuteRight a ⟦b⟧= ι [a, b]ₛca := by
  rfl

lemma superCommuteRight_eq_of_equiv (a1 a2 : 𝓕.CrAnAlgebra) (h : a1 ≈ a2) :
    superCommuteRight a1 = superCommuteRight a2 := by
  rw [equiv_iff_sub_mem_ideal] at h
  ext b
  obtain ⟨b, rfl⟩ := ι_surjective b
  have ha1b1 : (superCommuteRight (a1 - a2)) (ι b) = 0 := by
    rw [superCommuteRight_apply_ι]
    apply ι_superCommute_eq_zero_of_ι_left_zero
    exact (ι_eq_zero_iff_mem_ideal (a1 - a2)).mpr h
  simp_all [superCommuteRight_apply_ι]
  trans ι ((superCommute a2) b) + 0
  rw [← ha1b1]
  simp
  simp

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
    simp
    rw [superCommuteRight_apply_quot, superCommuteRight_apply_quot, superCommuteRight_apply_quot]
    simp
  map_smul' c y := by
    obtain ⟨y, rfl⟩ := ι_surjective y
    ext b
    obtain ⟨b, rfl⟩ := ι_surjective b
    rw [← map_smul, ι_apply, ι_apply, ι_apply]
    simp
    rw [superCommuteRight_apply_quot, superCommuteRight_apply_quot]
    simp

lemma ι_superCommute (a b : 𝓕.CrAnAlgebra) : ι [a, b]ₛca = superCommute (ι a) (ι b) := by
  rfl

end FieldOpAlgebra
end FieldSpecification
