/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.Group.Basic
import HepLean.SpaceTime.LorentzVector.Real.Basic
import Mathlib.RepresentationTheory.Basic
import HepLean.Lorentz.Group.Restricted
import HepLean.SpaceTime.PauliMatrices.SelfAdjoint
import HepLean.Meta.Informal
/-!
# The group SL(2, ℂ) and it's relation to the Lorentz group

The aim of this file is to give the relationship between `SL(2, ℂ)` and the Lorentz group.

-/
namespace SpaceTime

open Matrix
open MatrixGroups
open Complex

namespace SL2C

open SpaceTime

noncomputable section

/-!

## Some basic properties about SL(2, ℂ)

Possibly to be moved to mathlib at some point.
-/

lemma inverse_coe (M : SL(2, ℂ)) : M.1⁻¹ = (M⁻¹).1 := by
  apply Matrix.inv_inj
  simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true,
    nonsing_inv_nonsing_inv, SpecialLinearGroup.coe_inv]
  have h1 : IsUnit M.1.det := by
    simp
  rw [Matrix.inv_adjugate M.1 h1]
  · simp
  · simp

lemma transpose_coe (M : SL(2, ℂ)) : M.1ᵀ = (M.transpose).1 := rfl
/-!

## Representation of SL(2, ℂ) on spacetime

Through the correspondence between spacetime and self-adjoint matrices,
we can define a representation a representation of `SL(2, ℂ)` on spacetime.

-/

/-- Given an element `M ∈ SL(2, ℂ)` the linear map from `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` to
  itself defined by `A ↦ M * A * Mᴴ`. -/
@[simps!]
def toLinearMapSelfAdjointMatrix (M : SL(2, ℂ)) :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun A := ⟨M.1 * A.1 * Matrix.conjTranspose M,
    by
      noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
        conjTranspose_mul, conjTranspose_conjTranspose,
        (star_eq_conjTranspose A.1).symm.trans $ selfAdjoint.mem_iff.mp A.2]⟩
  map_add' A B := by
    simp only [AddSubgroup.coe_add, AddMemClass.mk_add_mk, Subtype.mk.injEq]
    noncomm_ring [AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid, AddSubmonoid.mk_add_mk,
      Subtype.mk.injEq]
  map_smul' r A := by
    noncomm_ring [selfAdjoint.val_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      RingHom.id_apply]

lemma toLinearMapSelfAdjointMatrix_det (M : SL(2, ℂ)) (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    det ((toLinearMapSelfAdjointMatrix M) A).1 = det A.1 := by
  simp only [LinearMap.coe_mk, AddHom.coe_mk, toLinearMapSelfAdjointMatrix, det_mul,
    selfAdjoint.mem_iff, det_conjTranspose, det_mul, det_one, RingHom.id_apply]
  simp only [SpecialLinearGroup.det_coe, one_mul, star_one, mul_one]

def toMatrix : SL(2, ℂ) →* Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ where
  toFun M := LinearMap.toMatrix PauliMatrix.σSAL PauliMatrix.σSAL (toLinearMapSelfAdjointMatrix M)
  map_one' := by
    simp only [toLinearMapSelfAdjointMatrix, SpecialLinearGroup.coe_one, one_mul, conjTranspose_one,
      mul_one, Subtype.coe_eta]
    erw [LinearMap.toMatrix_one]
  map_mul' M N := by
    simp only
    rw [← LinearMap.toMatrix_mul]
    apply congrArg
    ext1 x
    simp only [toLinearMapSelfAdjointMatrix, SpecialLinearGroup.coe_mul, conjTranspose_mul,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply, Subtype.mk.injEq]
    noncomm_ring

open Lorentz in
lemma toMatrix_apply_contrMod (M : SL(2, ℂ)) (v : ContrMod 3) :
    (toMatrix M) *ᵥ v = ContrMod.toSelfAdjoint.symm
    ((toLinearMapSelfAdjointMatrix M) (ContrMod.toSelfAdjoint v)) := by
  simp [toMatrix, LinearMap.toMatrix_apply, ContrMod.mulVec]
  obtain ⟨a, ha⟩ := ContrMod.toSelfAdjoint.symm.surjective v
  subst ha
  rw [LinearEquiv.apply_symm_apply]
  simp [ContrMod.toSelfAdjoint]
  change  ContrMod.toFin1dℝEquiv.symm ((
      ((LinearMap.toMatrix PauliMatrix.σSAL PauliMatrix.σSAL) (toLinearMapSelfAdjointMatrix M)))
     *ᵥ (((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 1 ⊕ Fin 3)) (PauliMatrix.σSAL.repr a)))) = _
  apply congrArg
  erw [LinearMap.toMatrix_mulVec_repr]
  rfl

lemma toMatrix_mem_lorentzGroup (M : SL(2, ℂ)) : toMatrix M ∈ LorentzGroup 3 := by
  rw [LorentzGroup.mem_iff_norm]
  intro x
  apply ofReal_injective
  rw [Lorentz.contrContrContractField.same_eq_det_toSelfAdjoint]
  rw [toMatrix_apply_contrMod]
  rw [LinearEquiv.apply_symm_apply]
  rw [toLinearMapSelfAdjointMatrix_det]
  rw [Lorentz.contrContrContractField.same_eq_det_toSelfAdjoint]

/-- The group homomorphism from `SL(2, ℂ)` to the Lorentz group `𝓛`. -/
@[simps!]
def toLorentzGroup : SL(2, ℂ) →* LorentzGroup 3 where
  toFun M := ⟨toMatrix M, toMatrix_mem_lorentzGroup M⟩
  map_one' := by
    simp only [_root_.map_one]
    rfl
  map_mul' M N := by
    ext1
    simp only [_root_.map_mul, lorentzGroupIsGroup_mul_coe]


lemma toLorentzGroup_eq_σSAL (M : SL(2, ℂ)) :
    toLorentzGroup M = LinearMap.toMatrix
    PauliMatrix.σSAL PauliMatrix.σSAL (toLinearMapSelfAdjointMatrix M) := by
  rfl


lemma toLinearMapSelfAdjointMatrix_basis (i : Fin 1 ⊕ Fin 3) :
    toLinearMapSelfAdjointMatrix M (PauliMatrix.σSAL i) =
    ∑ j, (toLorentzGroup M).1 j i •
    PauliMatrix.σSAL j := by
  rw [toLorentzGroup_eq_σSAL]
  simp only [LinearMap.toMatrix_apply, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
  nth_rewrite 1 [← (Basis.sum_repr PauliMatrix.σSAL
    ((toLinearMapSelfAdjointMatrix M) (PauliMatrix.σSAL i)))]
  rfl

lemma toLinearMapSelfAdjointMatrix_σSA (i : Fin 1 ⊕ Fin 3) :
    toLinearMapSelfAdjointMatrix M (PauliMatrix.σSA i) =
    ∑ j, (toLorentzGroup M⁻¹).1 i j • PauliMatrix.σSA j := by
  have h1 : (toLorentzGroup M⁻¹).1 = minkowskiMatrix.dual (toLorentzGroup M).1 := by
    simp
  simp only [h1]
  rw [PauliMatrix.σSA_minkowskiMetric_σSAL, _root_.map_smul]
  rw [toLinearMapSelfAdjointMatrix_basis]
  rw [Finset.smul_sum]
  apply congrArg
  funext j
  rw [smul_smul, PauliMatrix.σSA_minkowskiMetric_σSAL, smul_smul]
  apply congrFun
  apply congrArg
  exact Eq.symm (minkowskiMatrix.dual_apply_minkowskiMatrix ((toLorentzGroup M).1) i j)

/-!

## Homomorphism to the restricted Lorentz group

The homomorphism `toLorentzGroup` restricts to a homomorphism to the restricted Lorentz group.
In this section we will define this homomorphism.

-/

informal_lemma toLorentzGroup_det_one where
  math :≈ "The determinant of the image of `SL(2, ℂ)` in the Lorentz group is one."
  deps :≈ [``toLorentzGroup]

informal_lemma toLorentzGroup_inl_inl_nonneg where
  math :≈ "The time coponent of the image of `SL(2, ℂ)` in the Lorentz group is non-negative."
  deps :≈ [``toLorentzGroup]

informal_lemma toRestrictedLorentzGroup where
  math :≈ "The homomorphism from `SL(2, ℂ)` to the restricted Lorentz group."
  deps :≈ [``toLorentzGroup, ``toLorentzGroup_det_one, ``toLorentzGroup_inl_inl_nonneg,
    ``LorentzGroup.Restricted]

/-! TODO: Define homomorphism from `SL(2, ℂ)` to the restricted Lorentz group. -/
end
end SL2C

end SpaceTime
