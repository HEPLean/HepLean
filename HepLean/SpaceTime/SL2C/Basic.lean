/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup.Basic
import Mathlib.RepresentationTheory.Basic
import HepLean.SpaceTime.LorentzVector.AsSelfAdjointMatrix
import HepLean.SpaceTime.LorentzGroup.Restricted
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

/-- The representation of `SL(2, ℂ)` on `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` given by
  `M A ↦ M * A * Mᴴ`. -/
@[simps!]
def repSelfAdjointMatrix : Representation ℝ SL(2, ℂ) $ selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun := toLinearMapSelfAdjointMatrix
  map_one' := by
    noncomm_ring [toLinearMapSelfAdjointMatrix, SpecialLinearGroup.coe_one, one_mul,
      conjTranspose_one, mul_one, Subtype.coe_eta]
  map_mul' M N := by
    ext x i j : 3
    noncomm_ring [toLinearMapSelfAdjointMatrix, SpecialLinearGroup.coe_mul, mul_assoc,
      conjTranspose_mul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply]

/-- The representation of `SL(2, ℂ)` on `spaceTime` obtained from `toSelfAdjointMatrix` and
  `repSelfAdjointMatrix`. -/
def repLorentzVector : Representation ℝ SL(2, ℂ) (LorentzVector 3) where
  toFun M := toSelfAdjointMatrix.symm.comp ((repSelfAdjointMatrix M).comp
    toSelfAdjointMatrix.toLinearMap)
  map_one' := by
    ext
    simp
  map_mul' M N := by
    ext x : 3
    simp

/-!

## Homomorphism to the Lorentz group

There is a group homomorphism from `SL(2, ℂ)` to the Lorentz group `𝓛`.
The purpose of this section is to define this homomorphism.
In the next section we will restrict this homomorphism to the restricted Lorentz group.

-/

lemma iff_det_selfAdjoint (Λ : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) : Λ ∈ LorentzGroup 3 ↔
    ∀ (x : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)),
    det ((toSelfAdjointMatrix ∘
    toLin LorentzVector.stdBasis LorentzVector.stdBasis Λ ∘ toSelfAdjointMatrix.symm) x).1
    = det x.1 := by
  rw [LorentzGroup.mem_iff_norm]
  refine Iff.intro (fun h x => ?_) (fun h x => ?_)
  · simpa [← det_eq_ηLin] using congrArg ofReal $ h (toSelfAdjointMatrix.symm x)
  · simpa [det_eq_ηLin] using h (toSelfAdjointMatrix x)

/-- Given an element `M ∈ SL(2, ℂ)` the corresponding element of the Lorentz group. -/
@[simps!]
def toLorentzGroupElem (M : SL(2, ℂ)) : LorentzGroup 3 :=
  ⟨LinearMap.toMatrix LorentzVector.stdBasis LorentzVector.stdBasis (repLorentzVector M),
    by simp [repLorentzVector, iff_det_selfAdjoint]⟩

/-- The group homomorphism from ` SL(2, ℂ)` to the Lorentz group `𝓛`. -/
@[simps!]
def toLorentzGroup : SL(2, ℂ) →* LorentzGroup 3 where
  toFun := toLorentzGroupElem
  map_one' := by
    simp only [toLorentzGroupElem, _root_.map_one, LinearMap.toMatrix_one]
    rfl
  map_mul' M N := by
    apply Subtype.eq
    simp only [toLorentzGroupElem, _root_.map_mul, LinearMap.toMatrix_mul,
      lorentzGroupIsGroup_mul_coe]

/-!

## Homomorphism to the restricted Lorentz group

The homomorphism `toLorentzGroup` restricts to a homomorphism to the restricted Lorentz group.
In this section we will define this homomorphism.

-/

informal_lemma toLorentzGroup_det_one where
  math :≈ "The determinant of the image of `SL(2, ℂ)` in the Lorentz group is one."
  deps :≈ [``toLorentzGroup]

informal_lemma toLorentzGroup_timeComp_nonneg where
  math :≈ "The time coponent of the image of `SL(2, ℂ)` in the Lorentz group is non-negative."
  deps :≈ [``toLorentzGroup, ``LorentzGroup.timeComp]

informal_lemma toRestrictedLorentzGroup where
  math :≈ "The homomorphism from `SL(2, ℂ)` to the restricted Lorentz group."
  deps :≈ [``toLorentzGroup, ``toLorentzGroup_det_one, ``toLorentzGroup_timeComp_nonneg,
    ``LorentzGroup.Restricted]

/-! TODO: Define homomorphism from `SL(2, ℂ)` to the restricted Lorentz group. -/
end
end SL2C

end SpaceTime
