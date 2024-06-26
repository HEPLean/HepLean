/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup.Basic
import Mathlib.RepresentationTheory.Basic
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

## Representation of SL(2, ℂ) on spacetime

Through the correspondence between spacetime and self-adjoint matrices,
we can define a representation a representation of `SL(2, ℂ)` on spacetime.

-/

/-- Given an element  `M ∈ SL(2, ℂ)` the linear map from `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` to
 itself defined by  `A ↦ M * A * Mᴴ`. -/
@[simps!]
def toLinearMapSelfAdjointMatrix (M : SL(2, ℂ)) :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun A := ⟨M.1 * A.1 * Matrix.conjTranspose M,
    by
      noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
        conjTranspose_mul, conjTranspose_conjTranspose,
        (star_eq_conjTranspose A.1).symm.trans $ selfAdjoint.mem_iff.mp A.2]⟩
  map_add' A B := by
    noncomm_ring [AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid, AddSubmonoid.mk_add_mk,
      Subtype.mk.injEq]
  map_smul' r A := by
    noncomm_ring [selfAdjoint.val_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      RingHom.id_apply]

/-- The representation of  `SL(2, ℂ)` on `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` given by
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

/-- The representation of  `SL(2, ℂ)` on `spaceTime` obtained from `toSelfAdjointMatrix` and
  `repSelfAdjointMatrix`. -/
def repSpaceTime : Representation ℝ SL(2, ℂ) SpaceTime where
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

/-- Given an element `M ∈ SL(2, ℂ)` the corresponding element of the Lorentz group. -/
@[simps!]
def toLorentzGroupElem (M : SL(2, ℂ)) : 𝓛 :=
  ⟨LinearMap.toMatrix stdBasis stdBasis (repSpaceTime M) ,
   by simp [repSpaceTime, PreservesηLin.iff_det_selfAdjoint]⟩

/-- The group homomorphism from ` SL(2, ℂ)` to the Lorentz group `𝓛`. -/
@[simps!]
def toLorentzGroup : SL(2, ℂ) →* 𝓛 where
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

### TODO

Complete this section.

-/



end
end SL2C

end SpaceTime
