/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.WeylFermion.Basic
import HepLean.SpaceTime.WeylFermion.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import HepLean.SpaceTime.WeylFermion.Two
/-!

# Units of Weyl fermions

We define the units for Weyl fermions, often denoted `δ` in the literature.

-/

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-- The left-alt-left unit `δₐᵃ` as an element of `(leftHanded ⊗ altLeftHanded).V`. -/
def leftAltLeftUnitVal : (leftHanded ⊗ altLeftHanded).V :=
  leftAltLeftToMatrix.symm 1

/-- The left-alt-left unit `δₐᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ altLeftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def leftAltLeftUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ altLeftHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • leftAltLeftUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • leftAltLeftUnitVal =
      (TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M)) (x' • leftAltLeftUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, leftAltLeftUnitVal]
    erw [leftAltLeftToMatrix_ρ_symm]
    apply congrArg
    simp

/-- The alt-left-left unit `δᵃₐ` as an element of `(altLeftHanded ⊗ leftHanded).V`. -/
def altLeftLeftUnitVal : (altLeftHanded ⊗ leftHanded).V :=
  altLeftLeftToMatrix.symm 1

/-- The alt-left-left unit `δᵃₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ leftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def altLeftLeftUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ leftHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • altLeftLeftUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • altLeftLeftUnitVal =
      (TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M)) (x' • altLeftLeftUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp [altLeftLeftUnitVal]
    erw [altLeftLeftToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, ← transpose_mul, SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq,
      one_ne_zero, not_false_eq_true, mul_nonsing_inv, transpose_one]

/-- The right-alt-right unit `δ_{dot a}^{dot a}` as an element of
  `(rightHanded ⊗ altRightHanded).V`. -/
def rightAltRightUnitVal : (rightHanded ⊗ altRightHanded).V :=
  rightAltRightToMatrix.symm 1

/-- The right-alt-right unit `δ_{dot a}^{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ altRightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def rightAltRightUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ altRightHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • rightAltRightUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • rightAltRightUnitVal =
      (TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M)) (x' • rightAltRightUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, rightAltRightUnitVal]
    erw [rightAltRightToMatrix_ρ_symm]
    apply congrArg
    simp only [RCLike.star_def, mul_one]
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp only [transpose_mul, transpose_transpose]
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

/-- The alt-right-right unit `δ^{dot a}_{dot a}` as an element of
  `(rightHanded ⊗ altRightHanded).V`. -/
def altRightRightUnitVal : (altRightHanded ⊗ rightHanded).V :=
  altRightRightToMatrix.symm 1

/-- The alt-right-right unit `δ^{dot a}_{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ rightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def altRightRightUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ rightHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • altRightRightUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • altRightRightUnitVal =
      (TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M)) (x' • altRightRightUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp [altRightRightUnitVal]
    erw [altRightRightToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, RCLike.star_def]
    symm
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

end
end Fermion
