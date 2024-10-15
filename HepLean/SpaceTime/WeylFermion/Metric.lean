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

# Metrics of Weyl fermions

We define the metrics for Weyl fermions, often denoted `ε` in the literature.
These allow us to go from left-handed to alt-left-handed Weyl fermions and back,
and  from right-handed to alt-right-handed Weyl fermions and back.

-/

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

def metricRaw : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

lemma comm_metricRaw (M : SL(2,ℂ)) : M.1 * metricRaw = metricRaw * (M.1⁻¹)ᵀ := by
  rw [metricRaw]
  rw [SpaceTime.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
  simp only [Fin.isValue, mul_zero, mul_neg, mul_one, zero_add, add_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, head_fin_const, head_cons,
    cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, zero_smul, tail_cons, one_smul,
    empty_vecMul, neg_smul, neg_cons, neg_neg, neg_empty, empty_mul, Equiv.symm_apply_apply]

lemma metricRaw_comm (M : SL(2,ℂ)) : metricRaw * M.1 = (M.1⁻¹)ᵀ * metricRaw := by
  rw [metricRaw]
  rw [SpaceTime.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
  simp only [Fin.isValue, zero_mul, one_mul, zero_add, neg_mul, add_zero, transpose_apply, of_apply,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, head_fin_const, head_cons,
    cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, smul_cons, smul_eq_mul, mul_zero,
    mul_one, smul_empty, tail_cons, neg_smul, mul_neg, neg_cons, neg_neg, neg_zero, neg_empty,
    empty_vecMul, add_cons, empty_add_empty, empty_mul, Equiv.symm_apply_apply]

lemma star_comm_metricRaw  (M : SL(2,ℂ)) : M.1.map star * metricRaw = metricRaw * ((M.1)⁻¹)ᴴ := by
  rw [metricRaw]
  rw [SpaceTime.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
  simp

lemma metricRaw_comm_star (M : SL(2,ℂ)) : metricRaw * M.1.map star = ((M.1)⁻¹)ᴴ * metricRaw := by
  rw [metricRaw]
  rw [SpaceTime.SL2C.inverse_coe, eta_fin_two M.1]
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
  simp

/-- The metric `εₐₐ` as an element of `(leftHanded ⊗ leftHanded).V`. -/
def leftMetricVal : (leftHanded ⊗ leftHanded).V :=
  leftLeftToMatrix.symm (- metricRaw)

/-- The metric `εₐₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ leftHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def leftMetric : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ leftHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • leftMetricVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp
    let x' : ℂ := x
    change x' • leftMetricVal =
      (TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M)) (x' • leftMetricVal)
    simp
    apply congrArg
    simp [leftMetricVal]
    erw [leftLeftToMatrix_ρ_symm]
    apply congrArg
    rw [comm_metricRaw, mul_assoc, ← @transpose_mul]
    simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
      not_false_eq_true, mul_nonsing_inv, transpose_one, mul_one]

/-- The metric `εᵃᵃ` as an element of `(altLeftHanded ⊗ altLeftHanded).V`. -/
def altLeftMetricVal : (altLeftHanded ⊗ altLeftHanded).V :=
  altLeftaltLeftToMatrix.symm metricRaw

/-- The metric `εᵃᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ altLeftHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def altLeftMetric : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ altLeftHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • altLeftMetricVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp
    let x' : ℂ := x
    change x' • altLeftMetricVal =
      (TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M)) (x' • altLeftMetricVal)
    simp
    apply congrArg
    simp [altLeftMetricVal]
    erw [altLeftaltLeftToMatrix_ρ_symm]
    apply congrArg
    rw [← metricRaw_comm, mul_assoc]
    simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
      not_false_eq_true, mul_nonsing_inv, mul_one]


/-- The metric `ε_{dot a}_{dot a}` as an element of `(rightHanded ⊗ rightHanded).V`. -/
def rightMetricVal : (rightHanded ⊗ rightHanded).V :=
  rightRightToMatrix.symm (- metricRaw)

/-- The metric `ε_{dot a}_{dot a}` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ rightHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def rightMetric : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ rightHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • rightMetricVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp
    let x' : ℂ := x
    change x' • rightMetricVal =
      (TensorProduct.map (rightHanded.ρ M) (rightHanded.ρ M)) (x' • rightMetricVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, rightMetricVal, map_neg, neg_inj]
    trans rightRightToMatrix.symm ((M.1).map star * metricRaw * ((M.1).map star)ᵀ)
    · apply congrArg
      rw [star_comm_metricRaw, mul_assoc]
      have h1 : ((M.1)⁻¹ᴴ * ((M.1).map star)ᵀ) = 1 := by
        trans (M.1)⁻¹ᴴ * ((M.1))ᴴ
        · rfl
        rw [← @conjTranspose_mul]
        simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
          not_false_eq_true, mul_nonsing_inv, conjTranspose_one]
      rw [h1]
      simp
    · rw [← rightRightToMatrix_ρ_symm metricRaw M]
      rfl

/-- The metric `ε^{dot a}^{dot a}` as an element of `(altRightHanded ⊗ altRightHanded).V`. -/
def altRightMetricVal : (altRightHanded ⊗ altRightHanded).V :=
  altRightAltRightToMatrix.symm (metricRaw)

/-- The metric `ε^{dot a}^{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ altRightHanded`,
  making manifest its invariance under the action of `SL(2,ℂ)`. -/
def altRightMetric : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ altRightHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • altRightMetricVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp
    let x' : ℂ := x
    change x' • altRightMetricVal =
      (TensorProduct.map (altRightHanded.ρ M) (altRightHanded.ρ M)) (x' • altRightMetricVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V]
    trans altRightAltRightToMatrix.symm
      (((M.1)⁻¹).conjTranspose * metricRaw * (((M.1)⁻¹).conjTranspose)ᵀ)
    · rw [altRightMetricVal]
      apply congrArg
      rw [← metricRaw_comm_star, mul_assoc]
      have h1 : ((M.1).map star * (M.1)⁻¹ᴴᵀ) = 1 := by
        refine transpose_eq_one.mp ?_
        rw [@transpose_mul]
        simp
        change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
        rw [← @conjTranspose_mul]
        simp
      rw [h1, mul_one]
    · rw [← altRightAltRightToMatrix_ρ_symm metricRaw M]
      rfl

end
end Fermion
