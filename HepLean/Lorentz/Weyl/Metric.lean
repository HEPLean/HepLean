/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.Weyl.Basic
import HepLean.Lorentz.Weyl.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import HepLean.Lorentz.Weyl.Two
import HepLean.Lorentz.Weyl.Unit
/-!

# Metrics of Weyl fermions

We define the metrics for Weyl fermions, often denoted `ε` in the literature.
These allow us to go from left-handed to alt-left-handed Weyl fermions and back,
and from right-handed to alt-right-handed Weyl fermions and back.

-/

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-- The raw `2x2` matrix corresponding to the metric for fermions. -/
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

lemma star_comm_metricRaw (M : SL(2,ℂ)) : M.1.map star * metricRaw = metricRaw * ((M.1)⁻¹)ᴴ := by
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

/-- The metric `εᵃᵃ` as an element of `(leftHanded ⊗ leftHanded).V`. -/
def leftMetricVal : (leftHanded ⊗ leftHanded).V :=
  leftLeftToMatrix.symm (- metricRaw)

/-- Expansion of `leftMetricVal` into the left basis. -/
lemma leftMetricVal_expand_tmul : leftMetricVal =
    - leftBasis 0 ⊗ₜ[ℂ] leftBasis 1 + leftBasis 1 ⊗ₜ[ℂ] leftBasis 0 := by
  simp only [Action.instMonoidalCategory_tensorObj_V, leftMetricVal, Fin.isValue]
  erw [leftLeftToMatrix_symm_expand_tmul]
  simp only [metricRaw, neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one, neg_smul,
    Finset.sum_neg_distrib, Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, head_cons,
    neg_add_rev, one_smul, zero_smul, neg_zero, add_zero, head_fin_const, neg_neg, zero_add]

/-- The metric `εᵃᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ leftHanded`,
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
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • leftMetricVal =
      (TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M)) (x' • leftMetricVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, leftMetricVal, map_neg, neg_inj]
    erw [leftLeftToMatrix_ρ_symm]
    apply congrArg
    rw [comm_metricRaw, mul_assoc, ← @transpose_mul]
    simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
      not_false_eq_true, mul_nonsing_inv, transpose_one, mul_one]

lemma leftMetric_apply_one : leftMetric.hom (1 : ℂ) = leftMetricVal := by
  change leftMetric.hom.toFun (1 : ℂ) = leftMetricVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    leftMetric, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

/-- The metric `εₐₐ` as an element of `(altLeftHanded ⊗ altLeftHanded).V`. -/
def altLeftMetricVal : (altLeftHanded ⊗ altLeftHanded).V :=
  altLeftaltLeftToMatrix.symm metricRaw

/-- Expansion of `altLeftMetricVal` into the left basis. -/
lemma altLeftMetricVal_expand_tmul : altLeftMetricVal =
    altLeftBasis 0 ⊗ₜ[ℂ] altLeftBasis 1 - altLeftBasis 1 ⊗ₜ[ℂ] altLeftBasis 0 := by
  simp only [Action.instMonoidalCategory_tensorObj_V, altLeftMetricVal, Fin.isValue]
  erw [altLeftaltLeftToMatrix_symm_expand_tmul]
  simp only [metricRaw, neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one, neg_smul,
    Finset.sum_neg_distrib, Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, head_cons,
    neg_add_rev, one_smul, zero_smul, neg_zero, add_zero, head_fin_const, neg_neg, zero_add]
  rfl

/-- The metric `εₐₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ altLeftHanded`,
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
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • altLeftMetricVal =
      (TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M)) (x' • altLeftMetricVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, altLeftMetricVal]
    erw [altLeftaltLeftToMatrix_ρ_symm]
    apply congrArg
    rw [← metricRaw_comm, mul_assoc]
    simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
      not_false_eq_true, mul_nonsing_inv, mul_one]

lemma altLeftMetric_apply_one : altLeftMetric.hom (1 : ℂ) = altLeftMetricVal := by
  change altLeftMetric.hom.toFun (1 : ℂ) = altLeftMetricVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    altLeftMetric, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

/-- The metric `ε^{dot a}^{dot a}` as an element of `(rightHanded ⊗ rightHanded).V`. -/
def rightMetricVal : (rightHanded ⊗ rightHanded).V :=
  rightRightToMatrix.symm (- metricRaw)

/-- Expansion of `rightMetricVal` into the left basis. -/
lemma rightMetricVal_expand_tmul : rightMetricVal =
    - rightBasis 0 ⊗ₜ[ℂ] rightBasis 1 + rightBasis 1 ⊗ₜ[ℂ] rightBasis 0 := by
  simp only [Action.instMonoidalCategory_tensorObj_V, rightMetricVal, Fin.isValue]
  erw [rightRightToMatrix_symm_expand_tmul]
  simp only [metricRaw, neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one, neg_smul,
    Finset.sum_neg_distrib, Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, head_cons,
    neg_add_rev, one_smul, zero_smul, neg_zero, add_zero, head_fin_const, neg_neg, zero_add]

/-- The metric `ε^{dot a}^{dot a}` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ rightHanded`,
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
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
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

lemma rightMetric_apply_one : rightMetric.hom (1 : ℂ) = rightMetricVal := by
  change rightMetric.hom.toFun (1 : ℂ) = rightMetricVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    rightMetric, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

/-- The metric `ε_{dot a}_{dot a}` as an element of `(altRightHanded ⊗ altRightHanded).V`. -/
def altRightMetricVal : (altRightHanded ⊗ altRightHanded).V :=
  altRightAltRightToMatrix.symm (metricRaw)

/-- Expansion of `rightMetricVal` into the left basis. -/
lemma altRightMetricVal_expand_tmul : altRightMetricVal =
    altRightBasis 0 ⊗ₜ[ℂ] altRightBasis 1 - altRightBasis 1 ⊗ₜ[ℂ] altRightBasis 0 := by
  simp only [Action.instMonoidalCategory_tensorObj_V, altRightMetricVal, Fin.isValue]
  erw [altRightAltRightToMatrix_symm_expand_tmul]
  simp only [metricRaw, neg_apply, of_apply, cons_val', empty_val', cons_val_fin_one, neg_smul,
    Finset.sum_neg_distrib, Fin.sum_univ_two, Fin.isValue, cons_val_zero, cons_val_one, head_cons,
    neg_add_rev, one_smul, zero_smul, neg_zero, add_zero, head_fin_const, neg_neg, zero_add]
  rfl

/-- The metric `ε_{dot a}_{dot a}` as a morphism
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
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
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
        simp only [transpose_transpose, RCLike.star_def]
        change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
        rw [← @conjTranspose_mul]
        simp
      rw [h1, mul_one]
    · rw [← altRightAltRightToMatrix_ρ_symm metricRaw M]
      rfl

lemma altRightMetric_apply_one : altRightMetric.hom (1 : ℂ) = altRightMetricVal := by
  change altRightMetric.hom.toFun (1 : ℂ) = altRightMetricVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    altRightMetric, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

/-!

## Contraction of metrics

-/

lemma leftAltContraction_apply_metric : (β_ leftHanded altLeftHanded).hom.hom
    ((leftHanded.V ◁ (λ_ altLeftHanded.V).hom)
    ((leftHanded.V ◁ leftAltContraction.hom ▷ altLeftHanded.V)
    ((leftHanded.V ◁ (α_ leftHanded.V altLeftHanded.V altLeftHanded.V).inv)
    ((α_ leftHanded.V leftHanded.V (altLeftHanded.V ⊗ altLeftHanded.V)).hom
    (leftMetric.hom (1 : ℂ) ⊗ₜ[ℂ] altLeftMetric.hom (1 : ℂ)))))) =
    altLeftLeftUnit.hom (1 : ℂ) := by
  rw [leftMetric_apply_one, altLeftMetric_apply_one]
  rw [leftMetricVal_expand_tmul, altLeftMetricVal_expand_tmul]
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Fin.isValue, tmul_sub, add_tmul, neg_tmul, map_sub, map_add, map_neg]
  have h1 (x1 x2 : leftHanded) (y1 y2 :altLeftHanded) :
    (leftHanded.V ◁ (λ_ altLeftHanded.V).hom)
    ((leftHanded.V ◁ leftAltContraction.hom ▷ altLeftHanded.V) (((leftHanded.V ◁
    (α_ leftHanded.V altLeftHanded.V altLeftHanded.V).inv)
    ((α_ leftHanded.V leftHanded.V (altLeftHanded.V ⊗ altLeftHanded.V)).hom
    ((x1 ⊗ₜ[ℂ] x2) ⊗ₜ[ℂ] y1 ⊗ₜ[ℂ] y2)))))
      = x1 ⊗ₜ[ℂ] ((λ_ altLeftHanded.V).hom ((leftAltContraction.hom (x2 ⊗ₜ[ℂ] y1)) ⊗ₜ[ℂ] y2)) := rfl
  repeat rw (config := { transparency := .instances }) [h1]
  repeat rw [leftAltContraction_basis]
  simp only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero, ↓reduceIte, zero_tmul, map_zero,
    tmul_zero, neg_zero, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul, zero_add,
    zero_ne_one, add_zero, sub_neg_eq_add]
  erw [altLeftLeftUnit_apply_one, altLeftLeftUnitVal_expand_tmul]
  rw [add_comm]
  rfl

lemma altLeftContraction_apply_metric : (β_ altLeftHanded leftHanded).hom.hom
    ((altLeftHanded.V ◁ (λ_ leftHanded.V).hom)
    ((altLeftHanded.V ◁ altLeftContraction.hom ▷ leftHanded.V)
    ((altLeftHanded.V ◁ (α_ altLeftHanded.V leftHanded.V leftHanded.V).inv)
    ((α_ altLeftHanded.V altLeftHanded.V (leftHanded.V ⊗ leftHanded.V)).hom
    (altLeftMetric.hom (1 : ℂ) ⊗ₜ[ℂ] leftMetric.hom (1 : ℂ)))))) =
    leftAltLeftUnit.hom (1 : ℂ) := by
  rw [leftMetric_apply_one, altLeftMetric_apply_one]
  rw [leftMetricVal_expand_tmul, altLeftMetricVal_expand_tmul]
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Fin.isValue, tmul_add, tmul_neg, sub_tmul, map_add, map_neg, map_sub]
  have h1 (x1 x2 : altLeftHanded) (y1 y2 : leftHanded) :
    (altLeftHanded.V ◁ (λ_ leftHanded.V).hom)
    ((altLeftHanded.V ◁ altLeftContraction.hom ▷ leftHanded.V) (((altLeftHanded.V ◁
    (α_ altLeftHanded.V leftHanded.V leftHanded.V).inv)
    ((α_ altLeftHanded.V altLeftHanded.V (leftHanded.V ⊗ leftHanded.V)).hom
    ((x1 ⊗ₜ[ℂ] x2) ⊗ₜ[ℂ] y1 ⊗ₜ[ℂ] y2)))))
      = x1 ⊗ₜ[ℂ] ((λ_ leftHanded.V).hom ((altLeftContraction.hom (x2 ⊗ₜ[ℂ] y1)) ⊗ₜ[ℂ] y2)) := rfl
  repeat rw (config := { transparency := .instances }) [h1]
  repeat rw [altLeftContraction_basis]
  simp only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero, ↓reduceIte, zero_tmul, map_zero,
    tmul_zero, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul, zero_sub, neg_neg,
    zero_ne_one, sub_zero]
  erw [leftAltLeftUnit_apply_one, leftAltLeftUnitVal_expand_tmul]
  rw [add_comm]
  rfl

lemma rightAltContraction_apply_metric : (β_ rightHanded altRightHanded).hom.hom
    ((rightHanded.V ◁ (λ_ altRightHanded.V).hom)
    ((rightHanded.V ◁ rightAltContraction.hom ▷ altRightHanded.V)
    ((rightHanded.V ◁ (α_ rightHanded.V altRightHanded.V altRightHanded.V).inv)
    ((α_ rightHanded.V rightHanded.V (altRightHanded.V ⊗ altRightHanded.V)).hom
    (rightMetric.hom (1 : ℂ) ⊗ₜ[ℂ] altRightMetric.hom (1 : ℂ)))))) =
    altRightRightUnit.hom (1 : ℂ) := by
  rw [rightMetric_apply_one, altRightMetric_apply_one]
  rw [rightMetricVal_expand_tmul, altRightMetricVal_expand_tmul]
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Fin.isValue, tmul_sub, add_tmul, neg_tmul, map_sub, map_add, map_neg]
  have h1 (x1 x2 : rightHanded) (y1 y2 : altRightHanded) :
    (rightHanded.V ◁ (λ_ altRightHanded.V).hom)
    ((rightHanded.V ◁ rightAltContraction.hom ▷ altRightHanded.V) (((rightHanded.V ◁
    (α_ rightHanded.V altRightHanded.V altRightHanded.V).inv)
    ((α_ rightHanded.V rightHanded.V (altRightHanded.V ⊗ altRightHanded.V)).hom
    ((x1 ⊗ₜ[ℂ] x2) ⊗ₜ[ℂ] y1 ⊗ₜ[ℂ] y2))))) = x1 ⊗ₜ[ℂ] ((λ_ altRightHanded.V).hom
    ((rightAltContraction.hom (x2 ⊗ₜ[ℂ] y1)) ⊗ₜ[ℂ] y2)) := rfl
  repeat rw (config := { transparency := .instances }) [h1]
  repeat rw [rightAltContraction_basis]
  simp only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero, ↓reduceIte, zero_tmul, map_zero,
    tmul_zero, neg_zero, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul, zero_add,
    zero_ne_one, add_zero, sub_neg_eq_add]
  erw [altRightRightUnit_apply_one, altRightRightUnitVal_expand_tmul]
  rw [add_comm]
  rfl

lemma altRightContraction_apply_metric : (β_ altRightHanded rightHanded).hom.hom
    ((altRightHanded.V ◁ (λ_ rightHanded.V).hom)
    ((altRightHanded.V ◁ altRightContraction.hom ▷ rightHanded.V)
    ((altRightHanded.V ◁ (α_ altRightHanded.V rightHanded.V rightHanded.V).inv)
    ((α_ altRightHanded.V altRightHanded.V (rightHanded.V ⊗ rightHanded.V)).hom
    (altRightMetric.hom (1 : ℂ) ⊗ₜ[ℂ] rightMetric.hom (1 : ℂ)))))) =
    rightAltRightUnit.hom (1 : ℂ) := by
  rw [rightMetric_apply_one, altRightMetric_apply_one]
  rw [rightMetricVal_expand_tmul, altRightMetricVal_expand_tmul]
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Fin.isValue, tmul_add, tmul_neg, sub_tmul, map_add, map_neg, map_sub]
  have h1 (x1 x2 : altRightHanded) (y1 y2 : rightHanded) :
    (altRightHanded.V ◁ (λ_ rightHanded.V).hom)
    ((altRightHanded.V ◁ altRightContraction.hom ▷ rightHanded.V) (((altRightHanded.V ◁
    (α_ altRightHanded.V rightHanded.V rightHanded.V).inv)
    ((α_ altRightHanded.V altRightHanded.V (rightHanded.V ⊗ rightHanded.V)).hom
    ((x1 ⊗ₜ[ℂ] x2) ⊗ₜ[ℂ] y1 ⊗ₜ[ℂ] y2)))))
      = x1 ⊗ₜ[ℂ] ((λ_ rightHanded.V).hom ((altRightContraction.hom (x2 ⊗ₜ[ℂ] y1)) ⊗ₜ[ℂ] y2)) := rfl
  repeat rw (config := { transparency := .instances }) [h1]
  repeat rw [altRightContraction_basis]
  simp only [Fin.isValue, Fin.val_one, Fin.val_zero, one_ne_zero, ↓reduceIte, zero_tmul, map_zero,
    tmul_zero, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, one_smul, zero_sub, neg_neg,
    zero_ne_one, sub_zero]
  erw [rightAltRightUnit_apply_one, rightAltRightUnitVal_expand_tmul]
  rw [add_comm]
  rfl

end
end Fermion
