/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Complex.Two
/-!

# Unit for complex Lorentz vectors

-/
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open SpaceTime
open CategoryTheory.MonoidalCategory
namespace Lorentz

/-- The contra-co unit for complex lorentz vectors. Usually denoted `δⁱᵢ`. -/
def contrCoUnitVal : (complexContr ⊗ complexCo).V :=
  contrCoToMatrix.symm 1

/-- Expansion of `contrCoUnitVal` into basis. -/
lemma contrCoUnitVal_expand_tmul : contrCoUnitVal =
    complexContrBasis (Sum.inl 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inl 0)
    + complexContrBasis (Sum.inr 0) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 0)
    + complexContrBasis (Sum.inr 1) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 1)
    + complexContrBasis (Sum.inr 2) ⊗ₜ[ℂ] complexCoBasis (Sum.inr 2) := by
  simp only [Action.instMonoidalCategory_tensorObj_V, contrCoUnitVal, Fin.isValue]
  erw [contrCoToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

/-- The contra-co unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexCo`, manifesting the invaraince under
  the `SL(2, ℂ)` action. -/
def contrCoUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexCo where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • contrCoUnitVal,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • contrCoUnitVal =
      (TensorProduct.map (complexContr.ρ M) (complexCo.ρ M)) (x' • contrCoUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, contrCoUnitVal]
    erw [contrCoToMatrix_ρ_symm]
    apply congrArg
    simp

lemma contrCoUnit_apply_one : contrCoUnit.hom (1 : ℂ) = contrCoUnitVal := by
  change contrCoUnit.hom.toFun (1 : ℂ) = contrCoUnitVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    contrCoUnit, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

/-- The co-contra unit for complex lorentz vectors. Usually denoted `δᵢⁱ`. -/
def coContrUnitVal : (complexCo ⊗ complexContr).V :=
  coContrToMatrix.symm 1

/-- Expansion of `coContrUnitVal` into basis. -/
lemma coContrUnitVal_expand_tmul : coContrUnitVal =
    complexCoBasis (Sum.inl 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inl 0)
    + complexCoBasis (Sum.inr 0) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 0)
    + complexCoBasis (Sum.inr 1) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 1)
    + complexCoBasis (Sum.inr 2) ⊗ₜ[ℂ] complexContrBasis (Sum.inr 2) := by
  simp only [Action.instMonoidalCategory_tensorObj_V, coContrUnitVal, Fin.isValue]
  erw [coContrToMatrix_symm_expand_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, ne_eq, reduceCtorEq, not_false_eq_true, one_apply_ne,
    zero_smul, add_zero, one_apply_eq, one_smul, zero_add, Sum.inr.injEq, zero_ne_one, Fin.reduceEq,
    one_ne_zero]
  rfl

/-- The co-contra unit for complex lorentz vectors as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexContr`, manifesting the invaraince under
  the `SL(2, ℂ)` action. -/
def coContrUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexContr where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • coContrUnitVal,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • coContrUnitVal =
      (TensorProduct.map (complexCo.ρ M) (complexContr.ρ M)) (x' • coContrUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, coContrUnitVal]
    erw [coContrToMatrix_ρ_symm]
    apply congrArg
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp

lemma coContrUnit_apply_one : coContrUnit.hom (1 : ℂ) = coContrUnitVal := by
  change coContrUnit.hom.toFun (1 : ℂ) = coContrUnitVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    coContrUnit, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

end Lorentz
end
