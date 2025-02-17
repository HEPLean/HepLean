/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Lorentz.ComplexTensor.PauliMatrices.Basis
/-!

## Contractiong of indices of Pauli matrix.

The main result of this file is `pauliMatrix_contract_pauliMatrix` which states that
`η_{μν} σ^{μ α dot β} σ^{ν α' dot β'} = 2 ε^{αα'} ε^{dot β dot β'}`.

The current way this result is proved is by using tensor tree manipulations.
There is likely a more direct path to this result.

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open TensorTree
open OverColor.Discrete
noncomputable section

namespace complexLorentzTensor
open Fermion

/-- The statement that `ηᵤᵥ σᵘᵃᵇ  σᵛᵃ'ᵇ' = 2 εᵃᵃ' εᵇᵇ'`. -/
theorem pauliCo_contr_pauliContr :
    {pauliCo | ν α β ⊗ pauliContr | ν α' β' = 2 •ₜ εL | α α' ⊗ εR | β β'}ᵀ := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  conv_rhs =>
    rw [TensorTree.perm_tensorBasis_repr_apply]
    rw [TensorTree.smul_tensorBasis_repr]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Fin.succAbove_zero,
      Function.comp_apply, OverColor.mk_hom, OverColor.equivToHomEq_toEquiv, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul]
    rw (transparency := .instances) [TensorTree.prod_tensorBasis_repr_apply]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Fin.succAbove_zero,
      Function.comp_apply, tensorNode_tensor]
    rw [leftMetric_eq_ofRat, rightMetric_eq_ofRat]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, Fin.isValue, Fin.succAbove_zero,
      Function.comp_apply, cons_val_zero, cons_val_one, head_cons, ofRat_tensorBasis_repr_apply]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    erw [PhysLean.RatComplexNum.ofNat_mul_toComplexNum 2]
  rw [TensorTree.contr_tensorBasis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [TensorTree.prod_tensorBasis_repr_apply]
    simp only [pauliCo_ofRat, pauliContr_ofRat]
    simp only [ Fin.isValue, Function.comp_apply,
      tensorNode_tensor, ofRat_tensorBasis_repr_apply, Monoidal.tensorUnit_obj,
      Action.instMonoidalCategory_tensorUnit_V, Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      Functor.comp_obj, Discrete.functor_obj_eq_as, Fin.zero_succAbove, Fin.reduceSucc,
      Fin.cast_eq_self, Nat.cast_ofNat, mul_ite, mul_neg, mul_one, mul_zero]
    left
    rw (transparency := .instances) [ofRat_tensorBasis_repr_apply]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    right
    rw (transparency := .instances) [contr_basis_ratComplexNum]
  conv_lhs =>
    enter [2, x]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

end complexLorentzTensor
