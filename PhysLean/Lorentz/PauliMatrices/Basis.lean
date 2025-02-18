/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Lorentz.PauliMatrices.Basic
/-!

## Pauli matrices and the basis of complex Lorentz tensors

-/
open CategoryTheory
open MonoidalCategory
open Matrix
open Complex
open IndexNotation
open TensorTree
open OverColor.Discrete
noncomputable section

namespace PauliMatrix
open Fermion
open complexLorentzTensor

/-!

## Expanding pauliContr in a basis.

-/
/-- The expansion of the Pauli matrices `σ^μ^a^{dot a}` in terms of basis vectors. -/
lemma pauliContr_in_basis : {pauliContr | μ α β}ᵀ.tensor =
    basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 1 | 2 => 1)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 1 | 2 => 0)
    - I • basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + I • basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 1 | 2 => 0)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 0 | 2 => 0)
    - basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  rw [tensorNode_pauliContr]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constThreeNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [PauliMatrix.asConsTensor_apply_one, PauliMatrix.asTensor_expand]
  simp only [Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Action.instMonoidalCategory_tensorObj_V,
    Fin.isValue, map_sub, map_add, _root_.map_smul]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  all_goals
    erw [tripleIsoSep_tmul, basisVector]
    apply congrArg
    try apply congrArg
    funext i
    match i with
    | (0 : Fin 3) =>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      change _ = Lorentz.complexContrBasisFin4 _
      simp only [Fin.isValue, Lorentz.complexContrBasisFin4, Basis.coe_reindex, Function.comp_apply]
      rfl
    | (1 : Fin 3) => rfl
    | (2 : Fin 3) => rfl

lemma pauliContr_tensorBasis : pauliContr =
    complexLorentzTensor.tensorBasis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + complexLorentzTensor.tensorBasis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => 0 | 1 => 1 | 2 => 1)
    + complexLorentzTensor.tensorBasis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + complexLorentzTensor.tensorBasis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => 1 | 1 => 1 | 2 => 0)
    - I • complexLorentzTensor.tensorBasis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + I • complexLorentzTensor.tensorBasis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => 2 | 1 => 1 | 2 => 0)
    + complexLorentzTensor.tensorBasis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => 3 | 1 => 0 | 2 => 0)
    - complexLorentzTensor.tensorBasis ![Color.up, Color.upL, Color.upR]
      (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  trans {pauliContr | μ α β}ᵀ.tensor
  · simp
  rw [pauliContr_in_basis]
  simp [basisVector_eq_tensorBasis]

/-!

## Expanding pauliCo in a basis.

-/

/-- The map to color one gets when lowering the indices of pauli matrices. -/
def pauliCoMap := ((Sum.elim ![Color.down, Color.down] ![Color.up, Color.upL, Color.upR] ∘
  ⇑finSumFinEquiv.symm) ∘ Fin.succAbove 1 ∘ Fin.succAbove 1)

/-!

## ofRat for pauli matrices.

-/
lemma pauliContr_ofRat : pauliContr = ofRat (fun b =>
    if b = (fun | (0 : Fin 3) => 0 | 1 => 0 | 2 => 0) then ⟨1, 0⟩ else
    if b = (fun | 0 => 0 | 1 => 1 | 2 => 1) then ⟨1, 0⟩ else
    if b = (fun | 0 => 1 | 1 => 0 | 2 => 1) then ⟨1, 0⟩ else
    if b = (fun | 0 => 1 | 1 => 1 | 2 => 0) then ⟨1, 0⟩ else
    if b = (fun | 0 => 2 | 1 => 0 | 2 => 1) then ⟨0, -1⟩ else
    if b = (fun | 0 => 2 | 1 => 1 | 2 => 0) then ⟨0, 1⟩ else
    if b = (fun | 0 => 3 | 1 => 0 | 2 => 0) then ⟨1, 0⟩ else
    if b = (fun | 0 => 3 | 1 => 1 | 2 => 1) then ⟨-1, 0⟩ else 0) := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [pauliContr_tensorBasis]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add, map_neg,
    Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply, cons_val_zero, cons_val_one,
    head_cons]
  repeat rw [tensorBasis_eq_ofRat]
  simp [Nat.succ_eq_add_one, Nat.reduceAdd, map_sub, Finsupp.coe_sub, Pi.sub_apply,
    ofRat_tensorBasis_repr_apply, k_instSub, Fin.isValue, cons_val_zero, cons_val_one, head_cons]
  simp only [Fin.isValue, ← map_add, ← map_sub]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliCo_ofRat : pauliCo = ofRat (fun b =>
    if b = (fun | (0 : Fin 3) => 0 | 1 => 0 | 2 => 0) then ⟨1, 0⟩ else
    if b = (fun | 0 => 0 | 1 => 1 | 2 => 1) then ⟨1, 0⟩ else
    if b = (fun | 0 => 1 | 1 => 0 | 2 => 1) then ⟨-1, 0⟩ else
    if b = (fun | 0 => 1 | 1 => 1 | 2 => 0) then ⟨-1, 0⟩ else
    if b = (fun | 0 => 2 | 1 => 0 | 2 => 1) then ⟨0, 1⟩ else
    if b = (fun | 0 => 2 | 1 => 1 | 2 => 0) then ⟨0, -1⟩ else
    if b = (fun | 0 => 3 | 1 => 0 | 2 => 0) then ⟨-1, 0⟩ else
    if b = (fun | 0 => 3 | 1 => 1 | 2 => 1) then ⟨1, 0⟩ else ⟨0, 0⟩) := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [pauliCo]
  rw [TensorTree.contr_tensorBasis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [TensorTree.prod_tensorBasis_repr_apply]
    simp only [coMetric_eq_ofRat, tensorNode_tensor, ofRat_tensorBasis_repr_apply, pauliContr_ofRat]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  rw [ofRat_tensorBasis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliCoDown_ofRat : pauliCoDown = ofRat (fun b =>
    if b = (fun | (0 : Fin 3) => 0 | 1 => 1 | 2 => 1) then ⟨1, 0⟩ else
    if b = (fun | 0 => 0 | 1 => 0 | 2 => 0) then ⟨1, 0⟩ else
    if b = (fun | 0 => 1 | 1 => 0 | 2 => 1) then ⟨1, 0⟩ else
    if b = (fun | 0 => 1 | 1 => 1 | 2 => 0) then ⟨1, 0⟩ else
    if b = (fun | 0 => 2 | 1 => 0 | 2 => 1) then ⟨0, -1⟩ else
    if b = (fun | 0 => 2 | 1 => 1 | 2 => 0) then ⟨0, 1⟩ else
    if b = (fun | 0 => 3 | 1 => 1 | 2 => 1) then ⟨-1, 0⟩ else
    if b = (fun | 0 => 3 | 1 => 0 | 2 => 0) then ⟨1, 0⟩ else ⟨0, 0⟩) := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [pauliCoDown]
  rw [TensorTree.contr_tensorBasis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [TensorTree.prod_tensorBasis_repr_apply]
    rw [TensorTree.contr_tensorBasis_repr_apply]
    simp only [coMetric_eq_ofRat, tensorNode_tensor, ofRat_tensorBasis_repr_apply,
      altLeftMetric_eq_ofRat]
    enter [1, 1, 2, y]
    rw [contr_basis_ratComplexNum]
    rw [TensorTree.prod_tensorBasis_repr_apply]
    simp only [coMetric_eq_ofRat, tensorNode_tensor, ofRat_tensorBasis_repr_apply, pauliCo_ofRat,
      altRightMetric_eq_ofRat]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  rw [ofRat_tensorBasis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

lemma pauliContrDown_ofRat : pauliContrDown = ofRat (fun b =>
    if b = (fun | (0 : Fin 3) => 0 | 1 => 1 | 2 => 1) then ⟨1, 0⟩ else
    if b = (fun | 0 => 0 | 1 => 0 | 2 => 0) then ⟨1, 0⟩ else
    if b = (fun | 0 => 1 | 1 => 0 | 2 => 1) then ⟨-1, 0⟩ else
    if b = (fun | 0 => 1 | 1 => 1 | 2 => 0) then ⟨-1, 0⟩ else
    if b = (fun | 0 => 2 | 1 => 0 | 2 => 1) then ⟨0, 1⟩ else
    if b = (fun | 0 => 2 | 1 => 1 | 2 => 0) then ⟨0, -1⟩ else
    if b = (fun | 0 => 3 | 1 => 1 | 2 => 1) then ⟨1, 0⟩ else
    if b = (fun | 0 => 3 | 1 => 0 | 2 => 0) then ⟨-1, 0⟩ else 0) := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [pauliContrDown]
  rw [TensorTree.contr_tensorBasis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    rw [TensorTree.prod_tensorBasis_repr_apply]
    rw [TensorTree.contr_tensorBasis_repr_apply]
    simp only [coMetric_eq_ofRat, tensorNode_tensor, ofRat_tensorBasis_repr_apply,
      altLeftMetric_eq_ofRat]
    enter [1, 1, 2, y]
    rw [contr_basis_ratComplexNum]
    rw [TensorTree.prod_tensorBasis_repr_apply]
    simp only [coMetric_eq_ofRat, tensorNode_tensor, ofRat_tensorBasis_repr_apply, pauliContr_ofRat,
      altRightMetric_eq_ofRat]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  conv_lhs =>
    enter [2, x]
    rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  rw [ofRat_tensorBasis_repr_apply]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide +kernel

end PauliMatrix
