/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.ComplexTensor.Metrics.Basic
import PhysLean.Relativity.Lorentz.ComplexTensor.OfRat
import PhysLean.Relativity.Lorentz.ComplexTensor.Basis
import PhysLean.Relativity.Tensors.TensorSpecies.OfInt
/-!

## Metrics and basis expansions

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

/-- The expansion of the Lorentz covariant metric in terms of basis vectors. -/
lemma coMetric_basis_expand : {η' | μ ν}ᵀ.tensor =
    basisVector ![Color.down, Color.down] (fun _ => 0)
    - basisVector ![Color.down, Color.down] (fun _ => 1)
    - basisVector ![Color.down, Color.down] (fun _ => 2)
    - basisVector ![Color.down, Color.down] (fun _ => 3) := by
  rw [tensorNode_coMetric]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Functor.id_obj, Fin.isValue]
  erw [Lorentz.coMetric_apply_one, Lorentz.coMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    all_goals
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      change _ = Lorentz.complexCoBasisFin4 _
      simp only [Fin.isValue, Lorentz.complexCoBasisFin4, Basis.coe_reindex, Function.comp_apply]
      rfl

lemma coMetric_tensorBasis : η' =
    complexLorentzTensor.tensorBasis ![Color.down, Color.down] (fun _ => 0)
    - complexLorentzTensor.tensorBasis ![Color.down, Color.down] (fun _ => 1)
    - complexLorentzTensor.tensorBasis ![Color.down, Color.down] (fun _ => 2)
    - complexLorentzTensor.tensorBasis ![Color.down, Color.down] (fun _ => 3) := by
  trans {η' | μ ν}ᵀ.tensor
  · simp
  · rw [coMetric_basis_expand]
    simp [basisVector_eq_tensorBasis]

lemma coMetric_eq_ofRat : η' = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 0 then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [coMetric_tensorBasis]
  repeat rw [tensorBasis_eq_ofRat]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_sub, Finsupp.coe_sub, Pi.sub_apply,
    ofRat_tensorBasis_repr_apply, k_instSub, Fin.isValue, cons_val_zero, cons_val_one, head_cons]
  simp only [← map_sub, Fin.isValue]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  with_unfolding_all decide

/-- Provides the explicit expansion of the co-metric tensor in terms of the basis elements, as
a tensor tree. -/
lemma coMetric_basis_expand_tree : {η' | μ ν}ᵀ.tensor =
    (TensorTree.add (tensorNode (basisVector ![Color.down, Color.down] (fun _ => 0))) <|
    TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.down, Color.down] (fun _ => 1)))) <|
    TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.down, Color.down] (fun _ => 2)))) <|
    (smul (-1) (tensorNode (basisVector ![Color.down, Color.down] (fun _ => 3))))).tensor :=
  coMetric_basis_expand

/-!

## contrMetric

-/
/-- The expansion of the Lorentz contravariant metric in terms of basis vectors. -/
lemma contrMetric_basis_expand : {η | μ ν}ᵀ.tensor =
    basisVector ![Color.up, Color.up] (fun _ => 0)
    - basisVector ![Color.up, Color.up] (fun _ => 1)
    - basisVector ![Color.up, Color.up] (fun _ => 2)
    - basisVector ![Color.up, Color.up] (fun _ => 3) := by
  rw [tensorNode_contrMetric]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V]
  erw [Lorentz.contrMetric_apply_one, Lorentz.contrMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    all_goals
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      change _ = Lorentz.complexContrBasisFin4 _
      simp only [Fin.isValue, Lorentz.complexContrBasisFin4, Basis.coe_reindex, Function.comp_apply]
      rfl

lemma contrMetric_tensorBasis : η =
    complexLorentzTensor.tensorBasis ![Color.up, Color.up] (fun _ => 0)
    - complexLorentzTensor.tensorBasis ![Color.up, Color.up] (fun _ => 1)
    - complexLorentzTensor.tensorBasis ![Color.up, Color.up] (fun _ => 2)
    - complexLorentzTensor.tensorBasis ![Color.up, Color.up] (fun _ => 3) := by
  trans {η | μ ν}ᵀ.tensor
  · simp
  · rw [contrMetric_basis_expand]
    simp [basisVector_eq_tensorBasis]

lemma contrMetric_eq_ofRat : η = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 0 then 1 else
    if f 0 = f 1 then - 1 else 0 := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [contrMetric_tensorBasis]
  repeat rw [tensorBasis_eq_ofRat]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_sub, Finsupp.coe_sub, Pi.sub_apply,
    ofRat_tensorBasis_repr_apply, k_instSub, Fin.isValue, cons_val_zero, cons_val_one, head_cons]
  simp only [← map_sub, Fin.isValue]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  with_unfolding_all decide

/-- The expansion of the Lorentz contravariant metric in terms of basis vectors as
  a structured tensor tree. -/
lemma contrMetric_basis_expand_tree : {η | μ ν}ᵀ.tensor =
    (TensorTree.add (tensorNode (basisVector ![Color.up, Color.up] (fun _ => 0))) <|
    TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.up, Color.up] (fun _ => 1)))) <|
    TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.up, Color.up] (fun _ => 2)))) <|
    (smul (-1) (tensorNode (basisVector ![Color.up, Color.up] (fun _ => 3))))).tensor :=
  contrMetric_basis_expand

/-- The expansion of the Fermionic left metric in terms of basis vectors. -/
lemma leftMetric_expand : {εL | α β}ᵀ.tensor =
    - basisVector ![Color.upL, Color.upL] (fun | 0 => 0 | 1 => 1)
    + basisVector ![Color.upL, Color.upL] (fun | 0 => 1 | 1 => 0) := by
  rw [tensorNode_leftMetric]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [Fermion.leftMetric_apply_one, Fermion.leftMetricVal_expand_tmul]
  simp only [Fin.isValue, map_add, map_neg]
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    · rfl
    · rfl

lemma leftMetric_tensorBasis : εL =
    - complexLorentzTensor.tensorBasis ![Color.upL, Color.upL] (fun | 0 => 0 | 1 => 1)
    + complexLorentzTensor.tensorBasis ![Color.upL, Color.upL] (fun | 0 => 1 | 1 => 0) := by
  trans {εL | μ ν}ᵀ.tensor
  · simp
  · rw [leftMetric_expand]
    simp [basisVector_eq_tensorBasis]

lemma leftMetric_eq_ofRat : εL = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 1 then - 1 else
    if f 1 = 0 ∧ f 0 = 1 then 1 else 0 := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [leftMetric_tensorBasis]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add, map_neg,
    Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply, cons_val_zero, cons_val_one,
    head_cons]
  repeat rw [tensorBasis_eq_ofRat]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_sub, Finsupp.coe_sub, Pi.sub_apply,
    ofRat_tensorBasis_repr_apply, k_instSub, Fin.isValue, cons_val_zero, cons_val_one, head_cons]
  simp only [Fin.isValue, k_neg, ← map_neg, k_instAdd, ← map_add]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  with_unfolding_all decide

/-- The expansion of the Fermionic left metric in terms of basis vectors as a structured
  tensor tree. -/
lemma leftMetric_expand_tree : {εL | α β}ᵀ.tensor =
    (TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.upL, Color.upL]
    (fun | 0 => 0 | 1 => 1)))) <|
    (tensorNode (basisVector ![Color.upL, Color.upL] (fun | 0 => 1 | 1 => 0)))).tensor :=
  leftMetric_expand

/-- The expansion of the Fermionic alt-left metric in terms of basis vectors. -/
lemma altLeftMetric_expand : {εL' | α β}ᵀ.tensor =
    basisVector ![Color.downL, Color.downL] (fun | 0 => 0 | 1 => 1)
    - basisVector ![Color.downL, Color.downL] (fun | 0 => 1 | 1 => 0) := by
  rw [tensorNode_altLeftMetric]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [Fermion.altLeftMetric_apply_one, Fermion.altLeftMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    · rfl
    · rfl

lemma altLeftMetric_tensorBasis : εL' =
    complexLorentzTensor.tensorBasis ![Color.downL, Color.downL] (fun | 0 => 0 | 1 => 1)
    - complexLorentzTensor.tensorBasis ![Color.downL, Color.downL] (fun | 0 => 1 | 1 => 0) := by
  trans {εL' | μ ν}ᵀ.tensor
  · simp
  · rw [altLeftMetric_expand]
    simp [basisVector_eq_tensorBasis]

lemma altLeftMetric_eq_ofRat : εL' = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 1 then 1 else
    if f 1 = 0 ∧ f 0 = 1 then - 1 else 0 := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [altLeftMetric_tensorBasis]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add, map_neg,
    Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply, cons_val_zero, cons_val_one,
    head_cons]
  repeat rw [tensorBasis_eq_ofRat]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_sub, Finsupp.coe_sub, Pi.sub_apply,
    ofRat_tensorBasis_repr_apply, k_instSub, Fin.isValue, cons_val_zero, cons_val_one, head_cons]
  simp only [Fin.isValue, ← map_sub]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  with_unfolding_all decide

/-- The expansion of the Fermionic alt-left metric in terms of basis vectors as a
  structured tensor tree. -/
lemma altLeftMetric_expand_tree : {εL' | α β}ᵀ.tensor =
    (TensorTree.add (tensorNode (basisVector ![Color.downL, Color.downL]
    (fun | 0 => 0 | 1 => 1))) <|
    (smul (-1) (tensorNode (basisVector ![Color.downL, Color.downL]
    (fun | 0 => 1 | 1 => 0))))).tensor :=
  altLeftMetric_expand

/-- The expansion of the Fermionic right metric in terms of basis vectors. -/
lemma rightMetric_expand : {εR | α β}ᵀ.tensor =
    - basisVector ![Color.upR, Color.upR] (fun | 0 => 0 | 1 => 1)
    + basisVector ![Color.upR, Color.upR] (fun | 0 => 1 | 1 => 0) := by
  rw [tensorNode_rightMetric]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [Fermion.rightMetric_apply_one, Fermion.rightMetricVal_expand_tmul]
  simp only [Fin.isValue, map_add, map_neg]
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    · rfl
    · rfl

lemma rightMetric_tensorBasis : εR =
    - complexLorentzTensor.tensorBasis ![Color.upR, Color.upR] (fun | 0 => 0 | 1 => 1)
    + complexLorentzTensor.tensorBasis ![Color.upR, Color.upR] (fun | 0 => 1 | 1 => 0) := by
  trans {εR | μ ν}ᵀ.tensor
  · simp
  · rw [rightMetric_expand]
    simp [basisVector_eq_tensorBasis]

lemma rightMetric_eq_ofRat : εR = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 1 then - 1 else
    if f 1 = 0 ∧ f 0 = 1 then 1 else 0 := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [rightMetric_tensorBasis]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add, map_neg,
    Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply, cons_val_zero, cons_val_one,
    head_cons]
  repeat rw [tensorBasis_eq_ofRat]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_sub, Finsupp.coe_sub, Pi.sub_apply,
    ofRat_tensorBasis_repr_apply, k_instSub, Fin.isValue, cons_val_zero, cons_val_one, head_cons]
  simp only [Fin.isValue, k_neg, ← map_neg, k_instAdd, ← map_add]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  with_unfolding_all decide

/-- The expansion of the Fermionic right metric in terms of basis vectors as a
  structured tensor tree. -/
lemma rightMetric_expand_tree : {εR | α β}ᵀ.tensor =
    (TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.upR, Color.upR]
    (fun | 0 => 0 | 1 => 1)))) <|
    (tensorNode (basisVector ![Color.upR, Color.upR] (fun | 0 => 1 | 1 => 0)))).tensor :=
  rightMetric_expand

/-- The expansion of the Fermionic alt-right metric in terms of basis vectors. -/
lemma altRightMetric_expand : {εR' | α β}ᵀ.tensor =
    basisVector ![Color.downR, Color.downR] (fun | 0 => 0 | 1 => 1)
    - basisVector ![Color.downR, Color.downR] (fun | 0 => 1 | 1 => 0) := by
  rw [tensorNode_altRightMetric]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [Fermion.altRightMetric_apply_one, Fermion.altRightMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    · rfl
    · rfl

lemma altRightMetric_tensorBasis : εR' =
    complexLorentzTensor.tensorBasis ![Color.downR, Color.downR] (fun | 0 => 0 | 1 => 1)
    - complexLorentzTensor.tensorBasis ![Color.downR, Color.downR] (fun | 0 => 1 | 1 => 0) := by
  trans {εR' | μ ν}ᵀ.tensor
  · simp
  · rw [altRightMetric_expand]
    simp [basisVector_eq_tensorBasis]

lemma altRightMetric_eq_ofRat : εR' = ofRat fun f =>
    if f 0 = 0 ∧ f 1 = 1 then 1 else
    if f 1 = 0 ∧ f 0 = 1 then - 1 else 0 := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [altRightMetric_tensorBasis]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, map_add, map_neg,
    Finsupp.coe_add, Finsupp.coe_neg, Pi.add_apply, Pi.neg_apply, cons_val_zero, cons_val_one,
    head_cons]
  repeat rw [tensorBasis_eq_ofRat]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_sub, Finsupp.coe_sub, Pi.sub_apply,
    ofRat_tensorBasis_repr_apply, k_instSub, Fin.isValue, cons_val_zero, cons_val_one, head_cons]
  simp only [Fin.isValue, ← map_sub]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  with_unfolding_all decide

/-- The expansion of the Fermionic alt-right metric in terms of basis vectors as a
  structured tensor tree. -/
lemma altRightMetric_expand_tree : {εR' | α β}ᵀ.tensor =
    (TensorTree.add (tensorNode (basisVector
    ![Color.downR, Color.downR] (fun | 0 => 0 | 1 => 1))) <|
    (smul (-1) (tensorNode (basisVector ![Color.downR, Color.downR]
    (fun | 0 => 1 | 1 => 0))))).tensor :=
  altRightMetric_expand

end complexLorentzTensor
