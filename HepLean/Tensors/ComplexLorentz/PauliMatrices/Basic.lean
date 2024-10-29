/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.NodeIdentities.ProdAssoc
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.ProdContr
import HepLean.Tensors.Tree.NodeIdentities.ContrContr
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.PermContr
import HepLean.Tensors.Tree.NodeIdentities.Congr
/-!

## Pauli matrices as complex Lorentz tensors

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

/-!

## Definitions.

-/

/- The Pauli matrices as the complex Lorentz tensor `σ^μ^α^{dot β}`. -/
def pauliContr := {PauliMatrix.asConsTensor | ν α β}ᵀ.tensor

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ^α^{dot β}`. -/
def pauliCo := {Lorentz.coMetric | μ ν ⊗ pauliContr | ν α β}ᵀ.tensor

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ_α_{dot β}`. -/
def pauliCoDown := {pauliCo | μ α β ⊗ Fermion.altLeftMetric | α α' ⊗
  Fermion.altRightMetric | β β'}ᵀ.tensor

/-- The Pauli matrices as the complex Lorentz tensor `σ^μ_α_{dot β}`. -/
def pauliContrDown := {pauliContr | μ α β ⊗ Fermion.altLeftMetric | α α' ⊗
  Fermion.altRightMetric | β β'}ᵀ.tensor

/-!

## Tensor nodes.

-/

/-- The definitional tensor node relation for `pauliContr`. -/
lemma tensorNode_pauliContr : {pauliContr | μ α β}ᵀ.tensor =
    {PauliMatrix.asConsTensor | ν α β}ᵀ.tensor := by
  rfl

/-- The definitional tensor node relation for `pauliCo`. -/
lemma tensorNode_pauliCo : {pauliCo | μ α β}ᵀ.tensor =
    {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | ν α β}ᵀ.tensor := by
  rfl

/-- The definitional tensor node relation for `pauliCoDown`. -/
lemma tensorNode_pauliCoDown : {pauliCoDown | μ α β}ᵀ.tensor =
    {pauliCo | μ α β ⊗ Fermion.altLeftMetric | α α' ⊗
    Fermion.altRightMetric | β β'}ᵀ.tensor := by
  rfl

/-- The definitional tensor node relation for `pauliContrDown`. -/
lemma tensorNode_pauliContrDown : {pauliContrDown | μ α β}ᵀ.tensor =
    {pauliContr | μ α β ⊗ Fermion.altLeftMetric | α α' ⊗
    Fermion.altRightMetric | β β'}ᵀ.tensor := by
  rfl

/-!

## Basic equalities

-/

set_option maxRecDepth 5000 in
/-- A rearanging of `pauliCoDown` to place the pauli matrices on the right. -/
lemma pauliCoDown_eq_metric_mul_pauliCo :
    {pauliCoDown | μ α' β' = Fermion.altLeftMetric | α α' ⊗
    Fermion.altRightMetric | β β' ⊗ pauliCo | μ α β}ᵀ := by
  conv =>
    lhs
    rw [tensorNode_pauliCoDown]
    rw [contr_tensor_eq <| contr_prod _ _ _]
    rw [perm_contr]
    erw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| perm_eq_id _ rfl _]
    rw [perm_tensor_eq <| contr_congr 1 2]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_congr 1 2]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_congr 1 2]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| prod_assoc' _ _ _ _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_tensor_eq <| contr_congr 1 2]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_perm _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_congr 1 2]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| prod_comm _ _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_tensor_eq <| contr_congr 5 0]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_perm _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_congr 4 1]
    rw [perm_perm]
  conv =>
    rhs
    rw [perm_tensor_eq <| contr_swap _ _]
    rw [perm_perm]
    erw [perm_tensor_eq <| contr_congr 4 1]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_swap _ _]
    erw [perm_tensor_eq <| contr_tensor_eq <| perm_tensor_eq <| contr_congr 5 0]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_perm _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_congr 4 1]
    rw [perm_perm]
  apply perm_congr _ rfl
  decide

set_option maxRecDepth 5000 in
/-- A rearanging of `pauliContrDown` to place the pauli matrices on the right. -/
lemma pauliContrDown_eq_metric_mul_pauliContr :
    {pauliContrDown | μ α' β' = Fermion.altLeftMetric | α α' ⊗
    Fermion.altRightMetric | β β' ⊗ pauliContr | μ α β}ᵀ := by
  conv =>
    lhs
    rw [tensorNode_pauliContrDown]
    rw [contr_tensor_eq <| contr_prod _ _ _]
    rw [perm_contr]
    erw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| perm_eq_id _ rfl _]
    rw [perm_tensor_eq <| contr_congr 1 2]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_congr 1 2]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_congr 1 2]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| prod_assoc' _ _ _ _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_tensor_eq <| contr_congr 1 2]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_perm _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_congr 1 2]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| prod_comm _ _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_tensor_eq <| contr_congr 5 0]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_perm _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_congr 4 1]
    rw [perm_perm]
  conv =>
    rhs
    rw [perm_tensor_eq <| contr_swap _ _]
    rw [perm_perm]
    erw [perm_tensor_eq <| contr_congr 4 1]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_swap _ _]
    erw [perm_tensor_eq <| contr_tensor_eq <| perm_tensor_eq <| contr_congr 5 0]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_perm _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_congr 4 1]
    rw [perm_perm]
  apply perm_congr _ rfl
  decide

end complexLorentzTensor
