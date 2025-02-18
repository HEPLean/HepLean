/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Lorentz.ComplexTensor.Metrics.Lemmas
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

namespace PauliMatrix
open Fermion
open complexLorentzTensor
/-!

## Definitions.

-/

/-- The Pauli matrices as the complex Lorentz tensor `σ^μ^α^{dot β}`. -/
def pauliContr := (TensorTree.constThreeNodeE complexLorentzTensor .up .upL .upR
  PauliMatrix.asConsTensor).tensor

@[inherit_doc pauliContr]
scoped[PauliMatrix] notation "σ^^^" => PauliMatrix.pauliContr

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ^α^{dot β}`. -/
def pauliCo := {η' | μ ν ⊗ σ^^^ | ν α β}ᵀ.tensor

@[inherit_doc pauliCo]
scoped[PauliMatrix] notation "σ_^^" => PauliMatrix.pauliCo

/-- The Pauli matrices as the complex Lorentz tensor `σ_μ_{dot β}_α`. -/
def pauliCoDown := {σ_^^ | μ α β ⊗ εR' | β β' ⊗ εL' | α α' }ᵀ.tensor

@[inherit_doc pauliCoDown]
scoped[PauliMatrix] notation "σ___" => PauliMatrix.pauliCoDown

/-- The Pauli matrices as the complex Lorentz tensor `σ^μ_{dot β}_α`. -/
def pauliContrDown := {pauliContr | μ α β ⊗ εR' | β β' ⊗ εL' | α α' }ᵀ.tensor

@[inherit_doc pauliContrDown]
scoped[PauliMatrix] notation "σ^__" => PauliMatrix.pauliContrDown

/-!

## Tensor nodes.

-/

/-- The definitional tensor node relation for `pauliContr`. -/
lemma tensorNode_pauliContr : {pauliContr | μ α β}ᵀ.tensor =
    (TensorTree.constThreeNodeE complexLorentzTensor .up .upL .upR
  PauliMatrix.asConsTensor).tensor := by
  rfl

/-- The definitional tensor node relation for `pauliCo`. -/
lemma tensorNode_pauliCo : {pauliCo | μ α β}ᵀ.tensor =
    {η' | μ ν ⊗ pauliContr | ν α β}ᵀ.tensor := by
  rw [pauliCo, tensorNode_tensor]

/-- The definitional tensor node relation for `pauliCoDown`. -/
lemma tensorNode_pauliCoDown : {pauliCoDown | μ α β}ᵀ.tensor =
    {pauliCo | μ α β ⊗ εR' | β β' ⊗ εL' | α α' }ᵀ.tensor := by
  rw [pauliCoDown, tensorNode_tensor]

/-- The definitional tensor node relation for `pauliContrDown`. -/
lemma tensorNode_pauliContrDown : {pauliContrDown | μ α β}ᵀ.tensor =
    {pauliContr | μ α β ⊗ εR' | β β' ⊗ εL' | α α' }ᵀ.tensor := by
  rw [pauliContr, tensorNode_tensor]
  rfl

/-!

## Group actions

-/

/-- The tensor `pauliContr` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_pauliContr (g : SL(2,ℂ)) : {g •ₐ pauliContr | μ α β}ᵀ.tensor =
    {pauliContr | μ α β}ᵀ.tensor := by
  rw [tensorNode_pauliContr, constThreeNodeE]
  rw [← action_constThreeNode _ g]
  rfl

/-- The tensor `pauliCo` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_pauliCo (g : SL(2,ℂ)) : {g •ₐ pauliCo | μ α β}ᵀ.tensor =
    {pauliCo | μ α β}ᵀ.tensor := by
  conv =>
    lhs
    rw [action_tensor_eq <| tensorNode_pauliCo]
    rw [action_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <| tensorNode_pauliContr]
    rw [(contr_action _ _).symm]
    rw [contr_tensor_eq <| (prod_action _ _ _).symm]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| action_constTwoNode _ _]
    rw [contr_tensor_eq <| prod_tensor_eq_snd <| action_constThreeNode _ _]
  conv =>
    rhs
    rw [tensorNode_pauliCo]
    rw [contr_tensor_eq <| prod_tensor_eq_snd <| tensorNode_pauliContr]
  rfl

/-- The tensor `pauliCoDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_pauliCoDown (g : SL(2,ℂ)) : {g •ₐ pauliCoDown | μ α β}ᵀ.tensor =
    {pauliCoDown | μ α β}ᵀ.tensor := by
  conv =>
    lhs
    rw [action_tensor_eq <| tensorNode_pauliCoDown]
    rw [(contr_action _ _).symm]
    rw [contr_tensor_eq <| (prod_action _ _ _).symm]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| (contr_action _ _).symm]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_tensor_eq <| (prod_action _ _ _).symm]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_tensor_eq <| prod_tensor_eq_fst <|
      action_pauliCo _]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_tensor_eq <| prod_tensor_eq_snd <|
      action_altRightMetric _]
    rw [contr_tensor_eq <| prod_tensor_eq_snd <| action_altLeftMetric _]
  conv =>
    rhs
    rw [tensorNode_pauliCoDown]

/-- The tensor `pauliContrDown` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_pauliContrDown (g : SL(2,ℂ)) : {g •ₐ pauliContrDown | μ α β}ᵀ.tensor =
    {pauliContrDown | μ α β}ᵀ.tensor := by
  conv =>
    lhs
    rw [action_tensor_eq <| tensorNode_pauliContrDown]
    rw [(contr_action _ _).symm]
    rw [contr_tensor_eq <| (prod_action _ _ _).symm]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| (contr_action _ _).symm]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_tensor_eq <| (prod_action _ _ _).symm]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_tensor_eq <| prod_tensor_eq_fst <|
      action_pauliContr _]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_tensor_eq <| prod_tensor_eq_snd <|
      action_altRightMetric _]
    erw [contr_tensor_eq <| prod_tensor_eq_snd <| action_altLeftMetric _]
  conv =>
    rhs
    rw [tensorNode_pauliContrDown]

end PauliMatrix
