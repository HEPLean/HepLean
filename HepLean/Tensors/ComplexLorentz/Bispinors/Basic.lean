/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.ComplexLorentz.PauliMatrices.Basic
import HepLean.Tensors.Tree.NodeIdentities.ProdContr
import HepLean.Tensors.Tree.NodeIdentities.PermContr
import HepLean.Tensors.Tree.NodeIdentities.PermProd
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.ContrContr
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.Congr
import HepLean.Tensors.Tree.NodeIdentities.ProdAssoc
/-!

## Bispinors

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
open Fermion
noncomputable section
namespace complexLorentzTensor
open Lorentz

/-!

## Definitions

-/

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p^μ`. -/
def contrBispinorUp (p : complexContr) :=
  {pauliCo | μ α β ⊗ p | μ}ᵀ.tensor

/-- A bispinor `pₐₐ` created from a lorentz vector `p^μ`. -/
def contrBispinorDown (p : complexContr) :=
  {Fermion.altLeftMetric | α α' ⊗ Fermion.altRightMetric | β β' ⊗
  contrBispinorUp p | α β}ᵀ.tensor

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p_μ`. -/
def coBispinorUp (p : complexCo) :=
  {pauliContr | μ α β ⊗ p | μ}ᵀ.tensor

/-- A bispinor `pₐₐ` created from a lorentz vector `p_μ`. -/
def coBispinorDown (p : complexCo) :=
  {Fermion.altLeftMetric | α α' ⊗ Fermion.altRightMetric | β β' ⊗
  coBispinorUp p | α β}ᵀ.tensor

/-!

## Tensor nodes

-/

/-- The definitional tensor node relation for `contrBispinorUp`. -/
lemma tensorNode_contrBispinorUp (p : complexContr) :
    {contrBispinorUp p | α β}ᵀ.tensor = {pauliCo | μ α β ⊗ p | μ}ᵀ.tensor := by
  rw [contrBispinorUp, tensorNode_tensor]

/-- The definitional tensor node relation for `contrBispinorDown`. -/
lemma tensorNode_contrBispinorDown (p : complexContr) :
    {contrBispinorDown p | α β}ᵀ.tensor =
    {Fermion.altLeftMetric | α α' ⊗ Fermion.altRightMetric | β β'
    ⊗ contrBispinorUp p | α β}ᵀ.tensor := by
  rw [contrBispinorDown, tensorNode_tensor]

/-- The definitional tensor node relation for `coBispinorUp`. -/
lemma tensorNode_coBispinorUp  (p : complexCo) :
    {coBispinorUp p | α β}ᵀ.tensor = {pauliContr | μ α β ⊗ p | μ}ᵀ.tensor := by
  rw [coBispinorUp, tensorNode_tensor]

/-- The definitional tensor node relation for `coBispinorDown`. -/
lemma tensorNode_coBispinorDown (p : complexCo) :
    {coBispinorDown p | α β}ᵀ.tensor =
    {Fermion.altLeftMetric | α α' ⊗ Fermion.altRightMetric | β β'
    ⊗ coBispinorUp p | α β}ᵀ.tensor := by
  rw [coBispinorDown, tensorNode_tensor]

end complexLorentzTensor
end
