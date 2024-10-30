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

## Metrics as complex Lorentz tensors

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

/-- The unit `δᵢⁱ` as a complex Lorentz tensor. -/
def coContrUnit := (TensorTree.constTwoNodeE complexLorentzTensor Color.down Color.up
  Lorentz.coContrUnit).tensor

/-- The unit `δⁱᵢ` as a complex Lorentz tensor. -/
def contrCoUnit := (TensorTree.constTwoNodeE complexLorentzTensor Color.up Color.down
  Lorentz.contrCoUnit).tensor

/-- The unit `δₐᵃ` as a complex Lorentz tensor. -/
def altLeftLeftUnit := (TensorTree.constTwoNodeE complexLorentzTensor Color.downL Color.upL
  Fermion.altLeftLeftUnit).tensor

/-- The unit `δᵃₐ` as a complex Lorentz tensor. -/
def leftAltLeftUnit := (TensorTree.constTwoNodeE complexLorentzTensor Color.upL Color.downL
  Fermion.leftAltLeftUnit).tensor

/-- The unit `δ_{dot a}^{dot a}` as a complex Lorentz tensor. -/
def altRightRightUnit := (TensorTree.constTwoNodeE complexLorentzTensor Color.downR Color.upR
  Fermion.altRightRightUnit).tensor

/-- The unit `δ^{dot a}_{dot a}` as a complex Lorentz tensor. -/
def rightAltRightUnit := (TensorTree.constTwoNodeE complexLorentzTensor Color.upR Color.downR
  Fermion.rightAltRightUnit).tensor

/-!

## Notation

-/

/-- The unit `δᵢⁱ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δ'" => coContrUnit

/-- The unit `δⁱᵢ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δ" => contrCoUnit

/-- The unit `δₐᵃ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δL'" => altLeftLeftUnit

/-- The unit `δᵃₐ` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δL" => leftAltLeftUnit

/-- The unit `δ_{dot a}^{dot a}` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δR'" => altRightRightUnit

/-- The unit `δ^{dot a}_{dot a}` as a complex Lorentz tensor. -/
scoped[complexLorentzTensor] notation "δR" => rightAltRightUnit

/-!

## Tensor nodes.

-/

/-- The definitional tensor node relation for `coContrUnit`. -/
lemma tensorNode_coMetric : {δ' | μ ν}ᵀ.tensor = (TensorTree.constTwoNodeE complexLorentzTensor
  Color.down Color.up Lorentz.coContrUnit).tensor:= by
  rfl

/-- The definitional tensor node relation for `contrCoUnit`. -/
lemma tensorNode_contrMetric : {δ | μ ν}ᵀ.tensor = (TensorTree.constTwoNodeE complexLorentzTensor
  Color.up Color.down Lorentz.contrCoUnit).tensor := by
  rfl

/-- The definitional tensor node relation for `altLeftLeftUnit`. -/
lemma tensorNode_altLeftLeftMetric : {δL' | μ ν}ᵀ.tensor = (TensorTree.constTwoNodeE
  complexLorentzTensor Color.downL Color.upL Fermion.altLeftLeftUnit).tensor := by
  rfl

/-- The definitional tensor node relation for `leftAltLeftUnit`. -/
lemma tensorNode_leftAltLeftMetric : {δL | μ ν}ᵀ.tensor = (TensorTree.constTwoNodeE
  complexLorentzTensor Color.upL Color.downL Fermion.leftAltLeftUnit).tensor := by
  rfl

/-- The definitional tensor node relation for `altRightRightUnit`. -/
lemma tensorNode_altRightRightMetric : {δR' | μ ν}ᵀ.tensor = (TensorTree.constTwoNodeE
  complexLorentzTensor Color.downR Color.upR Fermion.altRightRightUnit).tensor := by
  rfl

/-- The definitional tensor node relation for `rightAltRightUnit`. -/
lemma tensorNode_rightAltRightMetric : {δR | μ ν}ᵀ.tensor = (TensorTree.constTwoNodeE
  complexLorentzTensor Color.upR Color.downR Fermion.rightAltRightUnit).tensor := by
  rfl

/-!

## Group actions

-/

/-- The tensor `coContrUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_coContrUnit (g : SL(2,ℂ)) : {g •ₐ δ' | μ ν}ᵀ.tensor = {δ' | μ ν}ᵀ.tensor := by
  rw [tensorNode_coMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `contrCoUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_contrCoUnit (g : SL(2,ℂ)) : {g •ₐ δ | μ ν}ᵀ.tensor = {δ | μ ν}ᵀ.tensor := by
  rw [tensorNode_contrMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `altLeftLeftUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_altLeftLeftUnit (g : SL(2,ℂ)) : {g •ₐ δL' | μ ν}ᵀ.tensor = {δL' | μ ν}ᵀ.tensor := by
  rw [tensorNode_altLeftLeftMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `leftAltLeftUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_leftAltLeftUnit (g : SL(2,ℂ)) : {g •ₐ δL | μ ν}ᵀ.tensor = {δL | μ ν}ᵀ.tensor := by
  rw [tensorNode_leftAltLeftMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `altRightRightUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_altRightRightUnit (g : SL(2,ℂ)) : {g •ₐ δR' | μ ν}ᵀ.tensor = {δR' | μ ν}ᵀ.tensor := by
  rw [tensorNode_altRightRightMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `rightAltRightUnit` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_rightAltRightUnit (g : SL(2,ℂ)) : {g •ₐ δR | μ ν}ᵀ.tensor = {δR | μ ν}ᵀ.tensor := by
  rw [tensorNode_rightAltRightMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

end complexLorentzTensor
