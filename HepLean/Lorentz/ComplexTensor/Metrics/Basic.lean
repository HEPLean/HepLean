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

/-- The metric `ηᵢᵢ` as a complex Lorentz tensor. -/
def coMetric := {Lorentz.coMetric | μ ν}ᵀ.tensor

/-- The metric `ηⁱⁱ` as a complex Lorentz tensor. -/
def contrMetric := {Lorentz.contrMetric | μ ν}ᵀ.tensor

/-- The metric `εᵃᵃ` as a complex Lorentz tensor. -/
def leftMetric := {Fermion.leftMetric | α α'}ᵀ.tensor

/-- The metric `ε^{dot a}^{dot a}` as a complex Lorentz tensor. -/
def rightMetric := {Fermion.rightMetric | β β'}ᵀ.tensor

/-- The metric `εₐₐ` as a complex Lorentz tensor. -/
def altLeftMetric := {Fermion.altLeftMetric | α α'}ᵀ.tensor

/-- The metric `ε_{dot a}_{dot a}` as a complex Lorentz tensor. -/
def altRightMetric := {Fermion.altRightMetric | β β'}ᵀ.tensor

/-!

## Notation

-/

/-- The metric `ηᵢᵢ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "η'" => coMetric

/-- The metric `ηⁱⁱ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "η" => contrMetric

/-- The metric `εᵃᵃ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εL" => leftMetric

/-- The metric `ε^{dot a}^{dot a}` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εR" => rightMetric

/-- The metric `εₐₐ` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εL'" => altLeftMetric

/-- The metric `ε_{dot a}_{dot a}` as a complex Lorentz tensors. -/
scoped[complexLorentzTensor] notation "εR'" => altRightMetric

/-!

## Tensor nodes.

-/

/-- The definitional tensor node relation for `coMetric`. -/
lemma tensorNode_coMetric : {η' | μ ν}ᵀ.tensor = {Lorentz.coMetric | μ ν}ᵀ.tensor := by
  rfl

/-- The definitional tensor node relation for `contrMetric`. -/
lemma tensorNode_contrMetric : {η | μ ν}ᵀ.tensor = {Lorentz.contrMetric | μ ν}ᵀ.tensor := by
  rfl

/-- The definitional tensor node relation for `leftMetric`. -/
lemma tensorNode_leftMetric : {εL | α α'}ᵀ.tensor = {Fermion.leftMetric | α α'}ᵀ.tensor := by
  rfl

/-- The definitional tensor node relation for `rightMetric`. -/
lemma tensorNode_rightMetric : {εR | β β'}ᵀ.tensor = {Fermion.rightMetric | β β'}ᵀ.tensor := by
  rfl

/-- The definitional tensor node relation for `altLeftMetric`. -/
lemma tensorNode_altLeftMetric :
    {εL' | α α'}ᵀ.tensor = {Fermion.altLeftMetric | α α'}ᵀ.tensor := by
  rfl

/-- The definitional tensor node relation for `altRightMetric`. -/
lemma tensorNode_altRightMetric :
    {εR' | β β'}ᵀ.tensor = {Fermion.altRightMetric | β β'}ᵀ.tensor := by
  rfl

/-!

## Group actions

-/

/-- The tensor `coMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_coMetric (g : SL(2,ℂ)) : {g •ₐ η' | μ ν}ᵀ.tensor =
    {η' | μ ν}ᵀ.tensor := by
  rw [tensorNode_coMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `contrMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_contrMetric (g : SL(2,ℂ)) : {g •ₐ η | μ ν}ᵀ.tensor =
    {η | μ ν}ᵀ.tensor := by
  rw [tensorNode_contrMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `leftMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_leftMetric (g : SL(2,ℂ)) : {g •ₐ εL | α α'}ᵀ.tensor =
    {εL | α α'}ᵀ.tensor := by
  rw [tensorNode_leftMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `rightMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_rightMetric (g : SL(2,ℂ)) : {g •ₐ εR | β β'}ᵀ.tensor =
    {εR | β β'}ᵀ.tensor := by
  rw [tensorNode_rightMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `altLeftMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_altLeftMetric (g : SL(2,ℂ)) : {g •ₐ εL' | α α'}ᵀ.tensor =
    {εL' | α α'}ᵀ.tensor := by
  rw [tensorNode_altLeftMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

/-- The tensor `altRightMetric` is invariant under the action of `SL(2,ℂ)`. -/
lemma action_altRightMetric (g : SL(2,ℂ)) : {g •ₐ εR' | β β'}ᵀ.tensor =
    {εR' | β β'}ᵀ.tensor := by
  rw [tensorNode_altRightMetric, constTwoNodeE]
  rw [← action_constTwoNode _ g]
  rfl

end complexLorentzTensor
