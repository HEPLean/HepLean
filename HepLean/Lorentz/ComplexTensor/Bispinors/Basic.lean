/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.ComplexTensor.PauliMatrices.Basic
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
  {εL' | α α' ⊗ εR' | β β' ⊗ contrBispinorUp p | α β}ᵀ.tensor

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p_μ`. -/
def coBispinorUp (p : complexCo) := {pauliContr | μ α β ⊗ p | μ}ᵀ.tensor

/-- A bispinor `pₐₐ` created from a lorentz vector `p_μ`. -/
def coBispinorDown (p : complexCo) :=
  {εL' | α α' ⊗ εR' | β β' ⊗ coBispinorUp p | α β}ᵀ.tensor

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
    {εL' | α α' ⊗ εR' | β β' ⊗ contrBispinorUp p | α β}ᵀ.tensor := by
  rw [contrBispinorDown, tensorNode_tensor]

/-- The definitional tensor node relation for `coBispinorUp`. -/
lemma tensorNode_coBispinorUp (p : complexCo) :
    {coBispinorUp p | α β}ᵀ.tensor = {pauliContr | μ α β ⊗ p | μ}ᵀ.tensor := by
  rw [coBispinorUp, tensorNode_tensor]

/-- The definitional tensor node relation for `coBispinorDown`. -/
lemma tensorNode_coBispinorDown (p : complexCo) :
    {coBispinorDown p | α β}ᵀ.tensor =
    {εL' | α α' ⊗ εR' | β β' ⊗ coBispinorUp p | α β}ᵀ.tensor := by
  rw [coBispinorDown, tensorNode_tensor]

/-!

## Basic equalities.

-/

/-- `{contrBispinorUp p | α β = εL | α α' ⊗ εR | β β'⊗ contrBispinorDown p | α' β' }ᵀ`.

Proof: expand `contrBispinorDown` and use fact that metrics contract to the identity.
-/
informal_lemma contrBispinorUp_eq_metric_contr_contrBispinorDown where
  deps := [``contrBispinorUp, ``contrBispinorDown, ``leftMetric, ``rightMetric]

/-- `{coBispinorUp p | α β = εL | α α' ⊗ εR | β β'⊗ coBispinorDown p | α' β' }ᵀ`.

proof: expand `coBispinorDown` and use fact that metrics contract to the identity.
-/
informal_lemma coBispinorUp_eq_metric_contr_coBispinorDown where
  deps := [``coBispinorUp, ``coBispinorDown, ``leftMetric, ``rightMetric]

lemma contrBispinorDown_expand (p : complexContr) :
    {contrBispinorDown p | α β}ᵀ.tensor =
    {εL' | α α' ⊗ εR' | β β' ⊗
    (pauliCo | μ α β ⊗ p | μ)}ᵀ.tensor := by
  rw [tensorNode_contrBispinorDown p]
  rw [contr_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <| tensorNode_contrBispinorUp p]

lemma coBispinorDown_expand (p : complexCo) :
    {coBispinorDown p | α β}ᵀ.tensor =
    {εL' | α α' ⊗ εR' | β β' ⊗
    (pauliContr | μ α β ⊗ p | μ)}ᵀ.tensor := by
  rw [tensorNode_coBispinorDown p]
  rw [contr_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <| tensorNode_coBispinorUp p]

set_option maxRecDepth 5000 in
lemma contrBispinorDown_eq_pauliCoDown_contr (p : complexContr) :
    {contrBispinorDown p | α β = pauliCoDown | μ α β ⊗ p | μ}ᵀ := by
  conv =>
    rhs
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_fst <|
      pauliCoDown_eq_metric_mul_pauliCo]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_perm_left _ _ _ _]
    rw [perm_tensor_eq <| perm_contr_congr 2 2]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_prod _ _ _]
    rw [perm_tensor_eq <| perm_contr_congr 2 2]
    rw [perm_perm]
    apply (perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| perm_eq_id _ rfl _).trans
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| contr_prod _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr_congr 1 3]
    rw [perm_tensor_eq <| perm_contr_congr 2 2]
    rw [perm_perm]
    erw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <|
      perm_eq_id _ rfl _]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <|
      prod_assoc' _ _ _ _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| perm_contr_congr 0 4]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr_congr 1 3]
    rw [perm_tensor_eq <| perm_contr_congr 2 2]
    rw [perm_perm]
  conv =>
    lhs
    rw [contrBispinorDown_expand p]
    rw [contr_tensor_eq <| contr_tensor_eq <| prod_contr _ _ _]
    rw [contr_tensor_eq <| perm_contr_congr 0 3]
    rw [perm_contr_congr 1 2]
    apply (perm_tensor_eq <| contr_tensor_eq <| contr_contr _ _ _).trans
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_contr _ _ _]
    rw [perm_perm]
  apply perm_congr _ rfl
  decide

set_option maxRecDepth 5000 in
lemma coBispinorDown_eq_pauliContrDown_contr (p : complexCo) :
    {coBispinorDown p | α β = pauliContrDown | μ α β ⊗ p | μ}ᵀ := by
  conv =>
    rhs
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_fst <|
      pauliContrDown_eq_metric_mul_pauliContr]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_perm_left _ _ _ _]
    rw [perm_tensor_eq <| perm_contr_congr 2 2]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_prod _ _ _]
    rw [perm_tensor_eq <| perm_contr_congr 2 2]
    rw [perm_perm]
    apply (perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| perm_eq_id _ rfl _).trans
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| contr_prod _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr_congr 1 3]
    rw [perm_tensor_eq <| perm_contr_congr 2 2]
    rw [perm_perm]
    erw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <|
      perm_eq_id _ rfl _]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <|
      prod_assoc' _ _ _ _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| perm_contr_congr 0 4]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr_congr 1 3]
    rw [perm_tensor_eq <| perm_contr_congr 2 2]
    rw [perm_perm]
  conv =>
    lhs
    rw [coBispinorDown_expand p]
    rw [contr_tensor_eq <| contr_tensor_eq <| prod_contr _ _ _]
    rw [contr_tensor_eq <| perm_contr_congr 0 3]
    rw [perm_contr_congr 1 2]
    apply (perm_tensor_eq <| contr_tensor_eq <| contr_contr _ _ _).trans
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_contr _ _ _]
    rw [perm_perm]
  apply perm_congr _ rfl
  decide

end complexLorentzTensor
end
