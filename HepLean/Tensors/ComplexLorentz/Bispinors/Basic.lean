/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.ComplexLorentz.PauliLower
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

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p^μ`. -/
def contrBispinorUp (p : complexContr) :=
  {p | μ ⊗ pauliCo | μ α β}ᵀ.tensor

lemma tensorNode_contrBispinorUp (p : complexContr) :
    (tensorNode (contrBispinorUp p)).tensor = {p | μ ⊗ pauliCo | μ α β}ᵀ.tensor := by
  rw [contrBispinorUp, tensorNode_tensor]

/-- A bispinor `pₐₐ` created from a lorentz vector `p^μ`. -/
def contrBispinorDown (p : complexContr) :=
  {Fermion.altLeftMetric | α α' ⊗ Fermion.altRightMetric | β β' ⊗
    (contrBispinorUp p) | α β}ᵀ.tensor

/-- Expands the tensor node of `contrBispinorDown` into a tensor tree based on
  `contrBispinorUp`. -/
lemma tensorNode_contrBispinorDown (p : complexContr) :
    {contrBispinorDown p | α β}ᵀ.tensor = {Fermion.altLeftMetric | α α' ⊗
    Fermion.altRightMetric | β β' ⊗ (contrBispinorUp p) | α β}ᵀ.tensor := by
  rw [contrBispinorDown, tensorNode_tensor]

/-- Expansion of a `contrBispinorDown` into the original contravariant tensor nested
  between pauli matrices and metrics. -/
lemma contrBispinorDown_full_nested (p : complexContr) :
    {contrBispinorDown p | α β}ᵀ.tensor = {Fermion.altLeftMetric | α α' ⊗
    Fermion.altRightMetric | β β' ⊗ (p | μ ⊗ pauliCo | μ α β)}ᵀ.tensor := by
  conv =>
    lhs
    rw [tensorNode_contrBispinorDown]
    rw [contr_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <| tensorNode_contrBispinorUp p]

end complexLorentzTensor
end
