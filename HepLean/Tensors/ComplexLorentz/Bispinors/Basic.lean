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

/-- A bispinor `pᵃᵃ` created from a lorentz vector  `p^μ`. -/
def contrBispinorUp (p : complexContr) :=
  {p | μ ⊗ pauliCo | μ α β}ᵀ.tensor

/-- A bispinor `pₐₐ` created from a lorentz vector  `p^μ`. -/
def bispinorDown (p : complexContr) :=
  {Fermion.altRightMetric | β β' ⊗ Fermion.altLeftMetric | α α' ⊗
    (complexContr.bispinorUp p) | α β}ᵀ.tensor

end complexLorentzTensor
end
