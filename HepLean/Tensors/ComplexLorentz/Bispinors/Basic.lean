/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.ComplexLorentz.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HepLean.Tensors.Tree.NodeIdentities.Basic
import HepLean.Tensors.Tree.NodeIdentities.PermProd
import HepLean.Tensors.Tree.NodeIdentities.PermContr
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.ContrContr
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
namespace Lorentz
namespace complexContr

/-- A bispinor `pᵃᵃ` created from a lorentz vector  `p^μ`. -/
def bispinorUp (p : complexContr) :=
  {p | μ ⊗ (Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | ν α β)}ᵀ.tensor

/-- A bispinor `pₐₐ` created from a lorentz vector  `p^μ`. -/
def bispinorDown (p : complexContr) :=
  {Fermion.altRightMetric | β β' ⊗ Fermion.altLeftMetric | α α' ⊗
    (complexContr.bispinorUp p) | α β}ᵀ.tensor

end complexContr
end Lorentz
end
