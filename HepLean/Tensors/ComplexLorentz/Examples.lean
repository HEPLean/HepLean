/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
import HepLean.Tensors.ComplexLorentz.TensorStruct
/-!

## The tensor structure for complex Lorentz tensors

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

noncomputable section

namespace complexLorentzTensor

/-- The color map for a 2d tensor with the first index up and the second index down. -/
def upDown : Fin 2 → complexLorentzTensor.C
  | 0 => Fermion.Color.up
  | 1 => Fermion.Color.down

variable (T S : complexLorentzTensor.F.obj (OverColor.mk upDown))

/-
import HepLean.Tensors.Tree.Elab

#check {T | i m ⊗ S | m l}ᵀ.dot
#check {T | i m ⊗ S | l τ(m)}ᵀ.dot
-/
end complexLorentzTensor

end
