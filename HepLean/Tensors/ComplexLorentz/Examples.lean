/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
import HepLean.Tensors.ComplexLorentz.TensorStruct
import HepLean.Tensors.Tree.Elab
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

def upDown : Fin 2 → complexLorentzTensor.C
  | 0 => Fermion.Color.up
  | 1 => Fermion.Color.down

variable (T S : complexLorentzTensor.F.obj (OverColor.mk upDown))

#check {T | i i}ᵀ.dot
end complexLorentzTensor

end
