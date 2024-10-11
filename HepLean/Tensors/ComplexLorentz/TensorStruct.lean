/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
import HepLean.Tensors.ComplexLorentz.ColorFun
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

/-- The tensor structure for complex Lorentz tensors. -/
def complexLorentzTensor : TensorStruct where
  C := Fermion.Color
  G := SL(2, ℂ)
  G_group := inferInstance
  k := ℂ
  k_commRing := inferInstance
  F := Fermion.colorFunMon
  τ := Fermion.τ
  evalNo := Fermion.evalNo

end
