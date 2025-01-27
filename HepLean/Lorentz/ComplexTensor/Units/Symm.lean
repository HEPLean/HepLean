/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.ComplexTensor.Metrics.Basis
import HepLean.Lorentz.ComplexTensor.Units.Basic
/-!

## Symmetry lemmas relating to units

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

/-!

## Symmetry properties

-/

informal_lemma coContrUnit_symm where
  math := "Swapping indices of coContrUnit returns contrCoUnit, i.e. {δ' | μ ν = δ | ν μ}.ᵀ"
  deps := [``coContrUnit, ``contrCoUnit]

informal_lemma contrCoUnit_symm where
  math := "Swapping indices of contrCoUnit returns coContrUnit, i.e. {δ | μ ν = δ' | ν μ}ᵀ"
  deps := [``contrCoUnit, ``coContrUnit]

informal_lemma altLeftLeftUnit_symm where
  math := "Swapping indices of altLeftLeftUnit returns leftAltLeftUnit, i.e.
    {δL' | α α' = δL | α' α}ᵀ"
  deps := [``altLeftLeftUnit, ``leftAltLeftUnit]

informal_lemma leftAltLeftUnit_symm where
  math := "Swapping indices of leftAltLeftUnit returns altLeftLeftUnit, i.e.
    {δL | α α' = δL' | α' α}ᵀ"
  deps := [``leftAltLeftUnit, ``altLeftLeftUnit]

informal_lemma altRightRightUnit_symm where
  math := "Swapping indices of altRightRightUnit returns rightAltRightUnit, i.e.
    {δR' | β β' = δR | β' β}ᵀ"
  deps := [``altRightRightUnit, ``rightAltRightUnit]

informal_lemma rightAltRightUnit_symm where
  math := "Swapping indices of rightAltRightUnit returns altRightRightUnit, i.e.
    {δR | β β' = δR' | β' β}ᵀ"
  deps := [``rightAltRightUnit, ``altRightRightUnit]

end complexLorentzTensor
