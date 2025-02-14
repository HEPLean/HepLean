/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Lorentz.ComplexTensor.Metrics.Basis
import PhysLean.Lorentz.ComplexTensor.Units.Basic
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

/-- Swapping indices of `coContrUnit` returns `contrCoUnit`: `{δ' | μ ν = δ | ν μ}ᵀ`. -/
informal_lemma coContrUnit_symm where
  deps := [``coContrUnit, ``contrCoUnit]

/-- Swapping indices of `contrCoUnit` returns `coContrUnit`: `{δ | μ ν = δ' | ν μ}ᵀ`. -/
informal_lemma contrCoUnit_symm where
  deps := [``contrCoUnit, ``coContrUnit]

/-- Swapping indices of `altLeftLeftUnit` returns `leftAltLeftUnit`: `{δL' | α α' = δL | α' α}ᵀ`. -/
informal_lemma altLeftLeftUnit_symm where
  deps := [``altLeftLeftUnit, ``leftAltLeftUnit]

/-- Swapping indices of `leftAltLeftUnit` returns `altLeftLeftUnit`: `{δL | α α' = δL' | α' α}ᵀ`. -/
informal_lemma leftAltLeftUnit_symm where
  deps := [``leftAltLeftUnit, ``altLeftLeftUnit]

/-- Swapping indices of `altRightRightUnit` returns `rightAltRightUnit`:
`{δR' | β β' = δR | β' β}ᵀ`.
-/
informal_lemma altRightRightUnit_symm where
  deps := [``altRightRightUnit, ``rightAltRightUnit]

/-- Swapping indices of `rightAltRightUnit` returns `altRightRightUnit`:
`{δR | β β' = δR' | β' β}ᵀ`.
-/
informal_lemma rightAltRightUnit_symm where
  deps := [``rightAltRightUnit, ``altRightRightUnit]

end complexLorentzTensor
