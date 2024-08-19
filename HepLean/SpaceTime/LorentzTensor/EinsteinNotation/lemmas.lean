/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/

import HepLean.SpaceTime.LorentzTensor.EinsteinNotation.IndexNotation
/-!

# Lemmas regarding Einstein tensors


-/
namespace einsteinTensor

open einsteinTensorColor
open IndexNotation IndexString
open TensorStructure TensorIndex


variable {R : Type} [CommSemiring R] {n m : ℕ}
/-lemma swap_eq_transpose (T : (einsteinTensor R n).Tensor ![Unit.unit, Unit.unit]) :
     (T|"ᵢ₁ᵢ₂") ≈ ((toMatrix.symm (toMatrix T).transpose)|"ᵢ₂ᵢ₁") := by
  apply And.intro
  · apply And.intro
    simp only [toTensorColor_eq, indexNotation_eq_color, ColorIndexList.contr, fromIndexStringColor,
      mkDualMap, decidableEq_eq_color]
    decide
    simp only [toTensorColor_eq, indexNotation_eq_color, ColorIndexList.contr, fromIndexStringColor,
      mkDualMap, decidableEq_eq_color, ColorIndexList.colorMap']
    decide
  intro h -/

end einsteinTensor
