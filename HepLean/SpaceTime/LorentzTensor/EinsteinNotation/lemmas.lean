/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/

import HepLean.SpaceTime.LorentzTensor.EinsteinNotation.IndexNotation
/-!

# Lemmas regarding Einstein tensors


-/
set_option profiler true
namespace einsteinTensor

open einsteinTensorColor
open IndexNotation IndexString
open TensorStructure TensorIndex

variable {R : Type} [CommSemiring R] {n m : ℕ}

/-! TODO: Fix notation here. -/
set_option maxHeartbeats 0
lemma swap_eq_transpose (T : (einsteinTensor R n).Tensor ![Unit.unit, Unit.unit]) :
     (T|"ᵢ₁ᵢ₂") ≈ ((toMatrix.symm (toMatrix T).transpose)|"ᵢ₂ᵢ₁") := by
  apply And.intro
  apply And.intro
  · simp only [toTensorColor_eq, indexNotation_eq_color, ColorIndexList.contr,
      fromIndexStringColor_indexList, IndexList.contrIndexList_length]
    decide
  apply And.intro
  · simp only [toTensorColor_eq, indexNotation_eq_color, ColorIndexList.contr,
      fromIndexStringColor_indexList, IndexList.contrIndexList_length]
    rw [IndexList.withUniqueDualInOther_eq_univ_iff_forall]
    intro x
    have h1 : (toIndexList' "ᵢ₁ᵢ₂" (by decide) : IndexList einsteinTensorColor.Color).contrIndexList.length
      = 2 := by
      decide
    sorry



  sorry

end einsteinTensor
