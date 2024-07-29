/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Contractions
/-!

# Structure for Rising and Lowering indices

-/

noncomputable section

open TensorProduct

variable {R : Type} [CommSemiring R]

/-- Structure extending `TensorStructure` with the addition of a metric
  permitting to `rise` and `lower` indices. -/
structure DualizeTensorStructure (R : Type) [CommSemiring R] extends TensorStructure R where
  /-- The metric for a given color. -/
  metric : Color → ColorModule (τ μ) ⊗[R] ColorModule (τ μ)
  /-- The metric contracted with its dual is the unit. -/
  metric_dual : ∀ μ,
    TensorProduct.congr (LinearEquiv.refl _ _) (toTensorStructure.colorModuleCast (τ_involutive μ))
    (toTensorStructure.contrTwoTwo (metric μ ⊗ₜ[R] metric (τ μ))) = unit μ

end
