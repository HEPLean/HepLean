/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
/-!

# Parity operator

-/

namespace QuantumMechanics

namespace OneDimension
noncomputable section

namespace HilbertSpace
open MeasureTheory

/-- The parity operator is defined as linear map from `ℝ → ℂ` to itself, such that
  `ψ` is taken to `fun x => ψ (-x)`. -/
def parity : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun ψ := fun x => ψ (-x)
  map_add' ψ1 ψ2 := by
    funext x
    simp
  map_smul' a ψ1 := by
    funext x
    simp

/-- The parity operator acting on a member of the Hilbert space is in Hilbert space. -/
lemma memHS_of_parity (ψ : ℝ → ℂ) (hψ : MemHS ψ) : MemHS (parity ψ) := by
  simp only [parity, LinearMap.coe_mk, AddHom.coe_mk]
  rw [memHS_iff] at hψ ⊢
  apply And.intro
  · rw [show (fun x => ψ (-x)) = ψ ∘ (λ x => -x) by funext x; simp]
    exact MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving hψ.left <|
      quasiMeasurePreserving_neg_of_right_invariant volume
  · simpa using (integrable_comp_mul_left_iff
      (fun x => ‖ψ (x)‖ ^ 2) (R := (-1 : ℝ)) (by simp)).mpr hψ.right

end HilbertSpace
