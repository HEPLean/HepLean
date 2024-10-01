/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.BeyondTheStandardModel.TwoHDM.Basic
import HepLean.StandardModel.HiggsBoson.GaugeAction
import Mathlib.LinearAlgebra.Matrix.PosDef
/-!

# Gauge orbits for the 2HDM

The main reference for material in this section is https://arxiv.org/pdf/hep-ph/0605184.

-/

namespace TwoHDM

open StandardModel
open ComplexConjugate
open HiggsField

noncomputable section

/-- For two Higgs fields `Φ₁` and `Φ₂`, the map from space time to 2 x 2 complex matrices
  defined by `((Φ₁^†Φ₁, Φ₂^†Φ₁), (Φ₁^†Φ₂, Φ₂^†Φ₂))`. -/
def prodMatrix (Φ1 Φ2 : HiggsField) (x : SpaceTime) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟪Φ1, Φ1⟫_H x, ⟪Φ2, Φ1⟫_H x; ⟪Φ1, Φ2⟫_H x, ⟪Φ2, Φ2⟫_H x]

/-- The 2 x 2 complex matrices made up of components of the two Higgs fields. -/
def fieldCompMatrix (Φ1 Φ2 : HiggsField) (x : SpaceTime) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Φ1 x 0, Φ1 x 1; Φ2 x 0, Φ2 x 1]

/-- The matrix `prodMatrix Φ1 Φ2 x` is equal to the square of `fieldCompMatrix Φ1 Φ2 x`. -/
lemma prodMatrix_eq_fieldCompMatrix_sq (Φ1 Φ2 : HiggsField) (x : SpaceTime) :
    prodMatrix Φ1 Φ2 x = fieldCompMatrix Φ1 Φ2 x * (fieldCompMatrix Φ1 Φ2 x).conjTranspose := by
  rw [fieldCompMatrix]
  trans !![Φ1 x 0, Φ1 x 1; Φ2 x 0, Φ2 x 1] *
    !![conj (Φ1 x 0), conj (Φ2 x 0); conj (Φ1 x 1), conj (Φ2 x 1)]
  · rw [Matrix.mul_fin_two, prodMatrix, innerProd_expand', innerProd_expand', innerProd_expand',
      innerProd_expand']
    funext i j
    fin_cases i <;> fin_cases j <;> ring_nf
  · funext i j
    fin_cases i <;> fin_cases j <;> rfl

/-- An instance of `PartialOrder` on `ℂ` defined through `Complex.partialOrder`. -/
local instance : PartialOrder ℂ := Complex.partialOrder

/-- The matrix `prodMatrix` is positive semi-definite. -/
lemma prodMatrix_posSemiDef (Φ1 Φ2 : HiggsField) (x : SpaceTime) :
    (prodMatrix Φ1 Φ2 x).PosSemidef := by
  rw [Matrix.posSemidef_iff_eq_transpose_mul_self]
  use (fieldCompMatrix Φ1 Φ2 x).conjTranspose
  simpa using prodMatrix_eq_fieldCompMatrix_sq Φ1 Φ2 x

/-- The matrix `prodMatrix` is hermitian. -/
lemma prodMatrix_hermitian (Φ1 Φ2 : HiggsField) (x : SpaceTime) :
    (prodMatrix Φ1 Φ2 x).IsHermitian := (prodMatrix_posSemiDef Φ1 Φ2 x).isHermitian

informal_lemma prodMatrix_smooth where
  math :≈ "The map ``prodMatrix is a smooth function on spacetime."
  deps :≈ [``prodMatrix]

informal_lemma prodMatrix_invariant where
  math :≈ "The map ``prodMatrix is invariant under the simultanous action of ``gaugeAction
   on the two Higgs fields."
  deps :≈ [``prodMatrix, ``gaugeAction]

end
end TwoHDM
