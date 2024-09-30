/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.BeyondTheStandardModel.TwoHDM.Basic
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
  defined by ((Φ₁^†Φ₁, Φ₂^†Φ₁), (Φ₁^†Φ₂, Φ₂^†Φ₂)). -/
def prodMatrix (Φ1 Φ2 : HiggsField) (x : SpaceTime) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟪Φ1, Φ1⟫_H x, ⟪Φ2, Φ1⟫_H x; ⟪Φ1, Φ2⟫_H x, ⟪Φ2, Φ2⟫_H x]

/-- The matrix `prodMatrix` is hermitian. -/
lemma prodMatrix_hermitian (Φ1 Φ2 : HiggsField) (x : SpaceTime) :
    (prodMatrix Φ1 Φ2 x).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [prodMatrix]
  · simp only [prodMatrix, innerProd, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two,
    Fin.isValue, Fin.zero_eta, Fin.mk_one, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_one, Matrix.head_fin_const, star_add, star_mul', RCLike.star_def,
    RingHomCompTriple.comp_apply, RingHom.id_apply, Matrix.head_cons]
    ring
  · simp only [prodMatrix, innerProd, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two,
    Fin.isValue, Fin.mk_one, Fin.zero_eta, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, star_add, star_mul', RCLike.star_def,
    RingHomCompTriple.comp_apply, RingHom.id_apply, Matrix.head_fin_const]
    ring
  · simp [prodMatrix]

informal_lemma prodMatrix_positive_semidefinite where
  math :≈ "For all x in ``SpaceTime, ``prodMatrix at `x` is positive semidefinite."
  deps :≈ [``prodMatrix, ``SpaceTime]

informal_lemma prodMatrix_smooth where
  math :≈ "The map ``prodMatrix is a smooth function on spacetime."
  deps :≈ [``prodMatrix]

end
end TwoHDM
