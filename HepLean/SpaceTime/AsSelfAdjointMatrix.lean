/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Metric
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
/-!
# Spacetime as a self-adjoint matrix

There is a linear equivalence between the vector space of space-time points
and the vector space of 2×2-complex self-adjoint matrices.

In this file we define this linear equivalence in `toSelfAdjointMatrix`.

-/
namespace SpaceTime

open Matrix
open MatrixGroups
open Complex

/-- A 2×2-complex matrix formed from a space-time point. -/
@[simp]
def toMatrix (x : SpaceTime) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![x 0 + x 3, x 1 - x 2 * I; x 1 + x 2 * I, x 0 - x 3]

/-- The matrix `x.toMatrix` for `x ∈ spaceTime` is self adjoint. -/
lemma toMatrix_isSelfAdjoint (x : SpaceTime) : IsSelfAdjoint x.toMatrix := by
  rw [isSelfAdjoint_iff, star_eq_conjTranspose, ← Matrix.ext_iff]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, conj_ofReal]
  rfl

/-- A self-adjoint matrix formed from a space-time point. -/
@[simps!]
def toSelfAdjointMatrix' (x : SpaceTime) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨x.toMatrix, toMatrix_isSelfAdjoint x⟩

/-- A self-adjoint matrix formed from a space-time point. -/
@[simp]
noncomputable def fromSelfAdjointMatrix' (x : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) : SpaceTime :=
  ![1/2 * (x.1 0 0 + x.1 1 1).re, (x.1 1 0).re, (x.1 1 0).im , (x.1 0 0 - x.1 1 1).re/2]

/-- The linear equivalence between the vector-space `spaceTime` and self-adjoint
  2×2-complex matrices. -/
noncomputable def toSelfAdjointMatrix : SpaceTime ≃ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun := toSelfAdjointMatrix'
  invFun := fromSelfAdjointMatrix'
  left_inv x := by
    simp only [fromSelfAdjointMatrix', one_div, toSelfAdjointMatrix'_coe, of_apply, cons_val',
      cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, head_cons, head_fin_const,
      add_add_sub_cancel, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, add_im, mul_im, zero_add, add_sub_sub_cancel, half_add_self]
    field_simp [SpaceTime]
    ext1 x
    fin_cases x <;> rfl
  right_inv x := by
    simp only [toSelfAdjointMatrix', toMatrix, fromSelfAdjointMatrix', one_div, Fin.isValue, add_re,
      sub_re, cons_val_zero, ofReal_mul, ofReal_inv, ofReal_ofNat, ofReal_add, cons_val_three,
      Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, head_cons, ofReal_div, ofReal_sub,
      cons_val_one, cons_val_two, re_add_im]
    ext i j
    fin_cases i <;> fin_cases j <;>
      field_simp [fromSelfAdjointMatrix', toMatrix, conj_ofReal]
    exact conj_eq_iff_re.mp (congrArg (fun M => M 0 0) $ selfAdjoint.mem_iff.mp x.2 )
    have h01 := congrArg (fun M => M 0 1) $ selfAdjoint.mem_iff.mp x.2
    simp only [Fin.isValue, star_apply, RCLike.star_def] at h01
    rw [← h01, RCLike.conj_eq_re_sub_im]
    rfl
    exact conj_eq_iff_re.mp (congrArg (fun M => M 1 1) $ selfAdjoint.mem_iff.mp x.2 )
  map_add' x y  := by
    ext i j : 2
    simp only [toSelfAdjointMatrix'_coe, add_apply, ofReal_add, of_apply, cons_val', empty_val',
      cons_val_fin_one, AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid, Matrix.add_apply]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' r x := by
    ext i j : 2
    simp only [toSelfAdjointMatrix', toMatrix, Fin.isValue, smul_apply, ofReal_mul,
      RingHom.id_apply]
    fin_cases i <;> fin_cases j <;>
      field_simp [fromSelfAdjointMatrix', toMatrix, conj_ofReal, smul_apply]
       <;> ring

lemma det_eq_ηLin (x : SpaceTime) : det (toSelfAdjointMatrix x).1 = ηLin x x := by
  simp [toSelfAdjointMatrix, ηLin_expand]
  ring_nf
  simp only [Fin.isValue, I_sq, mul_neg, mul_one]
  ring

end SpaceTime
