/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.MinkowskiMetric
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
/-!
# Spacetime as a self-adjoint matrix

There is a linear equivalence between the vector space of space-time points
and the vector space of 2×2-complex self-adjoint matrices.

In this file we define this linear equivalence in `toSelfAdjointMatrix`.

-/
/-! TODO: Generalize rep of Lorentz vector as a self-adjoint matrix to arbitrary dimension. -/
namespace SpaceTime

open Matrix
open MatrixGroups
open Complex

/-- A 2×2-complex matrix formed from a space-time point. -/
@[simp]
def toMatrix (x : LorentzVector 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![x.time + x.space 2, x.space 0 - x.space 1 * I; x.space 0 + x.space 1 * I, x.time - x.space 2]

/-- The matrix `x.toMatrix` for `x ∈ spaceTime` is self adjoint. -/
lemma toMatrix_isSelfAdjoint (x : LorentzVector 3) : IsSelfAdjoint (toMatrix x) := by
  rw [isSelfAdjoint_iff, star_eq_conjTranspose, ← Matrix.ext_iff]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, conj_ofReal]
  rfl

/-- A self-adjoint matrix formed from a space-time point. -/
@[simps!]
def toSelfAdjointMatrix' (x : LorentzVector 3) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨toMatrix x, toMatrix_isSelfAdjoint x⟩

/-- A self-adjoint matrix formed from a space-time point. -/
@[simp]
noncomputable def fromSelfAdjointMatrix' (x : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    LorentzVector 3 := fun i =>
  match i with
  | Sum.inl 0 => 1/2 * (x.1 0 0 + x.1 1 1).re
  | Sum.inr 0 => (x.1 1 0).re
  | Sum.inr 1 => (x.1 1 0).im
  | Sum.inr 2 => 1/2 * (x.1 0 0 - x.1 1 1).re

/-- The linear equivalence between the vector-space `spaceTime` and self-adjoint
  2×2-complex matrices. -/
noncomputable def toSelfAdjointMatrix :
    LorentzVector 3 ≃ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun := toSelfAdjointMatrix'
  invFun := fromSelfAdjointMatrix'
  left_inv x := by
    funext i
    match i with
    | Sum.inl 0 =>
      simp [fromSelfAdjointMatrix', toSelfAdjointMatrix', toMatrix, toMatrix_isSelfAdjoint]
      ring_nf
    | Sum.inr 0 =>
      simp [fromSelfAdjointMatrix', toSelfAdjointMatrix', toMatrix, toMatrix_isSelfAdjoint]
    | Sum.inr 1 =>
      simp [fromSelfAdjointMatrix', toSelfAdjointMatrix', toMatrix, toMatrix_isSelfAdjoint]
    | Sum.inr 2 =>
      simp [fromSelfAdjointMatrix', toSelfAdjointMatrix', toMatrix, toMatrix_isSelfAdjoint]
      ring
  right_inv x := by
    simp only [toSelfAdjointMatrix', toMatrix, LorentzVector.time, fromSelfAdjointMatrix', one_div,
      Fin.isValue, add_re, ofReal_mul, ofReal_inv, ofReal_ofNat, ofReal_add, LorentzVector.space,
      Function.comp_apply, sub_re, ofReal_sub, re_add_im]
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
    fin_cases i <;> fin_cases j
    · rw [show (x + y) (Sum.inl 0) = x (Sum.inl 0) + y (Sum.inl 0) from rfl]
      rw [show (x + y) (Sum.inr 2) = x (Sum.inr 2) + y (Sum.inr 2) from rfl]
      simp only [Fin.isValue, ofReal_add, Fin.zero_eta, cons_val_zero]
      ring
    · rw [show (x + y) (Sum.inr 0) = x (Sum.inr 0) + y (Sum.inr 0) from rfl]
      rw [show (x + y) (Sum.inr 1) = x (Sum.inr 1) + y (Sum.inr 1) from rfl]
      simp only [Fin.isValue, ofReal_add, Fin.mk_one, cons_val_one, head_cons, Fin.zero_eta,
        cons_val_zero]
      ring
    · rw [show (x + y) (Sum.inr 0) = x (Sum.inr 0) + y (Sum.inr 0) from rfl]
      rw [show (x + y) (Sum.inr 1) = x (Sum.inr 1) + y (Sum.inr 1) from rfl]
      simp only [Fin.isValue, ofReal_add, Fin.zero_eta, cons_val_zero, Fin.mk_one, cons_val_one,
        head_fin_const]
      ring
    · rw [show (x + y) (Sum.inl 0) = x (Sum.inl 0) + y (Sum.inl 0) from rfl]
      rw [show (x + y) (Sum.inr 2) = x (Sum.inr 2) + y (Sum.inr 2) from rfl]
      simp only [Fin.isValue, ofReal_add, Fin.mk_one, cons_val_one, head_cons, head_fin_const]
      ring
  map_smul' r x := by
    ext i j : 2
    simp only [toSelfAdjointMatrix'_coe, Fin.isValue, of_apply, cons_val', empty_val',
      cons_val_fin_one, RingHom.id_apply, selfAdjoint.val_smul, smul_apply, real_smul]
    fin_cases i <;> fin_cases j
    · rw [show (r • x) (Sum.inl 0) = r * x (Sum.inl 0)  from rfl]
      rw [show (r • x) (Sum.inr 2) = r * x (Sum.inr 2)  from rfl]
      simp only [Fin.isValue, ofReal_mul, Fin.zero_eta, cons_val_zero]
      ring
    · rw [show (r • x) (Sum.inr 0) = r * x (Sum.inr 0)  from rfl]
      rw [show (r • x) (Sum.inr 1) = r * x (Sum.inr 1)  from rfl]
      simp only [Fin.isValue, ofReal_mul, Fin.mk_one, cons_val_one, head_cons, Fin.zero_eta,
        cons_val_zero]
      ring
    · rw [show (r • x) (Sum.inr 0) = r * x (Sum.inr 0)  from rfl]
      rw [show (r • x) (Sum.inr 1) = r * x (Sum.inr 1)  from rfl]
      simp only [Fin.isValue, ofReal_mul, Fin.zero_eta, cons_val_zero, Fin.mk_one, cons_val_one,
        head_fin_const]
      ring
    · rw [show (r • x) (Sum.inl 0) = r * x (Sum.inl 0)  from rfl]
      rw [show (r • x) (Sum.inr 2) = r * x (Sum.inr 2)  from rfl]
      simp only [Fin.isValue, ofReal_mul, Fin.mk_one, cons_val_one, head_cons, head_fin_const]
      ring

open minkowskiMetric in
lemma det_eq_ηLin (x : LorentzVector 3) : det (toSelfAdjointMatrix x).1 = ⟪x, x⟫ₘ := by
  simp only [toSelfAdjointMatrix, LinearEquiv.coe_mk, toSelfAdjointMatrix'_coe, Fin.isValue,
    det_fin_two_of, eq_time_minus_inner_prod, LorentzVector.time, LorentzVector.space,
    PiLp.inner_apply, Function.comp_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    ofReal_sub, ofReal_mul, ofReal_add]
  ring_nf
  simp only [Fin.isValue, I_sq, mul_neg, mul_one]
  ring

end SpaceTime
