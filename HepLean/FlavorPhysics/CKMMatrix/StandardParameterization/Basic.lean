/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Rows
import HepLean.FlavorPhysics.CKMMatrix.Invariants
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
/-!
# Standard parameterization for the CKM Matrix

This file defines the standard parameterization of CKM matrices in terms of
four real numbers `θ₁₂`, `θ₁₃`, `θ₂₃` and `δ₁₃`.

We will show that every CKM matrix can be written within this standard parameterization
in the file `FlavorPhysics.CKMMatrix.StandardParameters`.

-/
open Matrix Complex
open ComplexConjugate
open CKMMatrix

noncomputable section

/-- Given four reals `θ₁₂ θ₁₃ θ₂₃ δ₁₃` the standard parameterization of the CKM matrix
as a `3×3` complex matrix. -/
def standParamAsMatrix (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![Real.cos θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₃ * exp (-I * δ₁₃)],
    ![(-Real.sin θ₁₂ * Real.cos θ₂₃) - (Real.cos θ₁₂ * Real.sin θ₁₃ * Real.sin θ₂₃ * exp (I * δ₁₃)),
      Real.cos θ₁₂ * Real.cos θ₂₃ - Real.sin θ₁₂ * Real.sin θ₁₃ * Real.sin θ₂₃ * exp (I * δ₁₃),
      Real.sin θ₂₃ * Real.cos θ₁₃],
    ![Real.sin θ₁₂ * Real.sin θ₂₃ - Real.cos θ₁₂ * Real.sin θ₁₃ * Real.cos θ₂₃ * exp (I * δ₁₃),
      (-Real.cos θ₁₂ * Real.sin θ₂₃) - (Real.sin θ₁₂ * Real.sin θ₁₃ * Real.cos θ₂₃ * exp (I * δ₁₃)),
      Real.cos θ₂₃ * Real.cos θ₁₃]]

open CKMMatrix

lemma standParamAsMatrix_unitary (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) :
    ((standParamAsMatrix θ₁₂ θ₁₃ θ₂₃ δ₁₃)ᴴ * standParamAsMatrix θ₁₂ θ₁₃ θ₂₃ δ₁₃) = 1 := by
  funext j i
  simp only [standParamAsMatrix, neg_mul, Fin.isValue]
  rw [mul_apply]
  have h1 := exp_ne_zero (I * ↑δ₁₃)
  fin_cases j <;> rw [Fin.sum_univ_three]
  simp only [Fin.zero_eta, Fin.isValue, conjTranspose_apply, cons_val', cons_val_zero, empty_val',
    cons_val_fin_one, star_mul', RCLike.star_def, conj_ofReal, cons_val_one, head_cons, star_sub,
    star_neg, ← exp_conj, _root_.map_mul, conj_I, neg_mul, cons_val_two, tail_cons, head_fin_const]
  simp [conj_ofReal]
  rw [exp_neg]
  fin_cases i <;> simp
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq, sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq]
    ring
  simp only [Fin.mk_one, Fin.isValue, conjTranspose_apply, cons_val', cons_val_one, head_cons,
    empty_val', cons_val_fin_one, cons_val_zero, star_mul', RCLike.star_def, conj_ofReal, star_sub,
    ← exp_conj, _root_.map_mul, conj_I, neg_mul, cons_val_two, tail_cons, head_fin_const, star_neg]
  simp [conj_ofReal]
  rw [exp_neg]
  fin_cases i <;> simp
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq, sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq]
    ring
  simp only [Fin.reduceFinMk, Fin.isValue, conjTranspose_apply, cons_val', cons_val_two, tail_cons,
    head_cons, empty_val', cons_val_fin_one, cons_val_zero, star_mul', RCLike.star_def, conj_ofReal,
    ← exp_conj, map_neg, _root_.map_mul, conj_I, neg_mul, neg_neg, cons_val_one, head_fin_const]
  simp [conj_ofReal]
  rw [exp_neg]
  fin_cases i <;> simp
  · ring_nf
    rw [sin_sq]
    ring
  · ring_nf
    rw [sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq]
    ring

/-- A CKM Matrix from four reals `θ₁₂`, `θ₁₃`, `θ₂₃`, and `δ₁₃`. This is the standard
  parameterization of CKM matrices. -/
def standParam (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) : CKMMatrix :=
  ⟨standParamAsMatrix θ₁₂ θ₁₃ θ₂₃ δ₁₃, by
   rw [mem_unitaryGroup_iff']
   exact standParamAsMatrix_unitary θ₁₂ θ₁₃ θ₂₃ δ₁₃⟩

namespace standParam
lemma cross_product_t (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) :
    [standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃]t =
    (conj [standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃]u ×₃ conj [standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃]c) := by
  have h1 := exp_ne_zero (I * ↑δ₁₃)
  funext i
  fin_cases i
  · simp only [tRow, standParam, standParamAsMatrix, neg_mul, exp_neg,
    Fin.isValue, cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_two, tail_cons,
    head_fin_const, cons_val_one, head_cons, Fin.zero_eta, crossProduct, uRow, cRow,
    LinearMap.mk₂_apply, Pi.conj_apply, _root_.map_mul, map_inv₀, ← exp_conj, conj_I, conj_ofReal,
    inv_inv, map_sub, map_neg]
    field_simp
    ring_nf
    rw [sin_sq]
    ring
  · simp only [tRow, standParam, standParamAsMatrix, neg_mul, exp_neg, Fin.isValue, cons_val',
    cons_val_zero, empty_val', cons_val_fin_one, cons_val_two, tail_cons, head_fin_const,
    cons_val_one, head_cons, Fin.mk_one, crossProduct, uRow, cRow, LinearMap.mk₂_apply,
    Pi.conj_apply, _root_.map_mul, conj_ofReal, map_inv₀, ← exp_conj, conj_I, inv_inv, map_sub,
    map_neg]
    field_simp
    ring_nf
    rw [sin_sq]
    ring
  · simp only [tRow, standParam, standParamAsMatrix, neg_mul, exp_neg, Fin.isValue,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_two, tail_cons, head_fin_const,
    cons_val_one, head_cons, Fin.reduceFinMk, crossProduct, uRow, cRow, LinearMap.mk₂_apply,
    Pi.conj_apply, _root_.map_mul, conj_ofReal, map_inv₀, ← exp_conj, conj_I, inv_inv, map_sub,
    map_neg]
    field_simp
    ring_nf
    rw [sin_sq]
    ring

lemma eq_rows (U : CKMMatrix) {θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ} (hu : [U]u = [standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃]u)
    (hc : [U]c = [standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃]c) (hU : [U]t = conj [U]u ×₃ conj [U]c) :
    U = standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃ := by
  apply ext_Rows hu hc
  rw [hU, cross_product_t, hu, hc]

lemma eq_exp_of_phases (θ₁₂ θ₁₃ θ₂₃ δ₁₃ δ₁₃' : ℝ) (h : cexp (δ₁₃ * I) = cexp (δ₁₃' * I)) :
    standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃ = standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃' := by
  simp [standParam, standParamAsMatrix]
  apply CKMMatrix_ext
  simp only
  rw [show exp (I * δ₁₃) = exp (I * δ₁₃') by rw [mul_comm, h, mul_comm]]
  rw [show cexp (-(I * ↑δ₁₃)) = cexp (-(I * ↑δ₁₃')) by rw [exp_neg, exp_neg, mul_comm, h, mul_comm]]

open Invariant in
lemma VusVubVcdSq_eq (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) (h1 : 0 ≤ Real.sin θ₁₂)
    (h2 : 0 ≤ Real.cos θ₁₃) (h3 : 0 ≤ Real.sin θ₂₃) (h4 : 0 ≤ Real.cos θ₁₂) :
    VusVubVcdSq ⟦standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃⟧ =
    Real.sin θ₁₂ ^ 2 * Real.cos θ₁₃ ^ 2 * Real.sin θ₁₃ ^ 2 * Real.sin θ₂₃ ^ 2 := by
  simp only [VusVubVcdSq, VusAbs, VAbs, VAbs', Fin.isValue, standParam, standParamAsMatrix,
     neg_mul, Quotient.lift_mk, cons_val', cons_val_one, head_cons,
    empty_val', cons_val_fin_one, cons_val_zero, _root_.map_mul, VubAbs, cons_val_two, tail_cons,
    VcbAbs, VudAbs, Complex.abs_ofReal]
  by_cases hx : Real.cos θ₁₃ ≠ 0
  · rw [Complex.abs_exp]
    simp only [neg_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
      neg_zero, Real.exp_zero, mul_one, _root_.sq_abs]
    rw [_root_.abs_of_nonneg h1, _root_.abs_of_nonneg h3, _root_.abs_of_nonneg h2,
      _root_.abs_of_nonneg h4]
    simp [sq]
    ring_nf
    nth_rewrite 2 [Real.sin_sq θ₁₂]
    ring_nf
    field_simp
    ring
  · simp at hx
    rw [hx]
    simp

open Invariant in
lemma mulExpδ₁₃_eq (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) (h1 : 0 ≤ Real.sin θ₁₂)
    (h2 : 0 ≤ Real.cos θ₁₃) (h3 : 0 ≤ Real.sin θ₂₃) (h4 : 0 ≤ Real.cos θ₁₂) :
    mulExpδ₁₃ ⟦standParam θ₁₂ θ₁₃ θ₂₃ δ₁₃⟧ =
    sin θ₁₂ * cos θ₁₃ ^ 2 * sin θ₂₃ * sin θ₁₃ * cos θ₁₂ * cos θ₂₃ * cexp (I * δ₁₃) := by
  rw [mulExpδ₁₃, VusVubVcdSq_eq _ _ _ _ h1 h2 h3 h4]
  simp only [jarlskogℂ, standParam, standParamAsMatrix, neg_mul,
    Quotient.lift_mk, jarlskogℂCKM, Fin.isValue, cons_val', cons_val_one, head_cons,
    empty_val', cons_val_fin_one, cons_val_zero, cons_val_two, tail_cons, _root_.map_mul, ←
    exp_conj, map_neg, conj_I, conj_ofReal, neg_neg, map_sub]
  simp only [ofReal_sin, ofReal_cos, ofReal_mul, ofReal_pow]
  ring_nf
  rw [exp_neg]
  have h1 : cexp (I * δ₁₃) ≠ 0 := exp_ne_zero _
  field_simp

end standParam
end
