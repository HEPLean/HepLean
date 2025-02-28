/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Particles.StandardModel.HiggsBoson.Potential
import PhysLean.Meta.TODO.Basic
/-!

# The Two Higgs Doublet Model

The two Higgs doublet model is the standard model plus an additional Higgs doublet.

Currently this file contains the definition of the 2HDM potential.

-/

namespace TwoHDM

open StandardModel
open ComplexConjugate
open HiggsField

noncomputable section

/-- The parameters of the Two Higgs doublet model potential. -/
structure Potential where
  /-- The parameter corresponding to `m₁₁²` in the 2HDM potential. -/
  m₁₁2 : ℝ
  /-- The parameter corresponding to `m₂₂²` in the 2HDM potential. -/
  m₂₂2 : ℝ
  /-- The parameter corresponding to `m₁₂²` in the 2HDM potential. -/
  m₁₂2 : ℂ
  /-- The parameter corresponding to `λ₁` in the 2HDM potential. -/
  𝓵₁ : ℝ
  /-- The parameter corresponding to `λ₂` in the 2HDM potential. -/
  𝓵₂ : ℝ
  /-- The parameter corresponding to `λ₃` in the 2HDM potential. -/
  𝓵₃ : ℝ
  /-- The parameter corresponding to `λ₄` in the 2HDM potential. -/
  𝓵₄ : ℝ
  /-- The parameter corresponding to `λ₅` in the 2HDM potential. -/
  𝓵₅ : ℂ
  /-- The parameter corresponding to `λ₆` in the 2HDM potential. -/
  𝓵₆ : ℂ
  /-- The parameter corresponding to `λ₇` in the 2HDM potential. -/
  𝓵₇ : ℂ

namespace Potential

variable (P : Potential) (Φ1 Φ2 : HiggsField)

/-- The potential of the two Higgs doublet model. -/
def toFun (Φ1 Φ2 : HiggsField) (x : SpaceTime) : ℝ :=
  P.m₁₁2 * ‖Φ1‖_H^2 x + P.m₂₂2 * ‖Φ2‖_H^2 x -
  (P.m₁₂2 * ⟪Φ1, Φ2⟫_H x + conj P.m₁₂2 * ⟪Φ2, Φ1⟫_H x).re
  + 1/2 * P.𝓵₁ * ‖Φ1‖_H^2 x * ‖Φ1‖_H^2 x + 1/2 * P.𝓵₂ * ‖Φ2‖_H^2 x * ‖Φ2‖_H^2 x
  + P.𝓵₃ * ‖Φ1‖_H^2 x * ‖Φ2‖_H^2 x
  + P.𝓵₄ * ‖⟪Φ1, Φ2⟫_H x‖ ^ 2
  + (1/2 * P.𝓵₅ * ⟪Φ1, Φ2⟫_H x ^ 2 + 1/2 * conj P.𝓵₅ * ⟪Φ2, Φ1⟫_H x ^ 2).re
  + (P.𝓵₆ * ‖Φ1‖_H^2 x * ⟪Φ1, Φ2⟫_H x + conj P.𝓵₆ * ‖Φ1‖_H^2 x * ⟪Φ2, Φ1⟫_H x).re
  + (P.𝓵₇ * ‖Φ2‖_H^2 x * ⟪Φ1, Φ2⟫_H x + conj P.𝓵₇ * ‖Φ2‖_H^2 x * ⟪Φ2, Φ1⟫_H x).re

/-- The potential where all parameters are zero. -/
def zero : Potential := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

lemma swap_fields : P.toFun Φ1 Φ2 =
    (Potential.mk P.m₂₂2 P.m₁₁2 (conj P.m₁₂2) P.𝓵₂ P.𝓵₁ P.𝓵₃ P.𝓵₄
    (conj P.𝓵₅) (conj P.𝓵₇) (conj P.𝓵₆)).toFun Φ2 Φ1 := by
  funext x
  simp only [toFun, normSq, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add, one_div, Complex.norm_eq_abs, Complex.inv_re, Complex.re_ofNat,
    Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div,
    zero_mul, sub_zero, Complex.mul_im, add_zero, mul_neg, Complex.ofReal_pow, normSq_apply_re_self,
    normSq_apply_im_zero, mul_zero, zero_add, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring_nf
  simp only [one_div, add_left_inj, add_right_inj, mul_eq_mul_left_iff]
  left
  rw [HiggsField.innerProd, HiggsField.innerProd, ← InnerProductSpace.conj_symm, Complex.abs_conj]

/-- If `Φ₂` is zero the potential reduces to the Higgs potential on `Φ₁`. -/
lemma right_zero : P.toFun Φ1 0 =
    (HiggsField.Potential.mk (- P.m₁₁2) (P.𝓵₁/2)).toFun Φ1 := by
  funext x
  simp only [toFun, normSq, ContMDiffSection.coe_zero, Pi.zero_apply, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, innerProd_right_zero,
    innerProd_left_zero, Complex.zero_re, sub_zero, one_div, Complex.ofReal_pow,
    Complex.ofReal_zero, neg_neg, add_right_inj, mul_eq_mul_right_iff, pow_eq_zero_iff,
    norm_eq_zero, HiggsField.Potential.toFun, or_self_right]
  ring_nf
  simp only [true_or]

/-- If `Φ₁` is zero the potential reduces to the Higgs potential on `Φ₂`. -/
lemma left_zero : P.toFun 0 Φ2 =
    (HiggsField.Potential.mk (- P.m₂₂2) (P.𝓵₂/2)).toFun Φ2 := by
  rw [swap_fields, right_zero]

/-- Negating `Φ₁` is equivalent to negating `m₁₂2`, `𝓵₆` and `𝓵₇`. -/
lemma neg_left : P.toFun (- Φ1) Φ2
    = (Potential.mk P.m₁₁2 P.m₂₂2 (- P.m₁₂2) P.𝓵₁ P.𝓵₂ P.𝓵₃ P.𝓵₄ P.𝓵₅ (- P.𝓵₆) (- P.𝓵₇)).toFun
    Φ1 Φ2 := by
  funext x
  simp only [toFun, normSq, ContMDiffSection.coe_neg, Pi.neg_apply, norm_neg,
    innerProd_neg_left, mul_neg, innerProd_neg_right, Complex.add_re, Complex.neg_re,
    Complex.mul_re, neg_sub, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add, neg_add_rev,
    one_div, Complex.norm_eq_abs, even_two, Even.neg_pow, Complex.inv_re, Complex.re_ofNat,
    Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div,
    zero_mul, sub_zero, Complex.mul_im, add_zero, Complex.ofReal_pow, map_neg]

/-- Negating `Φ₁` is equivalent to negating `m₁₂2`, `𝓵₆` and `𝓵₇`. -/
lemma neg_right : P.toFun Φ1 (- Φ2)
    = (Potential.mk P.m₁₁2 P.m₂₂2 (- P.m₁₂2) P.𝓵₁ P.𝓵₂ P.𝓵₃ P.𝓵₄ P.𝓵₅ (- P.𝓵₆) (- P.𝓵₇)).toFun
    Φ1 Φ2 := by
  rw [swap_fields, neg_left, swap_fields]
  simp only [map_neg, RingHomCompTriple.comp_apply, RingHom.id_apply]

lemma left_eq_right : P.toFun Φ1 Φ1 =
    (HiggsField.Potential.mk (- P.m₁₁2 - P.m₂₂2 + 2 * P.m₁₂2.re)
    (P.𝓵₁/2 + P.𝓵₂/2 + P.𝓵₃ + P.𝓵₄ + P.𝓵₅.re + 2 * P.𝓵₆.re + 2 * P.𝓵₇.re)).toFun Φ1 := by
  funext x
  simp only [toFun, normSq, innerProd_self_eq_normSq, Complex.ofReal_pow, Complex.add_re,
    Complex.mul_re, normSq_apply_re_self, normSq_apply_im_zero, mul_zero, sub_zero, Complex.conj_re,
    Complex.conj_im, one_div, norm_pow, Complex.norm_real, norm_norm, Complex.inv_re,
    Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im, Complex.im_ofNat,
    neg_zero, zero_div, zero_mul, Complex.mul_im, add_zero, mul_neg, neg_mul, sub_neg_eq_add,
    sub_add_add_cancel, zero_add, HiggsField.Potential.toFun, neg_add_rev, neg_sub]
  ring_nf
  erw [show ((Complex.ofRealHom ‖Φ1 x‖) ^ 4).re = ‖Φ1 x‖ ^ 4 by
    erw [← Complex.ofReal_pow]; rfl]
  erw [show ((Complex.ofRealHom ‖Φ1 x‖) ^ 2).re = ‖Φ1 x‖ ^ 2 by
    erw [← Complex.ofReal_pow]; rfl]
  erw [show (Complex.ofRealHom ‖Φ1 x‖ ^ 2).im = 0 by exact normSq_apply_im_zero Φ1 x]
  ring

lemma left_eq_neg_right : P.toFun Φ1 (- Φ1) =
    (HiggsField.Potential.mk (- P.m₁₁2 - P.m₂₂2 - 2 * P.m₁₂2.re)
    (P.𝓵₁/2 + P.𝓵₂/2 + P.𝓵₃ + P.𝓵₄ + P.𝓵₅.re - 2 * P.𝓵₆.re - 2 * P.𝓵₇.re)).toFun Φ1 := by
  rw [neg_right, left_eq_right]
  simp_all only [Complex.neg_re, mul_neg]
  rfl

/-!

## Potential bounded from below

-/

TODO "Prove bounded properties of the 2HDM potential.
  See e.g. https://inspirehep.net/literature/201299 and
  https://arxiv.org/pdf/hep-ph/0605184."

/-- The proposition on the coefficients for a potential to be bounded. -/
def IsBounded : Prop :=
  ∃ c, ∀ Φ1 Φ2 x, c ≤ P.toFun Φ1 Φ2 x

section IsBounded

variable {P : Potential}

lemma isBounded_right_zero (h : P.IsBounded) :
    (HiggsField.Potential.mk (- P.m₁₁2) (P.𝓵₁/2)).IsBounded := by
  obtain ⟨c, hc⟩ := h
  use c
  intro Φ x
  have hc1 := hc Φ 0 x
  rw [right_zero] at hc1
  exact hc1

lemma isBounded_left_zero (h : P.IsBounded) :
    (HiggsField.Potential.mk (- P.m₂₂2) (P.𝓵₂/2)).IsBounded := by
  obtain ⟨c, hc⟩ := h
  use c
  intro Φ x
  have hc1 := hc 0 Φ x
  rw [left_zero] at hc1
  exact hc1

lemma isBounded_𝓵₁_nonneg (h : P.IsBounded) :
    0 ≤ P.𝓵₁ := by
  have h1 := isBounded_right_zero h
  have h2 := HiggsField.Potential.isBounded_𝓵_nonneg _ h1
  simp only at h2
  linarith

lemma isBounded_𝓵₂_nonneg (h : P.IsBounded) :
    0 ≤ P.𝓵₂ := by
  have h1 := isBounded_left_zero h
  have h2 := HiggsField.Potential.isBounded_𝓵_nonneg _ h1
  simp only at h2
  linarith

lemma isBounded_of_left_eq_right (h : P.IsBounded) :
    0 ≤ P.𝓵₁/2 + P.𝓵₂/2 + P.𝓵₃ + P.𝓵₄ + P.𝓵₅.re + 2 * P.𝓵₆.re + 2 * P.𝓵₇.re := by
  obtain ⟨c, hc⟩ := h
  refine (HiggsField.Potential.mk (- P.m₁₁2 - P.m₂₂2 + 2 * P.m₁₂2.re)
    (P.𝓵₁/2 + P.𝓵₂/2 + P.𝓵₃ + P.𝓵₄ + P.𝓵₅.re + 2 * P.𝓵₆.re + 2 * P.𝓵₇.re)).isBounded_𝓵_nonneg
    ⟨c, fun Φ x => ?_⟩
  have hc1 := hc Φ Φ x
  rw [left_eq_right] at hc1
  exact hc1

lemma isBounded_of_left_eq_neg_right (h : P.IsBounded) :
    0 ≤ P.𝓵₁/2 + P.𝓵₂/2 + P.𝓵₃ + P.𝓵₄ + P.𝓵₅.re - 2 * P.𝓵₆.re - 2 * P.𝓵₇.re := by
  obtain ⟨c, hc⟩ := h
  refine (HiggsField.Potential.mk (- P.m₁₁2 - P.m₂₂2 - 2 * P.m₁₂2.re)
    (P.𝓵₁/2 + P.𝓵₂/2 + P.𝓵₃ + P.𝓵₄ + P.𝓵₅.re - 2 * P.𝓵₆.re - 2 * P.𝓵₇.re)).isBounded_𝓵_nonneg
    ⟨c, fun Φ x => ?_⟩
  have hc1 := hc Φ (- Φ) x
  rw [left_eq_neg_right] at hc1
  exact hc1

lemma nonneg_sum_𝓵₁_to_𝓵₅_of_isBounded (h : P.IsBounded) :
    0 ≤ P.𝓵₁/2 + P.𝓵₂/2 + P.𝓵₃ + P.𝓵₄ + P.𝓵₅.re := by
  have h1 := isBounded_of_left_eq_neg_right h
  have h2 := isBounded_of_left_eq_right h
  linarith

end IsBounded

end Potential

end
end TwoHDM
