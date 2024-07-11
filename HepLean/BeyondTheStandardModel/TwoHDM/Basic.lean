/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.HiggsBoson.Potential
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

/-- The potential of the two Higgs doublet model. -/
def potential (m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ)
    (m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ) (Φ1 Φ2 : HiggsField) (x : SpaceTime) : ℝ :=
  m₁₁2 * ‖Φ1‖_H ^ 2 x  + m₂₂2 * ‖Φ2‖_H ^ 2 x - (m₁₂2 * ⟪Φ1, Φ2⟫_H x + conj m₁₂2 * ⟪Φ2, Φ1⟫_H x).re
  + 1/2 * 𝓵₁ *  ‖Φ1‖_H ^ 2 x * ‖Φ1‖_H ^ 2 x + 1/2 * 𝓵₂ * ‖Φ2‖_H ^ 2 x * ‖Φ2‖_H ^ 2 x
  + 𝓵₃ * ‖Φ1‖_H ^ 2 x * ‖Φ2‖_H ^ 2 x
  + 𝓵₄ * ‖⟪Φ1, Φ2⟫_H x‖ ^ 2 + (1/2 * 𝓵₅ * ⟪Φ1, Φ2⟫_H  x ^ 2 + 1/2 * conj 𝓵₅ * ⟪Φ2, Φ1⟫_H x ^ 2).re
  + (𝓵₆ * ‖Φ1‖_H ^ 2 x * ⟪Φ1, Φ2⟫_H x + conj 𝓵₆ * ‖Φ1‖_H ^ 2 x * ⟪Φ2, Φ1⟫_H x).re
  + (𝓵₇ * ‖Φ2‖_H ^ 2 x * ⟪Φ1, Φ2⟫_H x + conj 𝓵₇ * ‖Φ2‖_H ^ 2 x * ⟪Φ2, Φ1⟫_H x).re

namespace potential

variable (Φ1 Φ2 : HiggsField)
variable (m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ)
variable (m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ)
/-!

## Simple properties of the potential

-/

/-- Swapping `Φ1` with `Φ2`, and a number of the parameters (with possible conjugation) leads
  to an identical potential. -/
lemma swap_fields :
    potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ Φ1 Φ2
    = potential m₂₂2 m₁₁2 𝓵₂ 𝓵₁ 𝓵₃ 𝓵₄ (conj m₁₂2) (conj 𝓵₅) (conj 𝓵₇) (conj 𝓵₆) Φ2 Φ1 := by
  funext x
  simp only [potential, HiggsField.normSq, Complex.add_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, neg_mul, sub_neg_eq_add, one_div, Complex.norm_eq_abs, Complex.inv_re,
    Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im, Complex.im_ofNat,
    neg_zero, zero_div, zero_mul, sub_zero, Complex.mul_im, add_zero, mul_neg, Complex.ofReal_pow,
    RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring_nf
  simp only [one_div, add_left_inj, add_right_inj, mul_eq_mul_left_iff]
  apply Or.inl
  rw [HiggsField.innerProd, HiggsField.innerProd, ← InnerProductSpace.conj_symm, Complex.abs_conj]

/-- If `Φ₂` is zero the potential reduces to the Higgs potential on `Φ₁`. -/
lemma right_zero : potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ Φ1 0 =
    StandardModel.HiggsField.potential (- m₁₁2) (𝓵₁/2) Φ1  := by
  funext x
  simp only [potential, normSq, ContMDiffSection.coe_zero, Pi.zero_apply, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, innerProd_right_zero,
    innerProd_left_zero, Complex.zero_re, sub_zero, one_div, Complex.ofReal_pow,
    Complex.ofReal_zero, HiggsField.potential, neg_neg, add_right_inj, mul_eq_mul_right_iff,
    pow_eq_zero_iff, norm_eq_zero, or_self_right]
  ring_nf
  simp only [true_or]

/-- If `Φ₁` is zero the potential reduces to the Higgs potential on `Φ₂`. -/
lemma left_zero : potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ 0 Φ2 =
    StandardModel.HiggsField.potential (- m₂₂2) (𝓵₂/2) Φ2 := by
  rw [swap_fields, right_zero]

/-!

## Potential bounded from below

-/

/-! TODO: Prove bounded properties of the 2HDM potential. -/

/-- The proposition on the coefficents for a potential to be bounded. -/
def IsBounded (m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ) (m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ) : Prop :=
  ∃ c, ∀ Φ1 Φ2 x, c ≤ potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ Φ1 Φ2 x

/-!

## Smoothness of the potential

-/

/-! TODO: Prove smoothness properties of the 2HDM potential. -/

/-!

## Invariance of the potential under gauge transformations

-/

/-! TODO: Prove invariance properties of the 2HDM potential. -/

end potential

end
end TwoHDM
