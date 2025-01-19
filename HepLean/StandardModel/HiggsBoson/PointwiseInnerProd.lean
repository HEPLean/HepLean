/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.HiggsBoson.Basic
/-!
# The pointwise inner product

We define the pointwise inner product of two Higgs fields.

The notation for the inner product is `⟪φ, ψ⟫_H`.

We also define the pointwise norm squared of a Higgs field `∥φ∥_H ^ 2`.

-/

noncomputable section

namespace StandardModel

namespace HiggsField

open Manifold
open Matrix
open Complex
open ComplexConjugate
open SpaceTime
open InnerProductSpace

/-!

## The pointwise inner product

-/

/-- Given two `HiggsField`, the map `SpaceTime → ℂ` obtained by taking their pointwise
  inner product. -/
def innerProd (φ1 φ2 : HiggsField) : (SpaceTime → ℂ) := fun x => ⟪φ1 x, φ2 x⟫_ℂ

/-- Notation for the inner product of two Higgs fields. -/
scoped[StandardModel.HiggsField] notation "⟪" φ1 "," φ2 "⟫_H" => innerProd φ1 φ2

/-!

## Properties of the inner product

-/

@[simp]
lemma innerProd_neg_left (φ1 φ2 : HiggsField) : ⟪- φ1, φ2⟫_H = - ⟪φ1, φ2⟫_H := by
  funext x
  simp [innerProd]

@[simp]
lemma innerProd_neg_right (φ1 φ2 : HiggsField) : ⟪φ1, - φ2⟫_H = -⟪φ1, φ2⟫_H := by
  funext x
  simp [innerProd]

@[simp]
lemma innerProd_left_zero (φ : HiggsField) : ⟪0, φ⟫_H = 0 := by
  funext x
  simp [innerProd]

@[simp]
lemma innerProd_right_zero (φ : HiggsField) : ⟪φ, 0⟫_H = 0 := by
  funext x
  simp [innerProd]

/-- Expands the inner product on Higgs fields in terms of complex components of the
  Higgs fields. -/
lemma innerProd_expand' (φ1 φ2 : HiggsField) (x : SpaceTime) :
    ⟪φ1, φ2⟫_H x = conj (φ1 x 0) * φ2 x 0 + conj (φ1 x 1) * φ2 x 1 := by
  simp [innerProd]

/-- Expands the inner product on Higgs fields in terms of real components of the
  Higgs fields. -/
lemma innerProd_expand (φ1 φ2 : HiggsField) :
    ⟪φ1, φ2⟫_H = fun x => equivRealProdCLM.symm (((φ1 x 0).re * (φ2 x 0).re
    + (φ1 x 1).re * (φ2 x 1).re+ (φ1 x 0).im * (φ2 x 0).im + (φ1 x 1).im * (φ2 x 1).im),
    ((φ1 x 0).re * (φ2 x 0).im + (φ1 x 1).re * (φ2 x 1).im
    - (φ1 x 0).im * (φ2 x 0).re - (φ1 x 1).im * (φ2 x 1).re)) := by
  funext x
  simp only [innerProd, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two,
    equivRealProdCLM_symm_apply, ofReal_add, ofReal_mul, ofReal_sub]
  rw [RCLike.conj_eq_re_sub_im, RCLike.conj_eq_re_sub_im]
  nth_rewrite 1 [← RCLike.re_add_im (φ2 x 0)]
  nth_rewrite 1 [← RCLike.re_add_im (φ2 x 1)]
  ring_nf
  simp only [Fin.isValue, RCLike.re_to_complex, coe_algebraMap, RCLike.I_to_complex,
    RCLike.im_to_complex, I_sq, mul_neg, mul_one, neg_mul, sub_neg_eq_add, one_mul]
  ring

lemma smooth_innerProd (φ1 φ2 : HiggsField) : ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℂ) ⊤ ⟪φ1, φ2⟫_H := by
  rw [innerProd_expand]
  exact (ContinuousLinearMap.contMDiff (equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)).comp $
    (((((φ1.apply_re_smooth 0).smul (φ2.apply_re_smooth 0)).add
    ((φ1.apply_re_smooth 1).smul (φ2.apply_re_smooth 1))).add
    ((φ1.apply_im_smooth 0).smul (φ2.apply_im_smooth 0))).add
    ((φ1.apply_im_smooth 1).smul (φ2.apply_im_smooth 1))).prod_mk_space $
    ((((φ1.apply_re_smooth 0).smul (φ2.apply_im_smooth 0)).add
    ((φ1.apply_re_smooth 1).smul (φ2.apply_im_smooth 1))).sub
    ((φ1.apply_im_smooth 0).smul (φ2.apply_re_smooth 0))).sub
    ((φ1.apply_im_smooth 1).smul (φ2.apply_re_smooth 1))

/-!

## The pointwise norm squared

-/

/-- Given a `HiggsField`, the map `SpaceTime → ℝ` obtained by taking the square norm of the
  pointwise Higgs vector. -/
@[simp]
def normSq (φ : HiggsField) : SpaceTime → ℝ := fun x => ‖φ x‖ ^ 2

/-- Notation for the norm squared of a Higgs field. -/
scoped[StandardModel.HiggsField] notation "‖" φ1 "‖_H^2" => normSq φ1

/-!

## Relation between inner prod and norm squared

-/

@[simp]
lemma innerProd_self_eq_normSq (φ : HiggsField) (x : SpaceTime) :
    ⟪φ, φ⟫_H x = ‖φ‖_H^2 x := by
  erw [normSq, @PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp only [innerProd, PiLp.inner_apply, RCLike.inner_apply, conj_mul', norm_eq_abs,
    Fin.sum_univ_two, ofReal_add, ofReal_pow]

lemma normSq_eq_innerProd_self (φ : HiggsField) (x : SpaceTime) :
    ‖φ x‖ ^ 2 = (⟪φ, φ⟫_H x).re := by
  rw [innerProd_self_eq_normSq]
  rfl

/-!

# Properties of the norm squared

-/

lemma normSq_apply_im_zero (φ : HiggsField) (x : SpaceTime) :
    ((Complex.ofRealHom ‖φ x‖) ^ 2).im = 0 := by
  rw [sq]
  simp only [ofRealHom_eq_coe, mul_im, ofReal_re, ofReal_im, mul_zero, zero_mul, add_zero]

lemma normSq_apply_re_self (φ : HiggsField) (x : SpaceTime) :
    ((Complex.ofRealHom ‖φ x‖) ^ 2).re = φ.normSq x := by
  rw [sq]
  simp only [ofRealHom_eq_coe, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, normSq]
  exact Eq.symm (pow_two ‖φ x‖)

lemma toHiggsVec_norm (φ : HiggsField) (x : SpaceTime) :
    ‖φ x‖ = ‖φ.toHiggsVec x‖ := rfl

/-- The expansion of the norm squared of into components. -/
lemma normSq_expand (φ : HiggsField) :
    φ.normSq = fun x => (conj (φ x 0) * (φ x 0) + conj (φ x 1) * (φ x 1)).re := by
  funext x
  simp [normSq, add_re, mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add, @norm_sq_eq_inner ℂ]

/-- The norm squared of a higgs field at any point is non-negative. -/
lemma normSq_nonneg (φ : HiggsField) (x : SpaceTime) : 0 ≤ φ.normSq x := by
  simp [normSq, ge_iff_le, norm_nonneg, pow_nonneg]

/-- If the norm square of a Higgs field at a point `x` is zero, then the Higgs field
  at that point is zero. -/
lemma normSq_zero (φ : HiggsField) (x : SpaceTime) : φ.normSq x = 0 ↔ φ x = 0 := by
  simp [normSq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero]

/-- The norm squared of the Higgs field is a smooth function on space-time. -/
lemma normSq_smooth (φ : HiggsField) : ContMDiff 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) ⊤ φ.normSq := by
  rw [normSq_expand]
  refine ContMDiff.add ?_ ?_
  · simp only [mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add]
    exact ((φ.apply_re_smooth 0).smul (φ.apply_re_smooth 0)).add $
      (φ.apply_im_smooth 0).smul (φ.apply_im_smooth 0)
  · simp only [mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add]
    exact ((φ.apply_re_smooth 1).smul (φ.apply_re_smooth 1)).add $
      (φ.apply_im_smooth 1).smul (φ.apply_im_smooth 1)

/-- The norm-squared of the Higgs field `HiggsField.ofReal a` for a non-negative real number `a`,
  is equal to `a`. -/
lemma ofReal_normSq {a : ℝ} (ha : 0 ≤ a) (x : SpaceTime) : (ofReal a).normSq x = a := by
  simp only [normSq, ofReal, HiggsVec.toField_apply, ha, HiggsVec.ofReal_normSq]

end HiggsField

end StandardModel
end
