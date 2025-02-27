/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Basic
import Mathlib.Topology.Algebra.Polynomial
/-!

# Eigenfunction of the Harmonic Oscillator

-/

namespace QuantumMechanics

namespace OneDimension
namespace HarmonicOscillator

variable (Q : HarmonicOscillator)

open Nat
open PhysLean
open HilbertSpace

/-- The `n`th eigenfunction of the Harmonic oscillator is defined as the function `ℝ → ℂ`
  taking `x : ℝ` to

  `1/√(2^n n!) (m ω /(π ℏ))^(1/4) * physHermite n (√(m ω /ℏ) x) * e ^ (- m ω x^2/2ℏ)`.

-/
noncomputable def eigenfunction (n : ℕ) : ℝ → ℂ := fun x =>
  1/√(2 ^ n * n !) * √√(Q.m * Q.ω / (Real.pi * Q.ℏ)) *
  physHermite n (√(Q.m * Q.ω / Q.ℏ) * x) * Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ))

lemma eigenfunction_eq (n : ℕ) :
    Q.eigenfunction n = fun (x : ℝ) => ((1/√(2 ^ n * n !) * √√(Q.m * Q.ω / (Real.pi * Q.ℏ))) *
    Complex.ofReal (physHermite n (√(Q.m * Q.ω / Q.ℏ) * x) *
    Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ)))) := by
  funext x
  simp only [eigenfunction, ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div,
    mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

lemma eigenfunction_zero : Q.eigenfunction 0 = fun (x : ℝ) =>
    √√(Q.m * Q.ω / (Real.pi * Q.ℏ)) * Complex.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ)) := by
  funext x
  simp [eigenfunction]

lemma eigenfunction_eq_mul_eigenfunction_zero (n : ℕ) :
    Q.eigenfunction n = fun x => Complex.ofReal (1/√(2 ^ n * n !))
    * Complex.ofReal (physHermite n (√(Q.m * Q.ω / Q.ℏ) * x)) * Q.eigenfunction 0 x := by
  match n with
  | 0 =>
    simp
  | n + 1 =>
    funext x
    field_simp [eigenfunction, eigenfunction_zero]
    ring

/-!

## Basic properties of the eigenfunctions

-/

/-- The eigenfunctions are integrable. -/
@[fun_prop]
lemma eigenfunction_integrable (n : ℕ) : MeasureTheory.Integrable (Q.eigenfunction n) := by
  rw [eigenfunction_eq]
  apply MeasureTheory.Integrable.const_mul
  apply MeasureTheory.Integrable.ofReal
  change MeasureTheory.Integrable
    (fun x => (physHermite n (√(Q.m * Q.ω / Q.ℏ) * x)) *
    (Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ)))) MeasureTheory.volume
  have h1 : (fun x => (physHermite n (√(Q.m * Q.ω / Q.ℏ) * x)) *
      (Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ)))) =
      (fun x => (physHermite n (√(Q.m * Q.ω / Q.ℏ) * x)) *
      (Real.exp (- (Q.m * Q.ω / (2* Q.ℏ)) * x ^ 2))) := by
    funext x
    simp only [neg_mul, mul_eq_mul_left_iff, Real.exp_eq_exp]
    left
    field_simp
  rw [h1]
  apply guassian_integrable_polynomial_cons
  simp

/-- The eigenfunctions are real. -/
@[simp]
lemma eigenfunction_conj (n : ℕ) (x : ℝ) :
    (starRingEnd ℂ) (Q.eigenfunction n x) = Q.eigenfunction n x := by
  rw [eigenfunction_eq]
  simp [-Complex.ofReal_exp]

lemma eigenfunction_point_norm (n : ℕ) (x : ℝ) :
    ‖Q.eigenfunction n x‖ = (1/√(2 ^ n * n !) * √√(Q.m * Q.ω / (Real.pi * Q.ℏ))) *
    (|physHermite n (√(Q.m * Q.ω / Q.ℏ) * x)| * Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ))) := by
  rw [eigenfunction_eq]
  simp only [neg_mul, Complex.ofReal_mul, Complex.norm_eq_abs]
  rw [AbsoluteValue.map_mul, AbsoluteValue.map_mul]
  congr
  · simp [Real.sqrt_nonneg, abs_of_nonneg]
  · simp
  · rw [AbsoluteValue.map_mul]
    congr 1
    · simp
    · rw [Complex.abs_ofReal]
      simp [abs_of_nonneg]

lemma eigenfunction_point_norm_sq (n : ℕ) (x : ℝ) :
    ‖Q.eigenfunction n x‖ ^ 2 = (1/√(2 ^ n * n !) * √√(Q.m * Q.ω / (Real.pi * Q.ℏ))) ^ 2 *
    ((physHermite n (√(Q.m * Q.ω / Q.ℏ) * x)) ^ 2 * Real.exp (- Q.m * Q.ω * x^2 / Q.ℏ)) := by
  trans (1/√(2 ^ n * n !) * √√(Q.m * Q.ω / (Real.pi * Q.ℏ))) ^ 2 *
    ((|physHermite n (√(Q.m * Q.ω / Q.ℏ) * x)|) ^ 2 *
    Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ)) ^ (2 : ℝ))
  · simp only [Real.rpow_two]
    rw [eigenfunction_point_norm]
    ring
  · congr 2
    · exact sq_abs (physHermite n _)
    · rw [← Real.exp_mul]
      congr 1
      ring

/-- The eigenfunctions are square integrable. -/
@[fun_prop]
lemma eigenfunction_square_integrable (n : ℕ) :
    MeasureTheory.Integrable (fun x => ‖Q.eigenfunction n x‖ ^ 2) := by
  have h0 (x : ℝ) : Real.exp (- Q.m * Q.ω * x ^ 2 / Q.ℏ) =
      Real.exp (- (Q.m * Q.ω /Q.ℏ) * x ^ 2) := by
    simp only [neg_mul, Real.exp_eq_exp]
    ring
  conv =>
    enter [1, x]
    rw [eigenfunction_point_norm_sq]
    rw [physHermite_pow, h0]
  apply MeasureTheory.Integrable.const_mul
  apply guassian_integrable_polynomial_cons
  simp

/-- The eigenfunctions are almost everywhere strongly measurable. -/
@[fun_prop]
lemma eigenfunction_aeStronglyMeasurable (n : ℕ) :
    MeasureTheory.AEStronglyMeasurable (Q.eigenfunction n) :=
  (Q.eigenfunction_integrable n).aestronglyMeasurable

/-- The eigenfunctions are members of the Hilbert space. -/
lemma eigenfunction_memHS (n : ℕ) : MemHS (Q.eigenfunction n) := by
  rw [memHS_iff]
  apply And.intro
  · fun_prop
  · fun_prop

/-- The eigenfunctions are differentiable. -/
@[fun_prop]
lemma eigenfunction_differentiableAt (x : ℝ) (n : ℕ) :
    DifferentiableAt ℝ (Q.eigenfunction n) x := by
  rw [eigenfunction_eq]
  fun_prop

/-- The eigenfunctions are continuous. -/
@[fun_prop]
lemma eigenfunction_continuous (n : ℕ) : Continuous (Q.eigenfunction n) := by
  rw [eigenfunction_eq]
  fun_prop

/-- The `n`th eigenfunction is an eigenfunction of the parity operator with
  the eigenvalue `(-1) ^ n`. -/
lemma eigenfunction_parity (n : ℕ) :
    parity (Q.eigenfunction n) = (-1) ^ n * Q.eigenfunction n := by
  funext x
  rw [eigenfunction_eq]
  simp only [parity, LinearMap.coe_mk, AddHom.coe_mk, mul_neg, Pi.mul_apply, Pi.pow_apply,
    Pi.neg_apply, Pi.one_apply]
  rw [← physHermite_eq_aeval, physHermite_parity]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  ring_nf

/-!

## Orthnormality

-/

/-- A simplification of the product of two eigen-functions. -/
lemma eigenfunction_mul (n p : ℕ) :
    (Q.eigenfunction n x) * (Q.eigenfunction p x) =
    1/√(2 ^ n * n !) * 1/√(2 ^ p * p !) * √(Q.m * Q.ω / (Real.pi * Q.ℏ)) *
    Complex.ofReal (physHermite n (√(Q.m * Q.ω /Q.ℏ) * x) *
    physHermite p (√(Q.m * Q.ω /Q.ℏ) * x) * Real.exp (- Q.m * Q.ω * x^2 / Q.ℏ)) := by
  calc Q.eigenfunction n x * Q.eigenfunction p x
    _ = (1/√(2 ^ n * n !) * 1/√(2 ^ p * p !)) *
        (√√(Q.m * Q.ω / (Real.pi * Q.ℏ)) * √√(Q.m * Q.ω / (Real.pi * Q.ℏ))) *
        (physHermite n (√(Q.m * Q.ω /Q.ℏ) * x) * physHermite p (√(Q.m * Q.ω /Q.ℏ) * x)) *
        (Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ)) * Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ))) := by
      simp only [eigenfunction, ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul,
        one_div, mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_pow, Complex.ofReal_ofNat, mul_one]
      ring
    _ = (1/√(2 ^ n * n !) * 1/√(2 ^ p * p !)) * √(Q.m * Q.ω / (Real.pi * Q.ℏ)) *
        (physHermite n (√(Q.m * Q.ω /Q.ℏ) * x) *  physHermite p (√(Q.m * Q.ω / Q.ℏ) * x)) *
        (Real.exp (- Q.m * Q.ω * x^2 / Q.ℏ)) := by
      congr 1
      · congr 1
        · congr 1
          · rw [← Complex.ofReal_mul]
            congr
            refine Real.mul_self_sqrt ?_
            exact Real.sqrt_nonneg (Q.m * Q.ω / (Real.pi * Q.ℏ))
      · rw [← Complex.ofReal_mul]
        congr
        rw [← Real.exp_add]
        simp only [neg_mul, Real.exp_eq_exp]
        field_simp
        ring
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
    mul_one, neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_pow]
  ring

lemma eigenfunction_mul_self (n : ℕ) : (Q.eigenfunction n x) * (Q.eigenfunction n x) =
    (1/ (2 ^ n * n !) * √(Q.m * Q.ω / (Real.pi * Q.ℏ))) *
    Complex.ofReal ((physHermite n (√(Q.m * Q.ω /Q.ℏ) * x))^2 *
    Real.exp (- Q.m * Q.ω * x^2 / Q.ℏ)) := by
  calc Q.eigenfunction n x * Q.eigenfunction n x
    _ = (1/√(2 ^ n * n !) * 1/√(2 ^ n * n !)) *
        (√√(Q.m * Q.ω / (Real.pi * Q.ℏ)) * √√(Q.m * Q.ω / (Real.pi * Q.ℏ))) *
        (physHermite n (√(Q.m * Q.ω /Q.ℏ) * x))^2 *
        (Real.exp (-Q.m * Q.ω * x^2 / (2 * Q.ℏ)) * Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ))) := by
      simp only [eigenfunction, ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul,
        one_div, mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_pow, Complex.ofReal_ofNat, mul_one]
      ring
    _ = (1/ (2 ^ n * n !)) * √(Q.m * Q.ω / (Real.pi * Q.ℏ)) *
        (physHermite n (√(Q.m * Q.ω / Q.ℏ) * x))^2 * Real.exp (- Q.m * Q.ω * x^2 /Q.ℏ) := by
      congr 1
      · congr 1
        · congr 1
          · trans 1 / ↑(√(2 ^ n * ↑n !) * ↑√(2 ^ n * ↑n !))
            · field_simp
            congr
            trans Complex.ofReal ((2 ^ n * ↑n !))
            · congr 1
              refine Real.mul_self_sqrt ?_
              refine Left.mul_nonneg ?_ (cast_nonneg' n !)
              refine pow_nonneg ?_ n
              simp only [ofNat_nonneg]
            simp
          · rw [← Complex.ofReal_mul]
            congr
            refine Real.mul_self_sqrt ?_
            exact Real.sqrt_nonneg (Q.m * Q.ω / (Real.pi * Q.ℏ))
      · rw [← Complex.ofReal_mul]
        congr
        rw [← Real.exp_add]
        simp only [neg_mul, Real.exp_eq_exp]
        field_simp
        ring
  simp only [one_div, mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

open InnerProductSpace

/-- The eigenfunction are normalized. -/
lemma eigenfunction_normalized (n : ℕ) : ⟪HilbertSpace.mk (Q.eigenfunction_memHS n),
    HilbertSpace.mk (Q.eigenfunction_memHS n)⟫_ℂ = 1 := by
  rw [inner_mk_mk]
  conv_lhs =>
    enter [2, x]
    rw [eigenfunction_conj, Q.eigenfunction_mul_self]
  rw [MeasureTheory.integral_mul_left, integral_complex_ofReal]
  have hc : (∫ (x : ℝ), physHermite n (√(Q.m * Q.ω / Q.ℏ) * x) ^ 2 *
      Real.exp (- Q.m * Q.ω * x ^ 2 / Q.ℏ))
      = ∫ (x : ℝ), (physHermite n (1/Q.ξ * x) *
      physHermite n (1/Q.ξ * x)) * Real.exp (- (1/Q.ξ)^2 * x ^ 2) := by
    congr
    funext x
    congr
    · simp only [one_over_ξ]
      exact pow_two _
    · simp only [neg_mul, one_over_ξ_sq]
      field_simp
  rw [hc, physHermite_norm_cons]
  simp only [one_div, mul_inv_rev, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring_nf
  have h1 : √(Q.m * Q.ω * Real.pi⁻¹ * Q.ℏ⁻¹) = Q.ξ⁻¹* (√(Real.pi⁻¹)) := by
    trans √((Q.m * Q.ω * Q.ℏ⁻¹) * Real.pi⁻¹)
    · ring_nf
    rw [Real.sqrt_mul' _ (inv_nonneg_of_nonneg Real.pi_nonneg), ξ_inverse]
    field_simp
  rw [h1]
  have : (n ! : ℂ) ≠ 0 := Complex.ne_zero_of_re_pos <| by simpa using factorial_pos n
  have := Complex.ofReal_ne_zero.mpr (ne_of_gt Q.ξ_pos)
  have := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  field_simp

/-- The eigen-functions of the quantum harmonic oscillator are orthogonal. -/
lemma eigenfunction_orthogonal {n p : ℕ} (hnp : n ≠ p) :
    ⟪HilbertSpace.mk (Q.eigenfunction_memHS n),
      HilbertSpace.mk (Q.eigenfunction_memHS p)⟫_ℂ = 0 := by
  rw [inner_mk_mk]
  conv_lhs =>
    enter [2, x]
    rw [eigenfunction_conj, Q.eigenfunction_mul n p]
  rw [MeasureTheory.integral_mul_left, integral_complex_ofReal]
  have hc : (∫ (x : ℝ), (physHermite n (√(Q.m * Q.ω / Q.ℏ) * x) *
      physHermite p (√(Q.m * Q.ω / Q.ℏ) * x)) *  Real.exp (-Q.m * Q.ω * x ^ 2 / Q.ℏ))
      = ∫ (x : ℝ), (physHermite n (1/Q.ξ * x) * physHermite p (1/Q.ξ * x)) *
      Real.exp (- (1/Q.ξ)^2 * x ^ 2) := by
    congr
    funext x
    rw [one_over_ξ_sq]
    field_simp [neg_mul, one_over_ξ, one_over_ξ_sq]
  rw [hc, physHermite_orthogonal_cons hnp]
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
    mul_one, Complex.ofReal_zero, mul_zero]

/-- The eigenfunctions are orthonormal within the Hilbert space. -/
lemma eigenfunction_orthonormal :
    Orthonormal ℂ (fun n => HilbertSpace.mk (Q.eigenfunction_memHS n)) := by
  rw [orthonormal_iff_ite]
  intro n p
  by_cases hnp : n = p
  · simp only [hnp, reduceIte]
    exact Q.eigenfunction_normalized p
  · simp only [hnp, reduceIte]
    exact Q.eigenfunction_orthogonal hnp

/-- The eigenfunctions are linearly independent. -/
lemma eigenfunction_linearIndependent :
    LinearIndependent ℂ (fun n => HilbertSpace.mk (Q.eigenfunction_memHS n)) :=
  Q.eigenfunction_orthonormal.linearIndependent

end HarmonicOscillator
end OneDimension
end QuantumMechanics
