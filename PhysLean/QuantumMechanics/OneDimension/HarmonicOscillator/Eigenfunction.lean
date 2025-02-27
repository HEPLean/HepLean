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
  1/Real.sqrt (2 ^ n * n !) * Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ))) *
  physHermite n (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x) * Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ))

lemma eigenfunction_eq (n : ℕ) :
    Q.eigenfunction n = fun (x : ℝ) =>
    ((1/Real.sqrt (2 ^ n * n !) * Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ)))) *
    Complex.ofReal (physHermite n (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x) *
    Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ)))) := by
  funext x
  simp only [eigenfunction, ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div,
    mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

lemma eigenfunction_zero : Q.eigenfunction 0 = fun (x : ℝ) =>
    (Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ))) *
    Complex.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ))) := by
  funext x
  simp [eigenfunction]

lemma eigenfunction_eq_mul_eigenfunction_zero (n : ℕ) :
    Q.eigenfunction n = fun x => Complex.ofReal (1/Real.sqrt (2 ^ n * n !))
    * Complex.ofReal (physHermite n (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x))
    * Q.eigenfunction 0 x := by
  match n with
  | 0 =>
    simp
  | n + 1 =>
    funext x
    rw [eigenfunction, eigenfunction_zero]
    repeat rw [mul_assoc]
    congr 1
    · simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
        Complex.ofReal_inv]
    · rw [mul_comm, mul_assoc]
      congr 1
      simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
      ring_nf

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
    ‖Q.eigenfunction n x‖ = (1/Real.sqrt (2 ^ n * n !) *
    Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ)))) *
    (|physHermite n (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x)| *
    Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ))) := by
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
    ‖Q.eigenfunction n x‖ ^ 2 = (1/Real.sqrt (2 ^ n * n !) *
    Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ)))) ^ 2 *
    ((physHermite n
    (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x)) ^ 2 * Real.exp (- Q.m * Q.ω * x^2 / Q.ℏ)) := by
  trans (1/Real.sqrt (2 ^ n * n !) *
    Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ)))) ^ 2 *
    ((|physHermite n (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x)|) ^ 2 *
    (Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ)) ^ (2 : ℝ)))
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
    ((1/Real.sqrt (2 ^ n * n !) * 1/Real.sqrt (2 ^ p * p !)) *
    ((Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ))))) *
    Complex.ofReal ((physHermite n (Real.sqrt (Q.m * Q.ω /Q.ℏ) * x) *
    physHermite p (Real.sqrt (Q.m * Q.ω /Q.ℏ) * x)) * (Real.exp (- Q.m * Q.ω * x^2 / Q.ℏ))) := by
  calc Q.eigenfunction n x * Q.eigenfunction p x
    _ = (1/Real.sqrt (2 ^ n * n !) * 1/Real.sqrt (2 ^ p * p !)) *
      (Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ))) *
      Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ)))) *
      (physHermite n (Real.sqrt (Q.m * Q.ω /Q.ℏ) * x) *
        physHermite p (Real.sqrt (Q.m * Q.ω /Q.ℏ) * x)) *
      (Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ)) * Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ))) := by
      simp only [eigenfunction, ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul,
        one_div, mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_pow, Complex.ofReal_ofNat, mul_one]
      ring
    _ = (1/Real.sqrt (2 ^ n * n !) * 1/Real.sqrt (2 ^ p * p !)) *
      ((Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ)))) *
      (physHermite n (Real.sqrt (Q.m * Q.ω /Q.ℏ) * x) *
        physHermite p (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x)) *
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

lemma eigenfunction_mul_self (n : ℕ) :
    (Q.eigenfunction n x) * (Q.eigenfunction n x) =
    ((1/ (2 ^ n * n !)) * (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ)))) *
    Complex.ofReal ((physHermite n (Real.sqrt (Q.m * Q.ω /Q.ℏ) * x))^2 *
    (Real.exp (- Q.m * Q.ω * x^2 / Q.ℏ))) := by
  calc Q.eigenfunction n x * Q.eigenfunction n x
    _ = (1/Real.sqrt (2 ^ n * n !) * 1/Real.sqrt (2 ^ n * n !)) *
      (Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ))) *
      Real.sqrt (Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ)))) *
      (physHermite n (Real.sqrt (Q.m * Q.ω /Q.ℏ) * x))^2 *
      (Real.exp (-Q.m * Q.ω * x^2 / (2 * Q.ℏ)) * Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ))) := by
      simp only [eigenfunction, ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul,
        one_div, mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_pow, Complex.ofReal_ofNat, mul_one]
      ring
    _ = (1/ (2 ^ n * n !)) *
      ((Real.sqrt (Q.m * Q.ω / (Real.pi * Q.ℏ)))) *
      (physHermite n (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x))^2 *
      (Real.exp (- Q.m * Q.ω * x^2 /Q.ℏ)) := by
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
lemma eigenfunction_normalized (n : ℕ) :
    ⟪HilbertSpace.mk (Q.eigenfunction_memHS n),
      HilbertSpace.mk (Q.eigenfunction_memHS n)⟫_ℂ = 1 := by
  rw [inner_mk_mk]
  conv_lhs =>
    enter [2, x]
    rw [eigenfunction_conj, Q.eigenfunction_mul_self]
  rw [MeasureTheory.integral_mul_left, integral_complex_ofReal]
  let c := √(Q.m * Q.ω / Q.ℏ)
  have h1 : c ^ 2 = Q.m * Q.ω / Q.ℏ := by
    trans c * c
    · exact pow_two c
    simp only [c]
    refine Real.mul_self_sqrt ?_
    refine div_nonneg ?_ ?_
    exact (mul_nonneg_iff_of_pos_left Q.hm).mpr (le_of_lt Q.hω)
    exact le_of_lt Q.hℏ
  have hc : (∫ (x : ℝ), physHermite n (√(Q.m * Q.ω / Q.ℏ) * x) ^ 2 *
      Real.exp (- Q.m * Q.ω * x ^ 2 / Q.ℏ))
      = ∫ (x : ℝ), (physHermite n (c * x) *
      physHermite n (c * x)) * Real.exp (- c^2 * x ^ 2) := by
    congr
    funext x
    congr
    · simp only [c]
      exact pow_two _
    simp only [neg_mul, h1, c]
    field_simp
  rw [hc, physHermite_norm_cons]
  simp only [one_div, mul_inv_rev, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_pow, Complex.ofReal_ofNat, c]
  ring_nf
  have h1 : ↑n ! * (↑n ! : ℂ)⁻¹ = 1 := by
    rw [← IsUnit.eq_mul_inv_iff_mul_eq]
    simp only [inv_inv, one_mul, c]
    refine IsUnit.inv ?_
    simp only [isUnit_iff_ne_zero, ne_eq, cast_eq_zero, c]
    exact factorial_ne_zero n
  rw [h1]
  repeat rw [mul_assoc]
  have h1 : ((1 / 2) ^ n * (2 : ℂ) ^ n) = 1:= by
    rw [← IsUnit.eq_mul_inv_iff_mul_eq]
    · simp
    · simp
  rw [h1]
  simp only [mul_one, one_mul, c]
  have h1 : Complex.ofReal |(√(Q.m * (Q.ω * Q.ℏ⁻¹)))⁻¹| = (√(Q.m * (Q.ω * Q.ℏ⁻¹)))⁻¹ := by
    congr
    apply abs_of_nonneg
    refine inv_nonneg_of_nonneg ?_
    exact Real.sqrt_nonneg (Q.m * (Q.ω * Q.ℏ⁻¹))
  rw [h1]
  have h1 : √(Q.m * (Q.ω * (Real.pi⁻¹ * Q.ℏ⁻¹))) = (√(Q.m * (Q.ω * Q.ℏ⁻¹))) * (√(Real.pi⁻¹)) := by
    trans √((Q.m * (Q.ω * Q.ℏ⁻¹)) * Real.pi⁻¹)
    · ring_nf
    refine Real.sqrt_mul' (Q.m * (Q.ω * Q.ℏ⁻¹)) ?_
    refine inv_nonneg_of_nonneg ?_
    exact Real.pi_nonneg
  rw [h1]
  simp only [Real.sqrt_inv, mul_comm, Complex.ofReal_mul, Complex.ofReal_inv, c]
  ring_nf
  have h1 : ↑√Real.pi * (↑√Real.pi : ℂ)⁻¹ =1 := by
    rw [← IsUnit.eq_mul_inv_iff_mul_eq]
    simp only [inv_inv, one_mul, c]
    simp only [isUnit_iff_ne_zero, ne_eq, inv_eq_zero, Complex.ofReal_eq_zero, c]
    refine Real.sqrt_ne_zero'.mpr ?_
    exact Real.pi_pos
  rw [h1]
  simp only [one_mul, c]
  suffices h2 : IsUnit (↑√(Q.m * Q.ω * Q.ℏ⁻¹) : ℂ) by
    rw [mul_comm, ← IsUnit.eq_mul_inv_iff_mul_eq h2]
    simp only [one_mul, c]
  simp only [isUnit_iff_ne_zero, ne_eq, Complex.ofReal_eq_zero, c]
  refine Real.sqrt_ne_zero'.mpr ?_
  rw [propext (lt_mul_inv_iff₀ Q.hℏ)]
  simp only [zero_mul, c]
  exact mul_pos Q.hm Q.hω

/-- The eigen-functions of the quantum harmonic oscillator are orthogonal. -/
lemma eigenfunction_orthogonal {n p : ℕ} (hnp : n ≠ p) :
    ⟪HilbertSpace.mk (Q.eigenfunction_memHS n),
      HilbertSpace.mk (Q.eigenfunction_memHS p)⟫_ℂ = 0 := by
  rw [inner_mk_mk]
  conv_lhs =>
    enter [2, x]
    rw [eigenfunction_conj, Q.eigenfunction_mul n p]
  rw [MeasureTheory.integral_mul_left]
  rw [integral_complex_ofReal]
  let c := √(Q.m * Q.ω / Q.ℏ)
  have h1 : c ^ 2 = Q.m * Q.ω / Q.ℏ := by
    trans c * c
    · exact pow_two c
    simp only [c]
    refine Real.mul_self_sqrt ?_
    refine div_nonneg ?_ ?_
    exact (mul_nonneg_iff_of_pos_left Q.hm).mpr (le_of_lt Q.hω)
    exact le_of_lt Q.hℏ
  have hc : (∫ (x : ℝ), (physHermite n (c * x) * physHermite p (c * x)) *
      Real.exp (-Q.m * Q.ω * x ^ 2 / Q.ℏ))
      = ∫ (x : ℝ), (physHermite n (c * x) * physHermite p (c * x)) *
      Real.exp (- c^2 * x ^ 2) := by
    congr
    funext x
    congr
    simp only [neg_mul, h1, c]
    field_simp
  rw [hc, physHermite_orthogonal_cons hnp]
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
      mul_one, Complex.ofReal_zero, mul_zero, c]

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

end HarmonicOscillator
end OneDimension
end QuantumMechanics
