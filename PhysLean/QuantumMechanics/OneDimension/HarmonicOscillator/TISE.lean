/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Eigenfunction
/-!

# The time-independent Schrodinger equation

-/


namespace QuantumMechanics

namespace OneDimension
namespace HarmonicOscillator

variable (Q : HarmonicOscillator)

open Nat
open PhysLean
open HilbertSpace


/-- The eigenvalues for the Harmonic oscillator. -/
noncomputable def eigenValue (n : ℕ) : ℝ := (n + 1/2) * Q.ℏ * Q.ω

lemma deriv_eigenfunction_zero : deriv (Q.eigenfunction  0) =
    Complex.ofReal (- Q.m * Q.ω / Q.ℏ) • Complex.ofReal * Q.eigenfunction 0 := by
  rw [eigenfunction_zero]
  simp only [neg_mul, deriv_const_mul_field', Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_mul, Algebra.smul_mul_assoc]
  ext x
  have h1 : deriv (fun x => Complex.exp (-(↑Q.m * ↑Q.ω * ↑x ^ 2) / (2 * ↑Q.ℏ))) x =
      - Q.m * Q.ω * x /Q.ℏ* Complex.exp (-(↑Q.m * ↑Q.ω * ↑x ^ 2) / (2 * ↑Q.ℏ)) := by
    trans deriv (Complex.exp ∘ (fun x => -(↑Q.m * ↑Q.ω * ↑x ^ 2) / (2 * ↑Q.ℏ))) x
    · rfl
    rw [deriv_comp]
    simp only [Complex.deriv_exp, deriv_div_const, deriv.neg', differentiableAt_const,
      deriv_const_mul_field', neg_mul]
    have h1' : deriv (fun x => (Complex.ofReal x) ^ 2) x = 2 * x := by
      trans deriv (fun x => Complex.ofReal x * Complex.ofReal x) x
      · apply congr
        apply congrArg
        funext x
        ring
        rfl
      rw [deriv_mul]
      simp only [Complex.deriv_ofReal, one_mul, mul_one]
      ring
      exact Complex.differentiableAt_ofReal
      exact Complex.differentiableAt_ofReal
    rw [h1']
    field_simp
    ring
    exact Complex.differentiableAt_exp
    refine DifferentiableAt.mul_const ?_ _
    refine differentiableAt_neg_iff.mpr ?_
    refine DifferentiableAt.const_mul ?_ _
    refine DifferentiableAt.pow ?_ 2
    exact Complex.differentiableAt_ofReal
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  rw [h1]
  ring



lemma deriv_deriv_eigenfunction_zero (x : ℝ) : deriv (deriv (Q.eigenfunction 0)) x =
    - (Q.m * Q.ω) / Q.ℏ * (Q.eigenfunction 0 x +
    x * (-(Q.m * Q.ω) / Q.ℏ * x * Q.eigenfunction 0 x)) := by
  simp [deriv_eigenfunction_zero]
  trans  deriv (fun x => (-(↑Q.m * ↑Q.ω) / ↑Q.ℏ) • (Complex.ofReal x * Q.eigenfunction 0 x)) x
  · congr
    funext x
    simp
  simp
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp only [differentiableAt_const, deriv_const_mul_field', Complex.deriv_ofReal, mul_one]
  rw [deriv_eigenfunction_zero]
  simp only [neg_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring_nf
  left
  trivial

lemma schrodingerOperator_eigenfunction_zero (x : ℝ) :
    Q.schrodingerOperator (Q.eigenfunction 0) x = Q.eigenValue 0 * Q.eigenfunction 0 x := by
  simp [schrodingerOperator]
  rw [deriv_deriv_eigenfunction_zero, eigenValue]
  have hm' := Complex.ofReal_ne_zero.mpr Q.m_ne_zero
  have hℏ' := Complex.ofReal_ne_zero.mpr Q.ℏ_ne_zero
  field_simp
  ring

lemma deriv_physHermiteFun_succ (n : ℕ) :
    deriv (fun x => Complex.ofReal (physHermiteFun (n + 1) (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x))) =
    fun x =>
    Complex.ofReal (Real.sqrt (Q.m * Q.ω / Q.ℏ)) * 2 * (n + 1) *
    physHermiteFun n (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x) := by
  funext x
  trans deriv (Complex.ofReal ∘ physHermiteFun (n + 1) ∘
    fun (x : ℝ) => (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x)) x
  · rfl
  rw [fderiv_comp_deriv]
  rw [fderiv_comp_deriv]
  simp only [Function.comp_apply, fderiv_eq_smul_deriv, smul_eq_mul, Complex.deriv_ofReal,
    Complex.real_smul, Complex.ofReal_mul, mul_one]
  rw [deriv_mul]
  simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add]
  rw [deriv_physHermiteFun]
  simp only [Pi.natCast_def, Pi.mul_apply, Pi.ofNat_apply, cast_ofNat, Pi.add_apply, Pi.one_apply,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one]
  simp only [cast_add, cast_one, add_tsub_cancel_right]
  ring
  all_goals fun_prop

lemma deriv_eigenfunction_succ (n : ℕ) :
    deriv (Q.eigenfunction (n + 1)) = fun x =>
    Complex.ofReal (1/Real.sqrt (2 ^ (n + 1) * (n + 1) !)) •
    (((Real.sqrt (Q.m * Q.ω / Q.ℏ)) * 2 * (↑n + 1) *
      ↑(physHermiteFun n (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x))
      + ↑(physHermiteFun (n + 1) (Real.sqrt (Q.m * Q.ω / Q.ℏ) * x)) *
      (-(Q.m * Q.ω) / Q.ℏ * ↑x)) * Q.eigenfunction 0 x) := by
  funext x
  rw [eigenfunction_eq_mul_eigenfunction_zero]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, Complex.ofReal_mul,
    Complex.ofReal_inv, differentiableAt_const, deriv_mul, deriv_const', zero_mul, mul_zero,
    add_zero, zero_add, smul_eq_mul]
  rw [deriv_physHermiteFun_succ, deriv_eigenfunction_zero]
  simp only [neg_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

lemma deriv_deriv_eigenfunction_succ (n : ℕ) (x : ℝ) :
    deriv (fun x => deriv (Q.eigenfunction (n + 1)) x) x =
    Complex.ofReal (1/Real.sqrt (2 ^ (n + 1) * (n + 1) !)) *
      ((↑√(Q.m * Q.ω / Q.ℏ) * 2 * (↑n + 1) *
      deriv (fun x => ↑(physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x))) x +
      (-(↑Q.m * ↑Q.ω) / ↑Q.ℏ) * ↑√(Q.m * Q.ω / Q.ℏ) * (4 * (↑n + 1) * x) *
      (physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x)) +
      (-(Q.m * Q.ω) / Q.ℏ) * (1 + (-(Q.m * Q.ω) / Q.ℏ) * x ^ 2) *
      (physHermiteFun (n + 1) (√(Q.m * Q.ω / Q.ℏ) * x))) * Q.eigenfunction 0 x) := by
  rw [deriv_eigenfunction_succ]
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, Complex.ofReal_mul,
    Complex.ofReal_inv, smul_eq_mul, differentiableAt_const, deriv_const_mul_field',
    mul_eq_mul_left_iff, _root_.mul_eq_zero, inv_eq_zero, Complex.ofReal_eq_zero, cast_nonneg,
    Real.sqrt_eq_zero, cast_eq_zero, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
    not_false_eq_true, pow_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
  left
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  rw [deriv_eigenfunction_zero]
  simp [← mul_assoc, ← add_mul]
  left
  rw [deriv_add (by fun_prop) (by fun_prop)]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp only [differentiableAt_const, deriv_mul, deriv_const', zero_mul, mul_zero, add_zero,
    deriv_add, zero_add]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp only [deriv_mul_const_field', Complex.deriv_ofReal, mul_one]
  rw [deriv_physHermiteFun_succ]
  simp only
  ring

lemma deriv_deriv_eigenfunction_one (x : ℝ) :
    deriv (fun x => deriv (Q.eigenfunction 1) x) x =
      Complex.ofReal (1/Real.sqrt (2 ^ 1 * 1 !)) *
      ((((-(Q.m * Q.ω) / Q.ℏ) * ↑√(Q.m * Q.ω / Q.ℏ) * (4 * x) +
        (-(Q.m * Q.ω) / Q.ℏ) * (1 + (-(Q.m * Q.ω) / Q.ℏ) * x ^ 2) * (2* (√(Q.m * Q.ω / Q.ℏ) * x)))) *
        Q.eigenfunction 0 x) := by
  rw [deriv_deriv_eigenfunction_succ]
  congr 2
  simp [physHermiteFun_eq_aeval_physHermite, physHermite_one, Polynomial.aeval]

lemma schrodingerOperator_eigenfunction_one (x : ℝ)  :
    Q.schrodingerOperator (Q.eigenfunction 1) x=
    Q.eigenValue 1 * Q.eigenfunction 1 x := by
  simp [schrodingerOperator, eigenValue]
  rw [deriv_deriv_eigenfunction_one]
  have hm' := Complex.ofReal_ne_zero.mpr Q.m_ne_zero
  have hℏ := Q.ℏ_ne_zero
  have hℏ' := Complex.ofReal_ne_zero.mpr Q.ℏ_ne_zero
  rw [Q.eigenfunction_eq_mul_eigenfunction_zero 1]
  simp [physHermiteFun_eq_aeval_physHermite, physHermite_one, Polynomial.aeval]
  ring_nf
  have hl : (Complex.ofReal √2 * Q.ℏ * (↑Q.m * ↑√2 * ↑Q.ℏ ^ 2)) ≠ 0 := by
    simp_all
  field_simp [hl, hℏ]
  ring



lemma deriv_deriv_eigenfunction_succ_succ (n : ℕ) (x : ℝ) :
    deriv (fun x => deriv (Q.eigenfunction (n + 2)) x) x = (- Q.m * Q.ω / Q.ℏ) * (2 * (n + 2)
    + (1 + (-(Q.m * Q.ω) / Q.ℏ) * x ^ 2)) * Q.eigenfunction (n + 2) x := by
  trans Complex.ofReal (1/Real.sqrt (2 ^ (n + 1 + 1) * (n + 1 + 1) !)) *
        (((- Q.m * Q.ω / Q.ℏ) * (2 * (n + 2)
        + (1 + (-(Q.m * Q.ω) / Q.ℏ) * x ^ 2)) *
        (physHermiteFun (n + 2) (√(Q.m * Q.ω / Q.ℏ) * x))) * Q.eigenfunction 0 x)
  rw [deriv_deriv_eigenfunction_succ]
  congr 2
  trans (√(Q.m * Q.ω / Q.ℏ) * 2 * (n + 1 + 1) * (√(Q.m * Q.ω / Q.ℏ) *
    2 * (n + 1) * (physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x))) +
    (-(Q.m * Q.ω) / Q.ℏ) * √(Q.m * Q.ω / Q.ℏ) * (4 * (n + 1 + 1) * x) *
    (physHermiteFun (n + 1) (√(Q.m * Q.ω / Q.ℏ) * x)) +
    (-(Q.m * Q.ω) / Q.ℏ) * (1 + (-(Q.m * Q.ω) / Q.ℏ) * x ^ 2) * (physHermiteFun (n + 2) (√(Q.m * Q.ω / Q.ℏ) * x)))
  · rw [deriv_physHermiteFun_succ]
    simp
  trans ((Q.m * Q.ω / Q.ℏ) * 2 * (n + 1 + 1) * (2 * (n + 1) * (physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x))) +
        (- (Q.m * Q.ω) / Q.ℏ) * √(Q.m * Q.ω / Q.ℏ) * (4 * (n + 1 + 1) * x) *
        (physHermiteFun (n + 1) (√(Q.m * Q.ω / Q.ℏ) * x)) +
        (-(Q.m * Q.ω) / Q.ℏ) * (1 + (-(Q.m * Q.ω) / Q.ℏ) * x ^ 2) *
        (physHermiteFun (n + 2) (√(Q.m * Q.ω / Q.ℏ) * x)))
  · congr 2
    trans (↑√(Q.m * Q.ω / Q.ℏ) * ↑√(Q.m * Q.ω / Q.ℏ)) * 2 * (↑n + 1 + 1) *
    (2 * (↑n + 1) * ↑(physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x)))
    · ring
    congr 3
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_div]
    congr 1
    refine Real.mul_self_sqrt ?_
    refine div_nonneg ?_ ?_
    exact (mul_nonneg_iff_of_pos_left Q.hm).mpr (le_of_lt Q.hω)
    exact le_of_lt Q.hℏ
  trans (- Q.m * Q.ω / Q.ℏ) * (2 * (n + 1 + 1) *
        (2 * (√(Q.m * Q.ω / Q.ℏ) * x) * (physHermiteFun (n + 1) (√(Q.m * Q.ω / Q.ℏ) * x)) -
        2 * (n + 1) * (physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x)))
        + (1 + (-(Q.m * Q.ω) / Q.ℏ) * x ^ 2) * (physHermiteFun (n + 2) (√(Q.m * Q.ω / Q.ℏ) * x)))
  · ring
  trans (- Q.m * Q.ω / Q.ℏ) * (2 * (n + 1 + 1) * (physHermiteFun (n + 2) (√(Q.m * Q.ω / Q.ℏ) * x))
        + (1 + (-(Q.m * Q.ω) / Q.ℏ) * x ^ 2) * (physHermiteFun (n + 2) (√(Q.m * Q.ω / Q.ℏ) * x)))
  · congr
    conv_rhs =>
      rw [physHermiteFun_succ]
    simp
  ring
  · rw [Q.eigenfunction_eq_mul_eigenfunction_zero (n + 2)]
    ring

lemma schrodingerOperator_eigenfunction_succ_succ (n : ℕ) (x : ℝ) :
    Q.schrodingerOperator (Q.eigenfunction (n + 2)) x=
    Q.eigenValue (n + 2) * Q.eigenfunction (n + 2) x := by
  simp [schrodingerOperator, eigenValue]
  rw [Q.deriv_deriv_eigenfunction_succ_succ]
  have hm' := Complex.ofReal_ne_zero.mpr (Ne.symm (_root_.ne_of_lt Q.hm))
  have hℏ' := Complex.ofReal_ne_zero.mpr (Ne.symm (_root_.ne_of_lt Q.hℏ))
  field_simp
  ring

/-- The eigenfunctions satisfy the time-independent Schrodinger equation. -/
theorem schrodingerOperator_eigenfunction (n : ℕ) :
    Q.schrodingerOperator (Q.eigenfunction n) x =
    Q.eigenValue n * Q.eigenfunction n x :=
  match n with
  | 0 => Q.schrodingerOperator_eigenfunction_zero x
  | 1 => Q.schrodingerOperator_eigenfunction_one x
  | n + 2 => Q.schrodingerOperator_eigenfunction_succ_succ n x

open Filter Finset

open InnerProductSpace


end HarmonicOscillator
end OneDimension
end QuantumMechanics
