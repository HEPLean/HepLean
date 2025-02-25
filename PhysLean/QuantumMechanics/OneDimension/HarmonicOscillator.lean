/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
/-!

# 1d Harmonic Oscillator

The quantum harmonic oscillator in 1d.
This file contains
- the definition of the Schrodinger operator
- the definition of eigenfunctions and eigenvalues of the Schrodinger operator in terms
  of Hermite polynomials
- proof that eigenfunctions and eigenvalues are indeed egienfunctions and eigenvalues.

## TODO
- Show that Schrodinger operator is linear.
- Show that eigenfunctions satisfy the completeness relation.

-/

/-!

## Some preliminary results about Complex.ofReal .

To be moved.

-/

lemma Complex.ofReal_hasDerivAt : HasDerivAt Complex.ofReal 1 x := by
  let f1 : ℂ → ℂ := id
  change HasDerivAt (f1 ∘ Complex.ofReal) 1 x
  apply HasDerivAt.comp_ofReal
  simp [f1]
  exact hasDerivAt_id _

@[simp]
lemma Complex.deriv_ofReal : deriv Complex.ofReal x = 1 := by
  exact HasDerivAt.deriv Complex.ofReal_hasDerivAt

@[fun_prop]
lemma Complex.differentiableAt_ofReal : DifferentiableAt ℝ Complex.ofReal x := by
  exact HasFDerivAt.differentiableAt Complex.ofReal_hasDerivAt

/-!

The 1d Harmonic Oscillator

-/
namespace QuantumMechanics

namespace OneDimension
namespace HarmonicOscillator

open Nat
open PhysLean
/-- The Schrodinger Operator for the Harmonic oscillator. -/
noncomputable def schrodingerOperator (m ℏ ω : ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ := fun y =>
  - ℏ ^ 2 / (2 * m) * (deriv (fun y => deriv ψ y) y) + 1/2 *
  m * ω^2 * y^2 * ψ y

/-- The eigenfunctions for the Harmonic oscillator.
  Note: eigenfunctions are not defined as members of the hilbert space.
  See `eigenVector` for this. -/
noncomputable def eigenfunction (m ℏ ω : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  1/Real.sqrt (2 ^ n * n !) * Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ))) *
  physHermiteFun n (Real.sqrt (m * ω /ℏ) * x) * Real.exp (- m * ω * x^2 / (2 * ℏ))

lemma eigenfunction_eq (m ℏ ω : ℝ) (n : ℕ) :
    eigenfunction m ℏ ω n = fun (x : ℝ) =>
    ((1/Real.sqrt (2 ^ n * n !) * Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ)))) *
    Complex.ofReal (physHermiteFun n (Real.sqrt (m * ω / ℏ) * x) *
    Real.exp (- m * ω * x^2 / (2 * ℏ)))) := by
  funext x
  simp [eigenfunction]
  ring

/-- The eigenvalues for the Harmonic oscillator. -/
noncomputable def eigenValue (ℏ ω : ℝ) (n : ℕ) : ℝ := (n + 1/2) * ℏ * ω

lemma eigenfunction_zero (m ℏ ω : ℝ) : eigenfunction m ℏ ω 0 = fun (x : ℝ) =>
    (Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ))) * Complex.exp (- m * ω * x^2 / (2 * ℏ))) := by
  funext x
  simp [eigenfunction, physHermiteFun]

lemma deriv_eigenfunction_zero (m ℏ ω : ℝ) : deriv (eigenfunction m ℏ ω 0) =
    Complex.ofReal (- m * ω / ℏ) • Complex.ofReal * eigenfunction m ℏ ω 0 := by
  rw [eigenfunction_zero m ℏ ω]
  simp only [neg_mul, deriv_const_mul_field', Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_mul, Algebra.smul_mul_assoc]
  ext x
  have h1 : deriv (fun x => Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))) x =
      - m * ω * x /ℏ* Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ)) := by
    trans deriv (Complex.exp ∘ (fun x => -(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))) x
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

@[fun_prop]
lemma eigenfunction_zero_differentiableAt (x : ℝ) :
    DifferentiableAt ℝ (eigenfunction m ℏ ω 0) x := by
  rw [eigenfunction_zero]
  fun_prop

lemma deriv_deriv_eigenfunction_zero (m ℏ ω : ℝ) (x : ℝ) :
    deriv (fun x => deriv (eigenfunction m ℏ ω 0) x) x =
    - (↑m * ↑ω) / ↑ℏ * (eigenfunction m ℏ ω 0 x
    + ↑x * (-(↑m * ↑ω) / ↑ℏ * ↑x * eigenfunction m ℏ ω 0 x)) := by
  simp [deriv_eigenfunction_zero]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp only [differentiableAt_const, deriv_const_mul_field', Complex.deriv_ofReal, mul_one]
  rw [deriv_eigenfunction_zero]
  simp only [neg_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

lemma schrodingerOperator_eigenfunction_zero (m ℏ ω : ℝ) (x : ℝ)
    (hm : m ≠ 0) (hℏ : ℏ ≠ 0) :
    schrodingerOperator m ℏ ω (eigenfunction m ℏ ω 0) x=
    eigenValue ℏ ω 0 * eigenfunction m ℏ ω 0 x := by
  simp [schrodingerOperator]
  rw [deriv_deriv_eigenfunction_zero, eigenValue]
  have hm' := Complex.ofReal_ne_zero.mpr hm
  have hℏ' := Complex.ofReal_ne_zero.mpr hℏ
  field_simp
  ring

lemma eigenFunction_succ_eq_mul_eigenfunction_zero (m ℏ ω : ℝ) (n : ℕ) :
    eigenfunction m ℏ ω (n + 1) = fun x => Complex.ofReal (1/Real.sqrt (2 ^ (n + 1) * (n + 1)!))
    * Complex.ofReal (physHermiteFun (n + 1) (Real.sqrt (m * ω / ℏ) * x))
    * eigenfunction m ℏ ω 0 x := by
  funext x
  rw [eigenfunction, eigenfunction_zero]
  repeat rw [mul_assoc]
  congr 1
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
    Complex.ofReal_inv]
  rw [mul_comm, mul_assoc]
  congr 1
  simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring_nf

lemma deriv_physHermiteFun_succ (m ℏ ω : ℝ) (n : ℕ) :
    deriv (fun x => Complex.ofReal (physHermiteFun (n + 1) (Real.sqrt (m * ω / ℏ) * x))) =
    fun x =>
    Complex.ofReal (Real.sqrt (m * ω / ℏ)) * 2 * (n + 1) *
    physHermiteFun n (Real.sqrt (m * ω / ℏ) * x) := by
  funext x
  trans deriv (Complex.ofReal ∘ physHermiteFun (n + 1) ∘
    fun (x : ℝ) => (Real.sqrt (m * ω / ℏ) * x)) x
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

lemma deriv_eigenFunction_succ (m ℏ ω : ℝ) (n : ℕ) :
    deriv (eigenfunction m ℏ ω (n + 1)) = fun x =>
    Complex.ofReal (1/Real.sqrt (2 ^ (n + 1) * (n + 1) !)) •
    (((Real.sqrt (m * ω / ℏ)) * 2 * (↑n + 1) *
      ↑(physHermiteFun n (Real.sqrt (m * ω / ℏ) * x))
      + ↑(physHermiteFun (n + 1) (Real.sqrt (m * ω / ℏ) * x)) *
      (-(↑m * ↑ω) / ↑ℏ * ↑x)) * eigenfunction m ℏ ω 0 x) := by
  funext x
  rw [eigenFunction_succ_eq_mul_eigenfunction_zero]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, one_div, mul_inv_rev, Complex.ofReal_mul,
    Complex.ofReal_inv, differentiableAt_const, deriv_mul, deriv_const', zero_mul, mul_zero,
    add_zero, zero_add, smul_eq_mul]
  rw [deriv_physHermiteFun_succ, deriv_eigenfunction_zero]
  simp only [neg_mul, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_mul, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

lemma deriv_deriv_eigenFunction_succ (m ℏ ω : ℝ) (n : ℕ) (x : ℝ) :
    deriv (fun x => deriv (eigenfunction m ℏ ω (n + 1)) x) x =
    Complex.ofReal (1/Real.sqrt (2 ^ (n + 1) * (n + 1) !)) *
      ((↑√(m * ω / ℏ) * 2 * (↑n + 1) *
      deriv (fun x => ↑(physHermiteFun n (√(m * ω / ℏ) * x))) x +
      (-(↑m * ↑ω) / ↑ℏ) * ↑√(m * ω / ℏ) * (4 * (↑n + 1) * x) *
      (physHermiteFun n (√(m * ω / ℏ) * x)) +
      (-(↑m * ↑ω) / ↑ℏ) * (1 + (-(↑m * ↑ω) / ↑ℏ) * x ^ 2) *
      (physHermiteFun (n + 1) (√(m * ω / ℏ) * x))) * eigenfunction m ℏ ω 0 x) := by
  rw [deriv_eigenFunction_succ]
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

lemma deriv_deriv_eigenFunction_one (m ℏ ω : ℝ) (x : ℝ) :
    deriv (fun x => deriv (eigenfunction m ℏ ω 1) x) x =
      Complex.ofReal (1/Real.sqrt (2 ^ 1 * 1 !)) *
      ((((-(↑m * ↑ω) / ↑ℏ) * ↑√(m * ω / ℏ) * (4 * x) +
        (-(↑m * ↑ω) / ↑ℏ) * (1 + (-(↑m * ↑ω) / ↑ℏ) * x ^ 2) * (2* (√(m * ω / ℏ) * x)))) *
        eigenfunction m ℏ ω 0 x) := by
  rw [deriv_deriv_eigenFunction_succ]
  congr 2
  simp [physHermiteFun_eq_aeval_physHermite, physHermite_one, Polynomial.aeval]

lemma schrodingerOperator_eigenfunction_one (m ℏ ω : ℝ) (x : ℝ) (hm : m ≠ 0) (hℏ : ℏ ≠ 0) :
    schrodingerOperator m ℏ ω (eigenfunction m ℏ ω 1) x=
    eigenValue ℏ ω 1 * eigenfunction m ℏ ω 1 x := by
  simp [schrodingerOperator, eigenValue]
  rw [deriv_deriv_eigenFunction_one]
  have hm' := Complex.ofReal_ne_zero.mpr hm
  have hℏ' := Complex.ofReal_ne_zero.mpr hℏ
  rw [eigenFunction_succ_eq_mul_eigenfunction_zero]
  simp [physHermiteFun_eq_aeval_physHermite, physHermite_one, Polynomial.aeval]
  ring_nf
  have hl : (Complex.ofReal √2 * ↑ℏ * (↑m * ↑√2 * ↑ℏ ^ 2)) ≠ 0 := by
    simp_all
  field_simp [hl]
  ring

lemma deriv_deriv_eigenFunction_succ_succ (m ℏ ω : ℝ) (n : ℕ) (x : ℝ) (hm : 0 < m) (hℏ : 0 < ℏ)
    (hω : 0 ≤ ω) :
    deriv (fun x => deriv (eigenfunction m ℏ ω (n + 2)) x) x = (- m * ω / ℏ) * (2 * (n + 2)
    + (1 + (-(m * ω) / ℏ) * x ^ 2)) * eigenfunction m ℏ ω (n + 2) x := by
  trans Complex.ofReal (1/Real.sqrt (2 ^ (n + 1 + 1) * (n + 1 + 1) !)) *
        (((- m * ω / ℏ) * (2 * (n + 2)
        + (1 + (-(m * ω) / ℏ) * x ^ 2)) *
        (physHermiteFun (n + 2) (√(m * ω / ℏ) * x))) * eigenfunction m ℏ ω 0 x)
  rw [deriv_deriv_eigenFunction_succ]
  congr 2
  trans (√(m * ω / ℏ) * 2 * (n + 1 + 1) * (√(m * ω / ℏ) *
    2 * (n + 1) * (physHermiteFun n (√(m * ω / ℏ) * x))) +
    (-(m * ω) / ℏ) * √(m * ω / ℏ) * (4 * (n + 1 + 1) * x) *
    (physHermiteFun (n + 1) (√(m * ω / ℏ) * x)) +
    (-(m * ω) / ℏ) * (1 + (-(m * ω) / ℏ) * x ^ 2) * (physHermiteFun (n + 2) (√(m * ω / ℏ) * x)))
  · rw [deriv_physHermiteFun_succ]
    simp
  trans ((m * ω / ℏ) * 2 * (n + 1 + 1) * (2 * (n + 1) * (physHermiteFun n (√(m * ω / ℏ) * x))) +
        (- (m * ω) / ℏ) * √(m * ω / ℏ) * (4 * (n + 1 + 1) * x) *
        (physHermiteFun (n + 1) (√(m * ω / ℏ) * x)) +
        (-(m * ω) / ℏ) * (1 + (-(m * ω) / ℏ) * x ^ 2) *
        (physHermiteFun (n + 2) (√(m * ω / ℏ) * x)))
  · congr 2
    trans (↑√(m * ω / ℏ) * ↑√(m * ω / ℏ)) * 2 * (↑n + 1 + 1) *
    (2 * (↑n + 1) * ↑(physHermiteFun n (√(m * ω / ℏ) * x)))
    · ring
    congr 3
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_div]
    congr 1
    refine Real.mul_self_sqrt ?_
    refine div_nonneg ?_ ?_
    exact (mul_nonneg_iff_of_pos_left hm).mpr hω
    exact le_of_lt hℏ
  trans (- m * ω / ℏ) * (2 * (n + 1 + 1) *
        (2 * (√(m * ω / ℏ) * x) * (physHermiteFun (n + 1) (√(m * ω / ℏ) * x)) -
        2 * (n + 1) * (physHermiteFun n (√(m * ω / ℏ) * x)))
        + (1 + (-(m * ω) / ℏ) * x ^ 2) * (physHermiteFun (n + 2) (√(m * ω / ℏ) * x)))
  · ring
  trans (- m * ω / ℏ) * (2 * (n + 1 + 1) * (physHermiteFun (n + 2) (√(m * ω / ℏ) * x))
        + (1 + (-(m * ω) / ℏ) * x ^ 2) * (physHermiteFun (n + 2) (√(m * ω / ℏ) * x)))
  · congr
    conv_rhs =>
      rw [physHermiteFun_succ]
    simp
  ring
  · rw [eigenFunction_succ_eq_mul_eigenfunction_zero]
    ring

lemma schrodingerOperator_eigenfunction_succ_succ (m ℏ ω : ℝ) (n : ℕ) (x : ℝ)
    (hm : 0 < m) (hℏ : 0 < ℏ) (hω : 0 ≤ ω) :
    schrodingerOperator m ℏ ω (eigenfunction m ℏ ω (n + 2)) x=
    eigenValue ℏ ω (n + 2) * eigenfunction m ℏ ω (n + 2) x := by
  simp [schrodingerOperator, eigenValue]
  rw [deriv_deriv_eigenFunction_succ_succ _ _ _ _ _ hm hℏ hω]
  have hm' := Complex.ofReal_ne_zero.mpr (Ne.symm (_root_.ne_of_lt hm))
  have hℏ' := Complex.ofReal_ne_zero.mpr (Ne.symm (_root_.ne_of_lt hℏ))
  field_simp
  ring

/-- The eigenfunctions satisfy the time-independent Schrodinger equation. -/
theorem schrodingerOperator_eigenfunction (m ℏ ω : ℝ) (n : ℕ) (x : ℝ)
    (hm : 0 < m) (hℏ : 0 < ℏ) (hω : 0 ≤ ω) :
    schrodingerOperator m ℏ ω (eigenfunction m ℏ ω n) x =
    eigenValue ℏ ω n * eigenfunction m ℏ ω n x :=
  match n with
  | 0 => schrodingerOperator_eigenfunction_zero m ℏ ω x
    (Ne.symm (_root_.ne_of_lt hm)) (Ne.symm (_root_.ne_of_lt hℏ))
  | 1 => schrodingerOperator_eigenfunction_one m ℏ ω x
    (Ne.symm (_root_.ne_of_lt hm)) (Ne.symm (_root_.ne_of_lt hℏ))
  | n + 2 => schrodingerOperator_eigenfunction_succ_succ m ℏ ω n x hm hℏ hω

open Filter Finset

/-- A simplification of the product of two eigen-functions. -/
lemma eigenFunction_mul (m ℏ ω : ℝ) (n p : ℕ) (hℏ : 0 < ℏ) :
    (eigenfunction m ℏ ω n x) * (eigenfunction m ℏ ω p x) =
    ((1/Real.sqrt (2 ^ n * n !) * 1/Real.sqrt (2 ^ p * p !)) *
    ((Real.sqrt (m * ω / (Real.pi * ℏ))))) *
    Complex.ofReal ((physHermiteFun n (Real.sqrt (m * ω /ℏ) * x) *
    physHermiteFun p (Real.sqrt (m * ω /ℏ) * x)) * (Real.exp (- m * ω * x^2 / ℏ))) := by
  calc eigenfunction m ℏ ω n x * eigenfunction m ℏ ω p x
    _ = (1/Real.sqrt (2 ^ n * n !) * 1/Real.sqrt (2 ^ p * p !)) *
      (Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ))) *
      Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ)))) *
      (physHermiteFun n (Real.sqrt (m * ω /ℏ) * x) * physHermiteFun p (Real.sqrt (m * ω /ℏ) * x)) *
      (Real.exp (- m * ω * x^2 / (2 * ℏ)) * Real.exp (- m * ω * x^2 / (2 * ℏ))) := by
      simp only [eigenfunction, ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul,
        one_div, mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_pow, Complex.ofReal_ofNat, mul_one]
      ring
    _ = (1/Real.sqrt (2 ^ n * n !) * 1/Real.sqrt (2 ^ p * p !)) *
      ((Real.sqrt (m * ω / (Real.pi * ℏ)))) *
      (physHermiteFun n (Real.sqrt (m * ω /ℏ) * x) * physHermiteFun p (Real.sqrt (m * ω /ℏ) * x)) *
      (Real.exp (- m * ω * x^2 / ℏ)) := by
      congr 1
      · congr 1
        · congr 1
          · rw [← Complex.ofReal_mul]
            congr
            refine Real.mul_self_sqrt ?_
            exact Real.sqrt_nonneg (m * ω / (Real.pi * ℏ))
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

lemma eigenFunction_mul_self (m ℏ ω : ℝ) (n : ℕ) (hℏ : 0 < ℏ) :
    (eigenfunction m ℏ ω n x) * (eigenfunction m ℏ ω n x) =
    ((1/ (2 ^ n * n !)) * (Real.sqrt (m * ω / (Real.pi * ℏ)))) *
    Complex.ofReal ((physHermiteFun n (Real.sqrt (m * ω /ℏ) * x))^2 *
    (Real.exp (- m * ω * x^2 / ℏ))) := by
  calc eigenfunction m ℏ ω n x * eigenfunction m ℏ ω n x
    _ = (1/Real.sqrt (2 ^ n * n !) * 1/Real.sqrt (2 ^ n * n !)) *
      (Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ))) *
      Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ)))) *
      (physHermiteFun n (Real.sqrt (m * ω /ℏ) * x))^2 *
      (Real.exp (- m * ω * x^2 / (2 * ℏ)) * Real.exp (- m * ω * x^2 / (2 * ℏ))) := by
      simp only [eigenfunction, ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul,
        one_div, mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg,
        Complex.ofReal_pow, Complex.ofReal_ofNat, mul_one]
      ring
    _ = (1/ (2 ^ n * n !)) *
      ((Real.sqrt (m * ω / (Real.pi * ℏ)))) *
      (physHermiteFun n (Real.sqrt (m * ω /ℏ) * x))^2 * (Real.exp (- m * ω * x^2 / ℏ)) := by
      congr 1
      · congr 1
        · congr 1
          · trans 1 / ↑(√(2 ^ n * ↑n !) * ↑√(2 ^ n * ↑n !))
            · field_simp
            congr
            trans Complex.ofReal ((2 ^ n * ↑n !))
            · congr 1
              refine Real.mul_self_sqrt ?_
              refine Left.mul_nonneg ?_ ?_
              refine pow_nonneg ?_ n
              simp only [ofNat_nonneg]
              exact cast_nonneg' n !
            simp
          · rw [← Complex.ofReal_mul]
            congr
            refine Real.mul_self_sqrt ?_
            exact Real.sqrt_nonneg (m * ω / (Real.pi * ℏ))
      · rw [← Complex.ofReal_mul]
        congr
        rw [← Real.exp_add]
        simp only [neg_mul, Real.exp_eq_exp]
        field_simp
        ring
  simp only [one_div, mul_inv_rev, neg_mul, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-!

## Normalization of the wave functions.

-/

/-- The eigenfunctions of the harmonic osscilator are normalized. -/
lemma eigenFunction_normalized (m ℏ ω : ℝ) (n : ℕ) (hℏ : 0 < ℏ) (hm : 0 < m) (hω : 0 < ω) :
    ∫ x : ℝ, (eigenfunction m ℏ ω n x) * (eigenfunction m ℏ ω n x) = 1 := by
  conv_lhs =>
    enter [2, x]
    rw [eigenFunction_mul_self m ℏ ω n hℏ]
  rw [MeasureTheory.integral_mul_left, integral_complex_ofReal]
  let c := √(m * ω / ℏ)
  have h1 : c ^ 2 = m * ω / ℏ := by
    trans c * c
    · exact pow_two c
    simp only [c]
    refine Real.mul_self_sqrt ?_
    refine div_nonneg ?_ ?_
    exact (mul_nonneg_iff_of_pos_left hm).mpr (le_of_lt hω)
    exact le_of_lt hℏ
  have hc : (∫ (x : ℝ), physHermiteFun n (√(m * ω / ℏ) * x) ^ 2 * Real.exp (-m * ω * x ^ 2 / ℏ))
      = ∫ (x : ℝ), (physHermiteFun n (c * x) *
      physHermiteFun n (c * x)) * Real.exp (- c^2 * x ^ 2) := by
    congr
    funext x
    congr
    · simp only [c]
      exact pow_two _
    simp only [neg_mul, h1, c]
    field_simp
  rw [hc, physHermiteFun_norm_cons]
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
  have h1 : Complex.ofReal |(√(m * (ω * ℏ⁻¹)))⁻¹| = (√(m * (ω * ℏ⁻¹)))⁻¹ := by
    congr
    apply abs_of_nonneg
    refine inv_nonneg_of_nonneg ?_
    exact Real.sqrt_nonneg (m * (ω * ℏ⁻¹))
  rw [h1]
  have h1 : √(m * (ω * (Real.pi⁻¹ * ℏ⁻¹))) = (√(m * (ω * ℏ⁻¹))) * (√(Real.pi⁻¹)) := by
    trans √((m * (ω * ℏ⁻¹)) * Real.pi⁻¹)
    · ring_nf
    refine Real.sqrt_mul' (m * (ω * ℏ⁻¹)) ?_
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
  rw [mul_comm, ← IsUnit.eq_mul_inv_iff_mul_eq]
  simp only [one_mul, c]
  simp only [isUnit_iff_ne_zero, ne_eq, Complex.ofReal_eq_zero, c]
  refine Real.sqrt_ne_zero'.mpr ?_
  rw [propext (lt_mul_inv_iff₀ hℏ)]
  simp only [zero_mul, c]
  exact mul_pos hm hω

/-- The eigen-functions of the quantum harmonic oscillator are orthogonal. -/
lemma eigenFunction_orthogonal (m ℏ ω : ℝ) (n p : ℕ) (hℏ : 0 < ℏ) (hm : 0 < m) (hω : 0 < ω)
    (hnp : n ≠ p) : ∫ x : ℝ, (eigenfunction m ℏ ω n x) * (eigenfunction m ℏ ω p x) = 0 := by
  conv_lhs =>
    enter [2, x]
    rw [eigenFunction_mul m ℏ ω n p hℏ]
  rw [MeasureTheory.integral_mul_left]
  rw [integral_complex_ofReal]
  let c := √(m * ω / ℏ)
  have h1 : c ^ 2 = m * ω / ℏ := by
    trans c * c
    · exact pow_two c
    simp [c]
    refine Real.mul_self_sqrt ?_
    refine div_nonneg ?_ ?_
    exact (mul_nonneg_iff_of_pos_left hm).mpr (le_of_lt hω)
    exact le_of_lt hℏ
  have hc : (∫ (x : ℝ), (physHermiteFun n (c * x) * physHermiteFun p (c * x)) *
      Real.exp (-m * ω * x ^ 2 / ℏ))
      = ∫ (x : ℝ), (physHermiteFun n (c * x) * physHermiteFun p (c * x)) *
      Real.exp (- c^2 * x ^ 2) := by
    congr
    funext x
    congr
    simp [h1]
    field_simp
  rw [hc]
  rw [physHermiteFun_orthogonal_cons]
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
    mul_one, Complex.ofReal_zero, mul_zero, c]
  exact hnp

@[fun_prop]
lemma eigenFunction_intergrable (m ℏ ω : ℝ) (n : ℕ) (hℏ : 0 < ℏ) (hm : 0 < m) (hω : 0 < ω) :
    MeasureTheory.Integrable (eigenfunction m ℏ ω n) := by
  rw [eigenfunction_eq]
  apply MeasureTheory.Integrable.const_mul
  apply MeasureTheory.Integrable.ofReal
  change MeasureTheory.Integrable
    (fun x => (physHermiteFun n (√(m * ω / ℏ) * x)) *
    (Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))) MeasureTheory.volume
  have h1 : (fun x => (physHermiteFun n (√(m * ω / ℏ) * x)) *
      (Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))) =
      (fun x => (physHermiteFun n (√(m * ω / ℏ) * x)) *
      (Real.exp (- (m * ω / (2* ℏ)) * x ^ 2))) := by
    funext x
    simp only [neg_mul, mul_eq_mul_left_iff, Real.exp_eq_exp]
    left
    field_simp
  rw [h1]
  rw [physHermiteFun_eq_aeval_physHermite]
  apply guassian_integrable_polynomial_cons
  simp_all only [neg_mul, mul_pos_iff_of_pos_left, div_pos_iff_of_pos_left, ofNat_pos]

@[fun_prop]
lemma eigenFunction_aeStronglyMeasurable {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω)  (n : ℕ) : MeasureTheory.AEStronglyMeasurable (eigenfunction m ℏ ω n) := by
  apply MeasureTheory.Integrable.aestronglyMeasurable
  exact eigenFunction_intergrable m ℏ ω n hℏ hm hω

@[simp]
lemma eigenfunction_conj (m ℏ ω : ℝ) (n : ℕ) (x : ℝ) :
    (starRingEnd ℂ) (eigenfunction m ℏ ω n x) = eigenfunction m ℏ ω n x := by
  rw [eigenfunction_eq]
  simp only [ofNat_nonneg, pow_nonneg, Real.sqrt_mul, Complex.ofReal_mul, one_div, mul_inv_rev,
    neg_mul, map_mul, map_inv₀, Complex.conj_ofReal]

lemma eigenfunction_norm_eq (m ℏ ω : ℝ) (n : ℕ) (x : ℝ) :
    ‖eigenfunction m ℏ ω n x‖ ^ 2 = (eigenfunction m ℏ ω n x) * (eigenfunction m ℏ ω n x) := by
  rw [← Complex.conj_mul']
  simp

@[fun_prop]
lemma eigenFunction_square_intergrable (m ℏ ω : ℝ) (n : ℕ) (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) : MeasureTheory.Integrable (fun x => ‖eigenfunction m ℏ ω n x‖ ^ 2) := by
  refine MeasureTheory.integrable_of_integral_eq_one ?_
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  conv_lhs =>
    enter [2, x]
    rw [Complex.ofReal_pow]
    rw [eigenfunction_norm_eq]
  rw [eigenFunction_normalized m ℏ ω n hℏ hm hω]
  rfl

lemma eigenfunction_mem_hilbertSpace {m ℏ ω : ℝ}  (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (n : ℕ) : MeasureTheory.AEEqFun.mk (eigenfunction m ℏ ω n)
    (eigenFunction_aeStronglyMeasurable hℏ hm hω n) ∈ HilbertSpace := by
  exact (HilbertSpace.mem_iff'
    (eigenFunction_aeStronglyMeasurable hℏ hm hω n)).mpr (
    eigenFunction_square_intergrable m ℏ ω n hℏ hm hω)

open InnerProductSpace

/-- The eigen vectors of the quantum harmonic Osscilators as members of the Hilbert space. -/
noncomputable def eigenVector {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (n : ℕ) : HilbertSpace :=
  ⟨MeasureTheory.AEEqFun.mk (eigenfunction m ℏ ω n)
    (eigenFunction_aeStronglyMeasurable hℏ hm hω n),
    eigenfunction_mem_hilbertSpace hℏ hm hω n⟩

lemma coe_eigenVector_ae_eigenfunction {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (n : ℕ) :
    (eigenVector hℏ hm hω n) =ᶠ[MeasureTheory.ae MeasureTheory.volume]
    eigenfunction m ℏ ω n := by
  simp [eigenVector]
  exact MeasureTheory.AEEqFun.coeFn_mk (eigenfunction m ℏ ω n)
      (eigenFunction_aeStronglyMeasurable hℏ hm hω n)

/-- The eigenvectors are orthonormal within the Hilbert space. s-/
lemma eigenVector_orthonormal {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) : Orthonormal ℂ (eigenVector hℏ hm hω ) := by
  rw [orthonormal_iff_ite]
  intro n p
  trans ∫ x : ℝ, (eigenfunction m ℏ ω n x) * (eigenfunction m ℏ ω p x)
  · apply MeasureTheory.integral_congr_ae
    have hn_ae := coe_eigenVector_ae_eigenfunction hℏ hm hω n
    have hm_ae := coe_eigenVector_ae_eigenfunction hℏ hm hω p
    filter_upwards [hn_ae, hm_ae] with _ hf hg
    rw [hf, hg]
    simp
  · by_cases hnp : n = p
    · simp [hnp]
      exact eigenFunction_normalized m ℏ ω p hℏ hm hω
    · simp [hnp]
      exact eigenFunction_orthogonal m ℏ ω n p hℏ hm hω hnp

/-

## Completeness

Completeness of the eigenfunctions follows from Plancherel's theorem.

The steps of this proof are:

1. Prove that if `f` is orthogonal to all eigenvectors then the Fourier transform of
  it muliplied by `exp(-c x^2)` for a `0<c` is zero.
  Part of this is using the concept of `dominated_convergence`.
2. Use 'Plancherel's theorem' to show that `f` is zero.

-/
open MeasureTheory


lemma orthogonal_eigenFunction_of_mem_orthogonal {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪eigenVector hℏ hm hω n, ⟨AEEqFun.mk f hf, hb⟩⟫_ℂ = 0) (n : ℕ) :
    ∫ (x : ℝ), (eigenfunction m ℏ ω n x) * f x = 0 := by
  have hn_ae := coe_eigenVector_ae_eigenfunction hℏ hm hω n
  have hf_ae : ↑↑(⟨AEEqFun.mk f hf, hb⟩ : HilbertSpace) =ᶠ[ae volume] f := by
    exact AEEqFun.coeFn_mk f hf
  rw [← hOrth n]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hn_ae, hf_ae] with _ hf hg
  rw [hf, hg]
  simp

lemma mul_eigenfunction_integrable {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hmem : AEEqFun.mk f hf ∈ HilbertSpace) :
    MeasureTheory.Integrable (fun x => (eigenfunction m ℏ ω n x) * f x) := by
  have h1 := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (eigenVector hℏ hm hω n)
    ⟨(AEEqFun.mk f hf), hmem⟩
  refine (integrable_congr   ?_).mp h1
  simp
  apply Filter.EventuallyEq.mul
  swap
  · exact AEEqFun.coeFn_mk f hf
  trans (fun x => (starRingEnd ℂ) (eigenfunction m ℏ ω n x))
  · apply Filter.EventuallyEq.fun_comp
    exact coe_eigenVector_ae_eigenfunction hℏ hm hω n
  · apply Filter.EventuallyEq.of_eq
    funext x
    exact eigenfunction_conj m ℏ ω n x

lemma orthogonal_physHermiteFun_of_mem_orthogonal {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪eigenVector hℏ hm hω n, ⟨AEEqFun.mk f hf, hb⟩⟫_ℂ = 0) (n : ℕ) :
    ∫ (x : ℝ), (physHermiteFun n (√(m * ω / ℏ) * x)) * (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ))))
    = 0 := by
  have h1 := orthogonal_eigenFunction_of_mem_orthogonal hℏ hm hω f hf hb hOrth n
  have h2 : (fun (x : ℝ ) =>
          (1 / ↑√(2 ^ n * ↑n !) * ↑√√(m * ω / (Real.pi * ℏ)) : ℂ) *
            (physHermiteFun n (√(m * ω / ℏ) * x) * f x  * Real.exp (-m * ω * x ^ 2 / (2 * ℏ))))
    = fun x => eigenfunction m ℏ ω n x * f x := by
    funext x
    simp [eigenfunction_eq]
    ring
  rw [← h2] at h1
  rw [MeasureTheory.integral_mul_left] at h1
  simp at h1
  have h0 : n ! ≠ 0 := by
    exact factorial_ne_zero n
  have h0' : √(m * ω / (Real.pi * ℏ)) ≠ 0 := by
    simp
    refine Real.sqrt_ne_zero'.mpr ?_
    refine div_pos ?_ ?_
    · exact mul_pos hm hω
    · apply mul_pos Real.pi_pos hℏ
  simp [h0, h0'] at h1
  rw [← h1]
  congr
  funext x
  simp
  ring

lemma mul_physHermiteFun_integrable {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace)  (n : ℕ) :
    MeasureTheory.Integrable (fun x => (physHermiteFun n (√(m * ω / ℏ) * x)) *
      (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ))))) := by
  have h2 : (1 / ↑√(2 ^ n * ↑n !) * ↑√√(m * ω / (Real.pi * ℏ)) : ℂ) • (fun (x : ℝ ) =>
            (physHermiteFun n (√(m * ω / ℏ) * x) * (f x  * Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))))
    = fun x => eigenfunction m ℏ ω n x * f x := by
    funext x
    simp [eigenfunction_eq]
    ring
  have h1 := mul_eigenfunction_integrable hℏ hm hω f hf hb (n := n)
  rw [← h2] at h1
  rw [IsUnit.integrable_smul_iff] at h1
  exact h1
  simp
  apply And.intro
  · exact factorial_ne_zero n
  · apply Real.sqrt_ne_zero'.mpr
    refine div_pos ?_ ?_
    · exact mul_pos hm hω
    · apply mul_pos Real.pi_pos hℏ

lemma orthogonal_polynomial_of_mem_orthogonal {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪eigenVector hℏ hm hω n, ⟨AEEqFun.mk f hf, hb⟩⟫_ℂ = 0)
    (P : Polynomial ℤ) :
    ∫ x : ℝ, ((fun x => P.aeval  x) (√(m * ω / ℏ)  * x)) *
      (f x * Real.exp (- m * ω * x^2 / (2 * ℏ))) = 0 := by
  have h1 := polynomial_mem_physHermiteFun_span P
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h1
  obtain ⟨a, ha⟩ := h1
  have h2 : (fun x => ↑((fun x => P.aeval  x) (√(m * ω / ℏ)  * x)) * (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))))
    = (fun x => ∑ r ∈ a.support, a r * (physHermiteFun r (√(m * ω / ℏ) * x)) * (f x * Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))) := by
    funext x
    rw [← ha]
    rw [← Finset.sum_mul]
    congr
    rw [Finsupp.sum]
    simp
  rw [h2]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro x hx
    simp [mul_assoc]
    rw [integral_mul_left]
    simp
    right
    rw [← orthogonal_physHermiteFun_of_mem_orthogonal hℏ hm hω f hf hb hOrth x]
    congr
    funext x
    simp
    left
    left
    congr 1
    ring
  · /- Integrablility -/
    intro i hi
    have hf' :
      (fun x => ↑(a i) * ↑(physHermiteFun i (√(m * ω / ℏ) * x)) * (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))))
        =  a i  • (fun x => (physHermiteFun i (√(m * ω / ℏ) * x)) * (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ))))) := by
        funext x
        simp
        ring
    rw [hf']
    apply Integrable.smul
    exact mul_physHermiteFun_integrable hℏ hm hω f hf hb i

lemma mul_polynomial_integrable {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace)
    (P : Polynomial ℤ) :
    MeasureTheory.Integrable (fun x => ((fun x => P.aeval  x) (√(m * ω / ℏ)  * x)) *
      (f x * Real.exp (- m * ω * x^2 / (2 * ℏ)))) volume := by
  have h1 := polynomial_mem_physHermiteFun_span P
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h1
  obtain ⟨a, ha⟩ := h1
  have h2 : (fun x => ↑((fun x => P.aeval  x) (√(m * ω / ℏ)  * x)) * (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))))
    = (fun x => ∑ r ∈ a.support, a r * (physHermiteFun r (√(m * ω / ℏ) * x)) * (f x * Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))) := by
    funext x
    rw [← ha]
    rw [← Finset.sum_mul]
    congr
    rw [Finsupp.sum]
    simp
  rw [h2]
  apply MeasureTheory.integrable_finset_sum
  intro i hi
  simp only [mul_assoc]
  have hf' : (fun a_1 =>
    ↑(a i) * (↑(physHermiteFun i (√(m * ω / ℏ) * a_1)) * (f a_1 * ↑(Real.exp (-m * (ω * a_1 ^ 2) / (2 * ℏ))))))
    = fun x => (a i) • ((physHermiteFun i (√(m * ω / ℏ) * x)) *
      (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ))))) := by
    funext x
    simp
    ring_nf
    simp_all
  rw [hf']
  apply MeasureTheory.Integrable.smul
  exact mul_physHermiteFun_integrable hℏ hm hω f hf hb i


lemma orthogonal_power_of_mem_orthogonal {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪eigenVector hℏ hm hω n, ⟨AEEqFun.mk f hf, hb⟩⟫_ℂ = 0)
    (r : ℕ) :
    ∫ x : ℝ, (x ^ r * (f x * Real.exp (- m * ω * x^2 / (2 * ℏ)))) = 0 := by
  by_cases hr : r ≠ 0
  · have h1 := orthogonal_polynomial_of_mem_orthogonal hℏ hm hω f hf hb hOrth (Polynomial.X ^ r)
    simp at h1
    have h2 : (fun x => (↑√(m * ω / ℏ) * ↑x) ^ r * (f x * Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))))
      =  (fun x => (↑√(m * ω / ℏ)  : ℂ) ^ r * (↑x ^r * (f x * Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))))) := by
      funext x
      ring
    rw [h2] at h1
    rw [MeasureTheory.integral_mul_left] at h1
    simp at h1
    have h0 : r ≠ 0 := by
      exact hr
    have h0' : √(m * ω / (ℏ)) ≠ 0 := by
      simp
      refine Real.sqrt_ne_zero'.mpr ?_
      refine div_pos ?_ ?_
      · exact mul_pos hm hω
      · exact hℏ
    simp [h0, h0'] at h1
    rw [← h1]
    congr
    funext x
    simp
  · simp at hr
    subst hr
    simp
    rw [← orthogonal_physHermiteFun_of_mem_orthogonal hℏ hm hω f hf hb hOrth 0]
    congr
    funext x
    simp


lemma mul_power_integrable {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace) (r : ℕ) :
    MeasureTheory.Integrable (fun x => x ^ r *
      (f x * Real.exp (- m * ω * x^2 / (2 * ℏ)))) volume := by
  by_cases hr : r ≠ 0
  · have h1 := mul_polynomial_integrable hℏ hm hω f hf hb (Polynomial.X ^ r)
    simp at h1
    have h2 : (fun x => (↑√(m * ω / ℏ) * ↑x) ^ r * (f x * Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))))
      =   (↑√(m * ω / ℏ)  : ℂ) ^ r •  (fun x => (↑x ^r * (f x * Real.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))))) := by
      funext x
      simp
      ring
    rw [h2] at h1
    rw [IsUnit.integrable_smul_iff] at h1
    simpa using h1
    simp
    have h1 :  √(m * ω / ℏ) ≠ 0 := by
      refine Real.sqrt_ne_zero'.mpr ?_
      refine div_pos ?_ ?_
      · exact mul_pos hm hω
      · exact hℏ
    simp [h1]
  · simp at hr
    subst hr
    simpa using mul_physHermiteFun_integrable hℏ hm hω f hf hb  0

lemma orthogonal_exp_of_mem_orthogonal {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪eigenVector hℏ hm hω n, ⟨AEEqFun.mk f hf, hb⟩⟫_ℂ = 0) (c : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * c * x) * (f x * Real.exp (- m * ω * x^2 / (2 * ℏ))) = 0 := by
  /- Rewriting the intergrand as a limit. -/
  have h1 (y : ℝ) : Filter.Tendsto (fun n =>  ∑ r ∈ range n,
        (Complex.I * ↑c * ↑y) ^ r / r ! * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))
      Filter.atTop (nhds (Complex.exp (Complex.I * c * y) * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))) := by
    have h11 : (fun n =>  ∑ r ∈ range n,
        (Complex.I * ↑c * ↑y) ^ r / r !
        * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ)))) =
        fun n => (∑ r ∈ range n,
        (Complex.I * ↑c * ↑y) ^ r / r !)
        * ((f y * Real.exp (- m * ω * y^2 / (2 * ℏ)))) := by
      funext s
      simp [Finset.sum_mul]
    rw [h11]
    have h12 :  (Complex.exp (Complex.I * c * y) * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))
      = ( Complex.exp (Complex.I * c * y)) * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))):= by
      simp
    rw [h12]
    apply Filter.Tendsto.mul_const
    simp [Complex.exp, Complex.exp']
    haveI hi : CauSeq.IsComplete ℂ norm :=
      inferInstanceAs (CauSeq.IsComplete ℂ Complex.abs)
    exact CauSeq.tendsto_limit (Complex.exp' (Complex.I * c * y))
  /- End of rewritting the intergrand as a limit. -/
  /- Rewritting the integral as a limit using dominated_convergence -/
  have h1' : Filter.Tendsto (fun n => ∫ y : ℝ, ∑ r ∈ range n,
      (Complex.I * ↑c * ↑y) ^ r / r ! * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))
      Filter.atTop (nhds (∫ y : ℝ, Complex.exp (Complex.I * c * y) * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))) := by
    let bound : ℝ → ℝ := fun x => Real.exp (|c * x|) * Complex.abs (f x) *
      (Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))
    apply MeasureTheory.tendsto_integral_of_dominated_convergence bound
    · intro n
      apply Finset.aestronglyMeasurable_sum
      intro r hr
      have h1 : (fun a => (Complex.I * ↑c * ↑a) ^ r / ↑r ! * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ)))))
        =  fun a => (Complex.I * ↑c) ^ r / ↑r ! * (f a * Complex.ofReal (a ^ r * (Real.exp (-m * ω * a ^ 2 / (2 * ℏ))))) := by
        funext a
        simp
        ring
      rw [h1]
      apply MeasureTheory.AEStronglyMeasurable.const_mul
      apply MeasureTheory.AEStronglyMeasurable.mul
      · exact hf
      · apply MeasureTheory.Integrable.aestronglyMeasurable
        apply MeasureTheory.Integrable.ofReal
        change Integrable (fun x =>  (x ^ r) * (Real.exp (-m * ω * x ^ 2 / (2 * ℏ))))
        have h1 : (fun x => (x ^ r)*(Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))) =
            (fun x => (Polynomial.X ^ r : Polynomial ℤ).aeval x  *
            (Real.exp (- (m * ω / (2* ℏ)) * x ^ 2))) := by
          funext x
          simp  [neg_mul, mul_eq_mul_left_iff, Real.exp_eq_exp]
          left
          field_simp
        rw [h1]
        apply guassian_integrable_polynomial
        simp_all only [neg_mul, mul_pos_iff_of_pos_left, div_pos_iff_of_pos_left, ofNat_pos]
    · /- Prove the bound is integrable. -/
      have hbound : bound =
        (fun x => Real.exp |c * x| * Complex.abs (f x) * Real.exp (-(m * ω / (2 * ℏ)) * x ^ 2))
         := by
         simp [bound]
         funext x
         congr
         field_simp
      rw [hbound]
      apply HilbertSpace.exp_abs_mul_abs_mul_gaussian_integrable
      · exact hb
      · refine div_pos ?_ ?_
        · exact mul_pos hm hω
        · linarith
    · intro n
      apply Filter.Eventually.of_forall
      intro y
      rw [← Finset.sum_mul]
      simp [bound]
      rw [mul_assoc]
      conv_rhs =>
        rw [mul_assoc]
      have h1 : (Complex.abs (f y) * Complex.abs (Complex.exp (-(↑m * ↑ω * ↑y ^ 2) / (2 * ↑ℏ))))
        = Complex.abs (f y) * Real.exp (-(m * ω * y ^ 2) / (2 * ℏ)) := by
        simp
        left
        rw [Complex.abs_exp]
        congr
        trans (Complex.ofReal (-(m * ω * y ^ 2) / (2 * ℏ))).re
        · congr
          simp
        · rw [Complex.ofReal_re]
      rw [h1]
      by_cases hf : Complex.abs (f y) = 0
      · simp [hf]
      rw [_root_.mul_le_mul_right]
      · have h1 := Real.sum_le_exp_of_nonneg (x := |c * y|) (abs_nonneg (c * y)) n
        refine le_trans ?_ h1
        have h2 :  Complex.abs (∑ i ∈ range n, (Complex.I * (↑c * ↑y)) ^ i / ↑i !) ≤
          ∑ i ∈ range n, Complex.abs ((Complex.I * (↑c * ↑y)) ^ i / ↑i !) := by
          exact AbsoluteValue.sum_le _ _ _
        refine le_trans h2 ?_
        apply le_of_eq
        congr
        funext i
        simp
        congr
        rw [abs_mul]
      · refine mul_pos ?_ ?_
        have h1 : 0 ≤  Complex.abs (f y) := by exact AbsoluteValue.nonneg Complex.abs (f y)
        apply lt_of_le_of_ne h1 (fun a => hf (id (Eq.symm a)))
        exact Real.exp_pos (-(m * ω * y ^ 2) / (2 * ℏ))
    · apply Filter.Eventually.of_forall
      intro y
      exact h1 y
  have h3b  : (fun n => ∫ y : ℝ, ∑ r ∈ range n,
      (Complex.I * ↑c * ↑y) ^ r / r ! * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ)))) = fun (n : ℕ) => 0 := by
    funext n
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro r hr
      have hf' : (fun a => (Complex.I * ↑c * ↑a) ^ r / ↑r ! * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ)))))
        = fun a => ((Complex.I * ↑c) ^ r / ↑r !) * (a^ r * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ))))) := by
        funext a
        simp
        ring
      rw [hf']
      rw [MeasureTheory.integral_mul_left]
      rw [orthogonal_power_of_mem_orthogonal hℏ hm hω f hf hb hOrth r]
      simp
    · intro r hr
      have hf' : (fun a => (Complex.I * ↑c * ↑a) ^ r / ↑r ! * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ)))))
        = ((Complex.I * ↑c) ^ r / ↑r !)  • fun a => (a^ r * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ))))) := by
        funext a
        simp
        ring
      rw [hf']
      apply MeasureTheory.Integrable.smul
      exact mul_power_integrable hℏ hm hω f hf hb r
  rw [h3b] at h1'
  apply tendsto_nhds_unique h1'
  rw [tendsto_const_nhds_iff]


open FourierTransform MeasureTheory Real Lp Memℒp Filter Complex Topology ComplexInnerProductSpace ComplexConjugate


lemma fourierIntegral_zero_of_mem_orthogonal {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪eigenVector hℏ hm hω n, ⟨AEEqFun.mk f hf, hb⟩⟫_ℂ = 0) :
    𝓕 (fun x => f x * Real.exp (- m * ω * x^2 / (2 * ℏ))) = 0 := by
  funext c
  rw [Real.fourierIntegral_eq]
  simp
  rw [← orthogonal_exp_of_mem_orthogonal hℏ hm hω f hf hb hOrth (- 2 * Real.pi * c)]
  congr
  funext x
  simp [Real.fourierChar, Circle.exp]
  change Complex.exp (-(2 * ↑Real.pi * (↑x * ↑c) * Complex.I)) *
    (f x * Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))) = _
  congr 2
  ring

lemma zero_of_orthogonal_mk   {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hb : AEEqFun.mk f hf ∈ HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪eigenVector hℏ hm hω n, ⟨AEEqFun.mk f hf, hb⟩⟫_ℂ = 0)
    (plancherel_theorem: ∀ {f : ℝ → ℂ} (hf : Integrable f volume) (_ : Memℒp f 2),
       eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume):
    (⟨AEEqFun.mk f hf, hb⟩ : HilbertSpace) = 0 := by
  have hf' : (fun x => f x * ↑(rexp (-m * ω * x ^ 2 / (2 * ℏ))))
        = (fun x => f x * ↑(rexp (- (m * ω / (2 * ℏ)) * (x - 0) ^ 2 ))) := by
        funext x
        simp
        left
        congr
        field_simp
  have h1 : eLpNorm (fun x => f x * Real.exp (- m * ω * x^2 / (2 * ℏ))) 2 volume = 0 := by
    rw [← plancherel_theorem]
    rw [fourierIntegral_zero_of_mem_orthogonal hℏ hm hω f hf hb hOrth]
    simp
    · /-  f x * Real.exp (- m * ω * x^2 / (2 * ℏ)) is integrable -/
      rw [hf']
      rw [← memℒp_one_iff_integrable]
      apply HilbertSpace.mul_gaussian_mem_Lp_one f hf hb (m * ω / (2 * ℏ)) 0
      refine div_pos ?_ ?_
      · exact mul_pos hm hω
      · linarith
    ·  /-  f x * Real.exp (- m * ω * x^2 / (2 * ℏ)) is square-integrable -/
      rw [hf']
      refine HilbertSpace.mul_gaussian_mem_Lp_two f hf hb (m * ω / (2 * ℏ)) 0 ?_
      refine div_pos ?_ ?_
      · exact mul_pos hm hω
      · linarith
  refine (norm_eq_zero_iff (by simp)).mp ?_
  simp [Norm.norm]
  have h2 : eLpNorm f 2 volume = 0 := by
    rw [MeasureTheory.eLpNorm_eq_zero_iff]  at h1 ⊢
    rw [Filter.eventuallyEq_iff_all_subsets] at h1 ⊢
    have h3 (x : ℝ) :  f x * ↑(rexp (-m * ω * x ^ 2 / (2 * ℏ))) = 0  ↔
      f x = 0 := by simp
    simp [h3] at h1
    exact h1
    exact hf
    simp
    ·  /-  f x * Real.exp (- m * ω * x^2 / (2 * ℏ)) is strongly measurable -/
      rw [hf']
      apply Integrable.aestronglyMeasurable
      rw [← memℒp_one_iff_integrable]
      apply HilbertSpace.mul_gaussian_mem_Lp_one f hf hb (m * ω / (2 * ℏ)) 0
      refine div_pos ?_ ?_
      · exact mul_pos hm hω
      · linarith
    · simp
  rw [h2]
  simp

lemma zero_of_orthogonal_eigenVector   {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪eigenVector hℏ hm hω n, f⟫_ℂ = 0)
    (plancherel_theorem: ∀ {f : ℝ → ℂ} (hf : Integrable f volume) (_ : Memℒp f 2),
       eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume) : f = 0 := by
  have hf : f.1 = AEEqFun.mk (f : ℝ → ℂ) (Lp.aestronglyMeasurable f) := by
    exact Eq.symm (AEEqFun.mk_coeFn _)
  have hf2 : f = ⟨AEEqFun.mk (f : ℝ → ℂ) (Lp.aestronglyMeasurable f) , by
    rw [← hf]
    exact f.2⟩ := by
    simp
  rw [hf2]
  apply zero_of_orthogonal_mk
  · rw [← hf2]
    exact hOrth
  · exact plancherel_theorem

lemma completness_eigenvector  {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (plancherel_theorem : ∀ {f : ℝ → ℂ} (hf : Integrable f volume) (_ : Memℒp f 2),
       eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume)  :
    (Submodule.span ℂ (Set.range (eigenVector hℏ hm hω))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  refine (Submodule.eq_bot_iff (Submodule.span ℂ (Set.range (eigenVector hℏ hm hω)))ᗮ).mpr ?_
  intro f hf
  apply zero_of_orthogonal_eigenVector hℏ hm hω f ?_ plancherel_theorem
  intro n
  rw [@Submodule.mem_orthogonal'] at hf
  rw [← inner_conj_symm]
  have hl : ⟪f, eigenVector hℏ hm hω n⟫_ℂ = 0 := by
    apply hf
    refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ?_
    use Finsupp.single n 1
    simp
  rw [hl]
  simp

end HarmonicOscillator
end OneDimension
end QuantumMechanics
