/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
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

namespace HarmonicOscillator

open Nat
open PhysLean
/-- The Schrodinger Operator for the Harmonic oscillator. -/
noncomputable def schrodingerOperator (m ℏ ω : ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ := fun y =>
  - ℏ ^ 2 / (2 * m) * (deriv (fun y => deriv ψ y) y) + 1/2 *
  m * ω^2 * y^2 * ψ y

/-- The eigenfunctions for the Harmonic oscillator. -/
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
lemma eigenFunction_aeStronglyMeasurable (m ℏ ω : ℝ) (n : ℕ) (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) : MeasureTheory.AEStronglyMeasurable (eigenfunction m ℏ ω n) := by
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

end HarmonicOscillator

end QuantumMechanics
