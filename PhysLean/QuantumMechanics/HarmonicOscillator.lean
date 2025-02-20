/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
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
- Show that eigenfunctions are orthogonal and normalized.
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
  simp
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


lemma eigenFunction_sq (m ℏ ω : ℝ) (n : ℕ)  (hℏ : 0 < ℏ) :
    (eigenfunction m ℏ ω n x) * (eigenfunction m ℏ ω n x)  =
    (( 1/ (2 ^ n * n !)) * (Real.sqrt (m * ω / (Real.pi * ℏ))))  *
     Complex.ofReal ((physHermiteFun n (Real.sqrt (m * ω /ℏ) * x))^2 * (Real.exp (- m * ω * x^2 /  ℏ))) := by
  calc eigenfunction m ℏ ω n x * eigenfunction m ℏ ω n x
    _ =  (1/Real.sqrt (2 ^ n * n !) * 1/Real.sqrt (2 ^ n * n !)) *
      (Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ))) * Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ))))  *
     (physHermiteFun n (Real.sqrt (m * ω /ℏ) * x))^2 * (Real.exp (- m * ω * x^2 / (2 * ℏ)) * Real.exp (- m * ω * x^2 / (2 * ℏ))) := by
      simp [eigenfunction]
      ring
    _ = ( 1/ (2 ^ n * n !)) *
      ( (Real.sqrt (m * ω / (Real.pi * ℏ))))  *
     (physHermiteFun n (Real.sqrt (m * ω /ℏ) * x))^2 * (Real.exp (- m * ω * x^2 /  ℏ)) := by
      congr 1
      · congr 1
        · congr 1
          · trans  1 / ↑(√(2 ^ n * ↑n !) * ↑√(2 ^ n * ↑n !))
            · field_simp
            congr
            trans Complex.ofReal ((2 ^ n * ↑n !))
            · congr 1
              refine Real.mul_self_sqrt ?_
              refine Left.mul_nonneg ?_ ?_
              refine pow_nonneg ?_ n
              simp
              exact cast_nonneg' n !
            simp
          · rw [← Complex.ofReal_mul]
            congr
            refine Real.mul_self_sqrt ?_
            exact Real.sqrt_nonneg (m * ω / (Real.pi * ℏ))
      · rw [← Complex.ofReal_mul]
        congr
        rw [← Real.exp_add]
        simp
        field_simp
        ring
  simp
  ring

end HarmonicOscillator

end QuantumMechanics
