/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
/-!

# Physicists Hermite Polynomial

This file may eventually be upstreamed to Mathlib.

-/

open Polynomial
namespace PhysLean

/-- The Physicists Hermite polynomial. -/
noncomputable def physHermite : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => 2 • X * physHermite n - derivative (physHermite n)

lemma physHermite_succ (n : ℕ) :
    physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n) := by
  simp [physHermite]

lemma physHermite_eq_iterate (n : ℕ) :
    physHermite n = (fun p => 2 * X * p - derivative p)^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ← ih, physHermite_succ]

@[simp]
lemma physHermite_zero : physHermite 0 = C 1 := rfl

lemma physHermite_one : physHermite 1 = 2 * X := by
  rw [physHermite_succ, physHermite_zero]
  simp

lemma derivative_physHermite_succ : (n : ℕ) →
    derivative (physHermite (n + 1)) = 2 * (n + 1) • physHermite n
  | 0 => by
    simp [physHermite_one]
  | n + 1 => by
    rw [physHermite_succ]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, derivative_sub, derivative_mul, derivative_ofNat,
      zero_mul, derivative_X, mul_one, zero_add, Nat.cast_add, Nat.cast_one]
    rw [derivative_physHermite_succ]
    simp only [physHermite_succ, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one,
      derivative_mul, derivative_ofNat, zero_mul, derivative_add, derivative_natCast,
      derivative_one, add_zero, zero_add]
    ring

lemma derivative_physHermite : (n : ℕ) →
    derivative (physHermite n) = 2 * n • physHermite (n - 1)
  | 0 => by
    simp
  | n + 1 => by
    rw [derivative_physHermite_succ]
    simp

lemma physHermite_succ' (n : ℕ) :
    physHermite (n + 1) = 2 • X * physHermite n - 2 * n • physHermite (n - 1) := by
  rw [physHermite_succ, derivative_physHermite]

lemma coeff_physHhermite_succ_zero (n : ℕ) :
    coeff (physHermite (n + 1)) 0 = - coeff (physHermite n) 1 := by
  simp [physHermite_succ, coeff_derivative]

lemma coeff_physHermite_succ_succ (n k : ℕ) : coeff (physHermite (n + 1)) (k + 1) =
    2 * coeff (physHermite n) k - (k + 2) * coeff (physHermite n) (k + 2) := by
  rw [physHermite_succ, coeff_sub, smul_mul_assoc, coeff_smul, coeff_X_mul, coeff_derivative,
    mul_comm]
  norm_cast

lemma coeff_physHermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (physHermite n) k = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hnk
  clear hnk
  induction n generalizing k with
  | zero => exact coeff_C
  | succ n ih =>
    have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring
    rw [coeff_physHermite_succ_succ, add_right_comm, this, ih k, ih (k + 2), mul_zero]
    simp

@[simp]
lemma coeff_physHermite_self_succ (n : ℕ) : coeff (physHermite n) n = 2 ^ n := by
  induction n with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_physHermite_succ_succ, ih, coeff_physHermite_of_lt, mul_zero, sub_zero]
    rw [← Int.pow_succ']
    omega

@[simp]
lemma degree_physHermite (n : ℕ) : degree (physHermite n) = n := by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  · simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
    rintro m hnm
    exact coeff_physHermite_of_lt hnm
  · simp

@[simp]
lemma natDegree_physHermite {n : ℕ} : (physHermite n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_physHermite n)

lemma iterate_derivative_physHermite_of_gt {n m : ℕ} (h : n < m) :
    derivative^[m] (physHermite n) = 0 := by
  refine iterate_derivative_eq_zero ?_
  simpa using h

open Nat

@[simp]
lemma iterate_derivative_physHermite_self {n : ℕ} :
    derivative^[n] (physHermite n) = C ((n ! : ℤ) * 2 ^ n) := by
  refine coeff_inj.mp ?_
  funext m
  rw [Polynomial.coeff_iterate_derivative]
  match m with
  | 0 =>
    rw [Polynomial.coeff_C_zero]
    simp only [zero_add, coeff_physHermite_self_succ, nsmul_eq_mul, mul_eq_mul_right_iff,
      Nat.cast_inj, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]
    rw [Nat.descFactorial_self]
  | m + 1 =>
    rw [coeff_physHermite_of_lt (by omega)]
    rw [Polynomial.coeff_C_ne_zero (by omega)]
    rfl

/-- The physicists Hermite polynomial as a function from `ℝ` to `ℝ`. -/
noncomputable def physHermiteFun (n : ℕ) : ℝ → ℝ := fun x => aeval x (physHermite n)

@[simp]
lemma physHermiteFun_zero_apply (x : ℝ) : physHermiteFun 0 x = 1 := by
  simp [physHermiteFun, aeval]

lemma physHermiteFun_eq_aeval_physHermite (n : ℕ) :
    physHermiteFun n = fun x => aeval x (physHermite n) := rfl

lemma physHermiteFun_succ_fun (n : ℕ) :
    physHermiteFun (n + 1) = 2 • (fun x => x) *
    physHermiteFun n - (2 * n : ℝ) • physHermiteFun (n - 1) := by
  ext x
  simp [physHermite_succ', aeval, physHermiteFun, mul_assoc]

lemma physHermiteFun_succ (n : ℕ) :
    physHermiteFun (n + 1) = fun x => 2 • x *
    physHermiteFun n x -
    (2 * n : ℝ) • physHermiteFun (n - 1) x := by
  ext x
  simp [physHermite_succ', aeval, mul_assoc, physHermiteFun]

lemma iterated_deriv_physHermiteFun_eq_aeval (n : ℕ) : (m : ℕ) →
    deriv^[m] (physHermiteFun n) = fun x => (derivative^[m] (physHermite n)).aeval x
  | 0 => by
    simp [physHermiteFun_eq_aeval_physHermite]
  | m + 1 => by
    simp only [Function.iterate_succ_apply', Function.comp_apply]
    rw [iterated_deriv_physHermiteFun_eq_aeval n m]
    funext x
    rw [Polynomial.deriv_aeval]

@[fun_prop]
lemma physHermiteFun_differentiableAt (n : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (physHermiteFun n) x := Polynomial.differentiableAt_aeval (physHermite n)

@[fun_prop]
lemma deriv_physHermiteFun_differentiableAt (n m : ℕ) (x : ℝ) :
    DifferentiableAt ℝ (deriv^[m] (physHermiteFun n)) x := by
  rw [iterated_deriv_physHermiteFun_eq_aeval]
  exact Polynomial.differentiableAt_aeval _

lemma deriv_physHermiteFun (n : ℕ) :
    deriv (physHermiteFun n) = 2 * n * (physHermiteFun (n - 1)) := by
  ext x
  rw [physHermiteFun_eq_aeval_physHermite]
  rw [Polynomial.deriv_aeval (physHermite n)]
  rw [derivative_physHermite]
  simp [aeval, mul_assoc, physHermiteFun_eq_aeval_physHermite]

lemma fderiv_physHermiteFun
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E)
    (f : E → ℝ) (hf : DifferentiableAt ℝ f x) (n : ℕ) :
    fderiv ℝ (fun x => physHermiteFun n (f x)) x
    = (2 * n * physHermiteFun (n - 1) (f x)) • fderiv ℝ f x := by
  have h := fderiv_comp (𝕜 := ℝ) (g := physHermiteFun n) (f := f) (hg := by fun_prop)
    (hf := by fun_prop)
  simp +unfoldPartialApp [Function.comp] at h
  ext dx
  simp [deriv_physHermiteFun,h]
  ring

@[simp]
lemma deriv_physHermiteFun' (x : ℝ)
    (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f x) (n : ℕ) :
    deriv (fun x => physHermiteFun n (f x)) x
    = (2 * n * physHermiteFun (n - 1) (f x)) * deriv f x := by
  unfold deriv
  rw [fderiv_physHermiteFun (hf := by fun_prop)]
  rfl

/-!

## Relationship to Gaussians

-/

lemma deriv_gaussian_eq_physHermiteFun_mul_gaussian (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y => Real.exp (- y ^ 2)) x =
    (-1 : ℝ) ^ n * physHermiteFun n x * Real.exp (- x ^ 2) := by
  rw [mul_assoc]
  induction' n with n ih generalizing x
  · rw [Function.iterate_zero_apply, pow_zero, one_mul, physHermiteFun_zero_apply, one_mul]
  · replace ih : deriv^[n] _ = _ := _root_.funext ih
    have deriv_gaussian :
      deriv (fun y => Real.exp (-(y ^ 2))) x = -2 * x * Real.exp (-(x ^ 2)) := by
      rw [deriv_exp (by simp)]; simp; ring
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_mul, pow_succ (-1 : ℝ),
      deriv_gaussian, physHermiteFun_succ]
    · rw [deriv_physHermiteFun]
      simp only [Pi.natCast_def, Pi.mul_apply, Pi.ofNat_apply, cast_ofNat, neg_mul, mul_neg,
        mul_one, nsmul_eq_mul, smul_eq_mul]
      ring
    · apply Polynomial.differentiable_aeval
    · apply DifferentiableAt.exp
      simp

lemma physHermiteFun_eq_deriv_gaussian (n : ℕ) (x : ℝ) :
    physHermiteFun n x = (-1 : ℝ) ^ n * deriv^[n]
    (fun y => Real.exp (- y ^ 2)) x / Real.exp (- x ^ 2) := by
  rw [deriv_gaussian_eq_physHermiteFun_mul_gaussian]
  field_simp [Real.exp_ne_zero]
  rw [← @smul_eq_mul ℝ _ ((-1) ^ n), ← inv_smul_eq_iff₀, mul_assoc, smul_eq_mul, ← inv_pow, ←
    neg_inv, inv_one]
  exact pow_ne_zero _ (by norm_num)

lemma physHermiteFun_eq_deriv_gaussian' (n : ℕ) (x : ℝ) :
    physHermiteFun n x = (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (- y ^ 2)) x *
    Real.exp (x ^ 2) := by
  rw [physHermiteFun_eq_deriv_gaussian, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

@[fun_prop]
lemma guassian_integrable_polynomial {b : ℝ} (hb : 0 < b) (P : Polynomial ℤ) :
    MeasureTheory.Integrable fun x : ℝ => (P.aeval x) * Real.exp (-b * x ^ 2) := by
  conv =>
    enter [1, x]
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  apply MeasureTheory.integrable_finset_sum
  intro i hi
  have h2 : (fun a => P.coeff i • a ^ i * Real.exp (-b * a ^ 2)) =
      (P.coeff i : ℝ) • (fun x => (x ^ (i : ℝ) * Real.exp (-b * x ^ 2))) := by
    funext x
    simp [mul_assoc]
  rw [h2]
  refine MeasureTheory.Integrable.smul (P.coeff i : ℝ) ?_
  apply integrable_rpow_mul_exp_neg_mul_sq (s := i)
  exact hb
  exact gt_of_ge_of_gt (Nat.cast_nonneg' i) neg_one_lt_zero

@[fun_prop]
lemma guassian_integrable_polynomial_cons {b c : ℝ} (hb : 0 < b) (P : Polynomial ℤ) :
    MeasureTheory.Integrable fun x : ℝ => (P.aeval (c * x)) * Real.exp (-b * x ^ 2) := by
  conv =>
    enter [1, x]
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul]
  apply MeasureTheory.integrable_finset_sum
  intro i hi
  have h2 : (fun a => P.coeff i • (c * a) ^ i * Real.exp (-b * a ^ 2)) =
      (c ^ i * P.coeff i : ℝ) • (fun x => (x ^ (i : ℝ) * Real.exp (-b * x ^ 2))) := by
    funext x
    simp [mul_assoc]
    ring
  rw [h2]
  refine MeasureTheory.Integrable.smul (c ^ i * P.coeff i : ℝ) ?_
  apply integrable_rpow_mul_exp_neg_mul_sq (s := i)
  exact hb
  exact gt_of_ge_of_gt (Nat.cast_nonneg' i) neg_one_lt_zero

@[fun_prop]
lemma physHermiteFun_gaussian_integrable (n p m : ℕ) :
    MeasureTheory.Integrable (deriv^[m] (physHermiteFun p) * deriv^[n] fun x => Real.exp (-x ^ 2))
    MeasureTheory.volume := by
  have h1 : (deriv^[m] (physHermiteFun p) * deriv^[n] fun x => Real.exp (-x ^ 2))
    = deriv^[m] (physHermiteFun p) *
    ((-1 : ℝ) ^ n • physHermiteFun n * (fun x => Real.exp (- x ^ 2))) := by
    funext x
    simp only [Pi.mul_apply, deriv_gaussian_eq_physHermiteFun_mul_gaussian, Algebra.smul_mul_assoc,
      Pi.smul_apply, smul_eq_mul, mul_eq_mul_left_iff]
    ring_nf
    left
    trivial
  rw [h1]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm]
  refine MeasureTheory.Integrable.smul ((-1) ^ n) ?_
  have h2 : deriv^[m] (physHermiteFun p) * physHermiteFun n =
      fun x => (derivative^[m] (physHermite p) * physHermite n).aeval x := by
    rw [iterated_deriv_physHermiteFun_eq_aeval, physHermiteFun_eq_aeval_physHermite]
    funext x
    simp
  conv =>
    enter [1, x]
    rw [← mul_assoc, h2]
  have h0 : ((fun x => (aeval x)
      ((⇑derivative)^[m] (physHermite p) * physHermite n)) * fun x => Real.exp (-x ^ 2))
      = fun x => ((⇑derivative)^[m] (physHermite p) * physHermite n).aeval x *
      Real.exp (- (1 : ℝ) * x ^ 2) := by
    funext x
    simp
  rw [h0]
  apply guassian_integrable_polynomial
  exact Real.zero_lt_one

lemma integral_physHermiteFun_mul_physHermiteFun_eq_integral_deriv_exp (n m : ℕ) :
    ∫ x : ℝ, (physHermiteFun n x * physHermiteFun m x) * Real.exp (-x ^ 2) =
    (-1 : ℝ) ^ m * ∫ x : ℝ, (physHermiteFun n x * (deriv^[m] fun x => Real.exp (-x ^ 2)) x) := by
  have h1 (x : ℝ) : (physHermiteFun n x * physHermiteFun m x) * Real.exp (-x ^ 2)
    = (-1 : ℝ) ^ m * (physHermiteFun n x * (deriv^[m] fun x => Real.exp (-x ^ 2)) x) := by
    conv_lhs =>
      enter [1, 2]
      rw [physHermiteFun_eq_deriv_gaussian']
    rw [mul_assoc, mul_assoc, ← Real.exp_add]
    simp only [add_neg_cancel, Real.exp_zero, mul_one]
    ring
  simp [h1]
  exact MeasureTheory.integral_mul_left ((-1) ^ m) fun a =>
      physHermiteFun n a * deriv^[m] (fun x => Real.exp (-x ^ 2)) a

lemma integral_physHermiteFun_mul_physHermiteFun_eq_integral_deriv_inductive (n m : ℕ) :
    (p : ℕ) → (hpm : p ≤ m) →
    ∫ x : ℝ, (physHermiteFun n x * physHermiteFun m x) * Real.exp (- x ^ 2) =
    (-1 : ℝ) ^ (m - p) * ∫ x : ℝ, (deriv^[p] (physHermiteFun n) x *
    (deriv^[m - p] fun x => Real.exp (-x ^ 2)) x)
  | 0, h => by
    exact integral_physHermiteFun_mul_physHermiteFun_eq_integral_deriv_exp n m
  | p + 1, h => by
    rw [integral_physHermiteFun_mul_physHermiteFun_eq_integral_deriv_inductive n m p]
    have h1 : m - p = m - (p + 1) + 1 := by omega
    rw [h1]
    rw [Function.iterate_succ_apply']
    conv_rhs =>
      rw [Function.iterate_succ_apply']
    have h1 : (-1 : ℝ) ^ (m - (p + 1) + 1) = (-1) ^ (m - (p + 1)) * (-1) := by
      rw [pow_add]
      simp
    rw [h1, mul_assoc]
    congr
    have hl : ∫ (x : ℝ), deriv^[p] (physHermiteFun n) x *
        deriv (deriv^[m - (p + 1)] fun x => Real.exp (-x ^ 2)) x =
        - ∫ (x : ℝ), deriv (deriv^[p] (physHermiteFun n)) x *
        deriv^[m - (p + 1)] (fun x => Real.exp (-x ^ 2)) x := by
      apply MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      · intro x
        refine DifferentiableAt.hasDerivAt ?_
        fun_prop
      · intro x
        simp only [hasDerivAt_deriv_iff]
        have h1 : (deriv^[m - (p + 1)] fun x => Real.exp (-x ^ 2)) =
            fun x => (-1 : ℝ) ^ (m - (p + 1)) * physHermiteFun (m - (p + 1)) x *
            Real.exp (- x ^ 2) := by
          funext x
          exact deriv_gaussian_eq_physHermiteFun_mul_gaussian (m - (p + 1)) x
        rw [h1]
        fun_prop
      · rw [← Function.iterate_succ_apply' deriv]
        exact physHermiteFun_gaussian_integrable _ _ _
      · rw [← Function.iterate_succ_apply' deriv]
        exact physHermiteFun_gaussian_integrable _ _ _
      · fun_prop
    rw [hl]
    simp only [mul_neg, neg_mul, one_mul, neg_neg]
    omega

lemma integral_physHermiteFun_mul_physHermiteFun_eq_integral_deriv (n m : ℕ) :
    ∫ x : ℝ, (physHermiteFun n x * physHermiteFun m x) * Real.exp (- x ^ 2) =
    ∫ x : ℝ, (deriv^[m] (physHermiteFun n) x * (Real.exp (-x ^ 2))) := by
  rw [integral_physHermiteFun_mul_physHermiteFun_eq_integral_deriv_inductive n m m (by rfl)]
  simp

lemma physHermiteFun_orthogonal_lt {n m : ℕ} (hnm : n < m) :
    ∫ x : ℝ, (physHermiteFun n x * physHermiteFun m x) * Real.exp (- x ^ 2) = 0 := by
  rw [integral_physHermiteFun_mul_physHermiteFun_eq_integral_deriv]
  rw [iterated_deriv_physHermiteFun_eq_aeval, iterate_derivative_physHermite_of_gt hnm]
  simp

theorem physHermiteFun_orthogonal {n m : ℕ} (hnm : n ≠ m) :
    ∫ x : ℝ, (physHermiteFun n x * physHermiteFun m x) * Real.exp (- x ^ 2) = 0 := by
  by_cases hnm' : n < m
  · exact physHermiteFun_orthogonal_lt hnm'
  · have hmn : m < n := by omega
    conv_lhs =>
      enter [2, x, 1]
      rw [mul_comm]
    rw [physHermiteFun_orthogonal_lt hmn]

lemma physHermiteFun_orthogonal_cons {n m : ℕ} (hnm : n ≠ m) (c : ℝ) :
    ∫ x : ℝ, (physHermiteFun n (c * x) * physHermiteFun m (c * x)) *
    Real.exp (- c ^ 2 * x ^ 2) = 0 := by
  trans ∫ x : ℝ, (fun x => (physHermiteFun n x * physHermiteFun m x) * Real.exp (- x^2)) (c * x)
  · congr
    funext x
    simp only [neg_mul, mul_eq_mul_left_iff, Real.exp_eq_exp, neg_inj, _root_.mul_eq_zero]
    left
    exact Eq.symm (mul_pow c x 2)
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun x => physHermiteFun n x * physHermiteFun m x * Real.exp (-x ^ 2)) c]
  rw [physHermiteFun_orthogonal hnm]
  simp

theorem physHermiteFun_norm (n : ℕ) :
    ∫ x : ℝ, (physHermiteFun n x * physHermiteFun n x) * Real.exp (- x ^ 2) =
    ↑n ! * 2 ^ n * √Real.pi := by
  rw [integral_physHermiteFun_mul_physHermiteFun_eq_integral_deriv]
  rw [iterated_deriv_physHermiteFun_eq_aeval]
  simp only [iterate_derivative_physHermite_self,
    Int.cast_pow, Int.cast_ofNat, map_pow]
  conv_lhs =>
    enter [2, x]
    rw [aeval_C]
    simp
  rw [MeasureTheory.integral_mul_left]
  have h1 : ∫ (x : ℝ), Real.exp (- x^2) = Real.sqrt (Real.pi) := by
    trans ∫ (x : ℝ), Real.exp (- 1 * x^2)
    · simp
    rw [integral_gaussian]
    simp
  rw [h1]

lemma physHermiteFun_norm_cons (n : ℕ) (c : ℝ) :
    ∫ x : ℝ, (physHermiteFun n (c * x) * physHermiteFun n (c * x)) * Real.exp (- c ^ 2 * x ^ 2) =
    |c⁻¹| • (↑n ! * 2 ^ n * √Real.pi) := by
  trans ∫ x : ℝ, (fun x => (physHermiteFun n x * physHermiteFun n x) * Real.exp (- x^2)) (c * x)
  · congr
    funext x
    simp only [neg_mul, mul_eq_mul_left_iff, Real.exp_eq_exp, neg_inj, _root_.mul_eq_zero, or_self]
    left
    exact Eq.symm (mul_pow c x 2)
  rw [MeasureTheory.Measure.integral_comp_mul_left
    (fun x => physHermiteFun n x * physHermiteFun n x * Real.exp (-x ^ 2)) c]
  rw [physHermiteFun_norm]

end PhysLean
