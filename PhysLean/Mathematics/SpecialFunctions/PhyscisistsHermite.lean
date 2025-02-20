import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
/-!

# Physicists Hermite Polynomial

This file may eventually be upstreamed to Mathlib.

-/

open Polynomial
namespace PhysLean

/-- The Physicists Hermite  polynomial. -/
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
    physHermiteFun (n + 1) = fun x =>  2 • x *
    physHermiteFun n x -
    (2 * n : ℝ) • physHermiteFun (n - 1) x := by
  ext x
  simp [physHermite_succ', aeval, mul_assoc, physHermiteFun]

@[fun_prop]
lemma physHermiteFun_differentiableAt (n : ℕ) (x : ℝ)  :
    DifferentiableAt ℝ (physHermiteFun n) x := Polynomial.differentiableAt_aeval (physHermite n)

lemma deriv_physHermiteFun (n : ℕ) :
    deriv (physHermiteFun n) = 2 * n * (physHermiteFun (n - 1)) := by
  ext x
  rw [physHermiteFun_eq_aeval_physHermite]
  rw [Polynomial.deriv_aeval (physHermite n)]
  rw [derivative_physHermite]
  simp [aeval, mul_assoc, physHermiteFun_eq_aeval_physHermite]

lemma iterated_deriv_physHermiteFun (n : ℕ) : (m : ℕ) →
    deriv^[m] (physHermiteFun n) = fun x => (derivative^[m] (physHermite n)).aeval x
  | 0 => by
    simp [physHermiteFun_eq_aeval_physHermite]
  | m + 1 => by
    simp only [Function.iterate_succ_apply' , Function.comp_apply]
    rw [iterated_deriv_physHermiteFun n m]
    funext x
    rw [Polynomial.deriv_aeval]

lemma fderiv_physHermiteFun
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E)
    (f : E → ℝ) (hf : DifferentiableAt ℝ f x) (n : ℕ)  :
    fderiv ℝ (fun x => physHermiteFun n (f x)) x
    = (2 * n * physHermiteFun  (n - 1) (f x)) • fderiv ℝ f x := by
  have h := fderiv_comp (𝕜:=ℝ) (g:=physHermiteFun n) (f:=f) (hg:=by fun_prop) (hf:=by fun_prop)
  simp +unfoldPartialApp [Function.comp] at h
  ext dx
  simp [deriv_physHermiteFun,h]
  ring

@[simp]
lemma deriv_physHermiteFun' (x : ℝ)
    (f : ℝ → ℝ) (hf : DifferentiableAt ℝ f x) (n : ℕ)  :
    deriv (fun x => physHermiteFun n (f x)) x
    = (2 * n * physHermiteFun  (n - 1) (f x)) * deriv f x := by
  unfold deriv
  rw [fderiv_physHermiteFun (hf:=by fun_prop)]
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
      deriv (fun y => Real.exp (-(y ^ 2 ))) x = -2 * x * Real.exp (-(x ^ 2 )) := by
      rw [deriv_exp (by simp)]; simp; ring
    rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_mul, pow_succ (-1 : ℝ),
      deriv_gaussian, physHermiteFun_succ]
    · rw [deriv_physHermiteFun]
      simp
      ring
    · apply Polynomial.differentiable_aeval
    · apply DifferentiableAt.exp
      simp

lemma physHermiteFun_eq_deriv_gaussian  (n : ℕ) (x : ℝ) :
    physHermiteFun n x = (-1 : ℝ) ^ n * deriv^[n]
    (fun y => Real.exp (- y ^ 2)) x / Real.exp (- x ^ 2) := by
  rw [deriv_gaussian_eq_physHermiteFun_mul_gaussian]
  field_simp [Real.exp_ne_zero]
  rw [← @smul_eq_mul ℝ _ ((-1) ^ n), ← inv_smul_eq_iff₀, mul_assoc, smul_eq_mul, ← inv_pow, ←
    neg_inv, inv_one]
  exact pow_ne_zero _ (by norm_num)

lemma physHermiteFun_eq_deriv_gaussian'  (n : ℕ) (x : ℝ) :
    physHermiteFun n x = (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (- y ^ 2)) x *
    Real.exp (x ^ 2) := by
  rw [physHermiteFun_eq_deriv_gaussian, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

@[fun_prop]
lemma guassian_integrable_polynomial {b : ℝ} (hb : 0 < b) (P : Polynomial ℤ)  :
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
lemma physHermiteFun_gaussian_integrable (n p m : ℕ) :
    MeasureTheory.Integrable (deriv^[m] (physHermiteFun p) * deriv^[n] fun x => Real.exp (-x ^ 2))
    MeasureTheory.volume := by
  have h1 : (deriv^[m] (physHermiteFun p) * deriv^[n] fun x => Real.exp (-x ^ 2))
    = deriv^[m] (physHermiteFun p) *
    ((-1 : ℝ) ^ n • physHermiteFun n * (fun x => Real.exp (- x ^ 2)))
    := by
    funext x
    simp [deriv_gaussian_eq_physHermiteFun_mul_gaussian]
    ring_nf
    left
    trivial
  rw [h1]
  simp
  refine MeasureTheory.Integrable.smul ((-1) ^ n) ?_
  have h2 : deriv^[m] (physHermiteFun p) * physHermiteFun n =
      fun x => (derivative^[m] (physHermite p) * physHermite n).aeval x := by
    rw [iterated_deriv_physHermiteFun, physHermiteFun_eq_aeval_physHermite]
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


end PhysLean
