import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
lemma physHermiteFun_differentiableAt : (n : ℕ) → (x : ℝ) →
    DifferentiableAt ℝ (physHermiteFun n) x
  | 0, x => by
    simp [physHermite, physHermiteFun_eq_aeval_physHermite]
  | 1, x => by
    simp [physHermite, physHermiteFun_eq_aeval_physHermite, aeval]
    fun_prop
  | n + 2, x => by
    rw [physHermiteFun_succ]
    have ih := physHermiteFun_differentiableAt n x
    have ih' := physHermiteFun_differentiableAt (n + 1) x
    fun_prop

lemma deriv_physHermiteFun (n : ℕ) :
    deriv (physHermiteFun n) = 2 * n * (physHermiteFun (n - 1)) := by
  ext x
  rw [physHermiteFun_eq_aeval_physHermite]
  rw [Polynomial.deriv_aeval (physHermite n)]
  rw [derivative_physHermite]
  simp [aeval, mul_assoc, physHermiteFun_eq_aeval_physHermite]


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

end PhysLean
