/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

## Some preliminary results about Hermite polynomials.

To be moved.

-/

/-- The Hermite polynomials defined via their recursive relation. -/
def hermitePolynomial : (n : ℕ) → (x : ℝ) → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | (n + 2), x => 2 * x * hermitePolynomial (n + 1) x - 2 * (n + 1) * hermitePolynomial n x

@[fun_prop]
lemma hermitePolynomial_differentiableAt : (n : ℕ) → (x : ℝ) →
    DifferentiableAt ℝ (hermitePolynomial n) x
  | 0, x => by
    simp [hermitePolynomial]
  | 1, x => by
    simp [hermitePolynomial]
    fun_prop
  | n + 2, x => by
    simp [hermitePolynomial]
    have ih := hermitePolynomial_differentiableAt (n + 1) x
    have ih' := hermitePolynomial_differentiableAt n x
    fun_prop

lemma hermitePolynomial_add_succ_succ (n : ℕ) :
    hermitePolynomial (n + 2) = 2 • (fun x => x) * hermitePolynomial (n + 1) -
    (2 * (n + 1) : ℝ) • hermitePolynomial n := by
  simp [hermitePolynomial]
  rfl

lemma deriv_hermitePolynomial : (n : ℕ) →
    deriv (hermitePolynomial (n + 1)) = 2 * (n + 1) * hermitePolynomial n
  | 0 => by
    simp [hermitePolynomial]
    trans (deriv fun x => (fun x => 2) x * id x)
    rfl
    funext x
    have h1 := deriv_mul (c := fun x => (2 : ℝ)) (d := id) (x := x)
      (differentiableAt_const 2) (differentiableAt_id)
    rw [h1]
    simp
  | 1 => by
    simp [hermitePolynomial]
    ring_nf
    let f3 := fun (x : ℝ) => (-2 : ℝ)
    let f1 := fun (x : ℝ) => x
    let f2 := fun (x : ℝ) => (4 : ℝ)
    trans deriv (fun x => (f3 x + (f1 x * f1 x) * f2 x))
    · apply congrArg
      funext x
      simp [f1, f2]
      ring
    funext x
    rw [deriv_add (by fun_prop) (by fun_prop)]
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    simp [f1, f2, f3]
    ring
  | n + 2 => by
    change deriv (hermitePolynomial ((n + 1) + 2)) = _
    conv_lhs =>
      rw [hermitePolynomial_add_succ_succ]
    let f1 := fun (x : ℝ) => (2 • fun x => x) x * hermitePolynomial (n + 1 + 1) x
    let f2 := fun x => (2 * ↑(n +1 + 1)) • hermitePolynomial (n + 1) x
    funext x
    trans deriv (fun x => f1 x - f2 x) x
    · simp [f1, f2]
      rfl
    rw [deriv_sub (by simp [f1]; fun_prop) (by simp [f2]; fun_prop)]
    simp only [f1, f2]
    rw [deriv_mul _ (by fun_prop)]
    simp
    have h1 : deriv (2 * fun x => x) x = 2 := by
      erw [deriv_const_mul_field']
      simp
      rfl
    rw [h1]
    have ih := deriv_hermitePolynomial n
    have ih' := deriv_hermitePolynomial (n + 1)
    rw [ih, ih']
    simp [hermitePolynomial]
    ring_nf
    simp
    change DifferentiableAt ℝ (fun x => 2 * x) x
    fun_prop

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

/-- The Schrodinger Operator for the Harmonic oscillator. -/
noncomputable def schrodingerOperator (m ℏ ω : ℝ) (ψ : ℝ → ℂ) : ℝ → ℂ := fun y =>
  - ℏ ^ 2 / (2 * m) * (deriv (fun y => deriv ψ y) y) + 1/2 *
  m * ω^2 * y^2 * ψ y

/-- The eigenfunctions for the Harmonic oscillator. -/
noncomputable def eigenfunction (m ℏ ω : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  1/Real.sqrt (2 ^ n * n !) * Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ))) *
  hermitePolynomial n (Real.sqrt (m * ω /ℏ) * x) * Real.exp (- m * ω * x^2 / (2 * ℏ))

/-- The eigenvalues for the Harmonic oscillator. -/
noncomputable def eigenValue (ℏ ω : ℝ) (n : ℕ) : ℝ := (n + 1/2) * ℏ * ω

lemma eigenfunction_zero (m ℏ ω : ℝ) : eigenfunction m ℏ ω 0 = fun (x : ℝ) =>
    (Real.sqrt (Real.sqrt (m * ω / (Real.pi * ℏ))) * Complex.exp (- m * ω * x^2 / (2 * ℏ))) := by
  funext x
  simp [eigenfunction, hermitePolynomial]

lemma deriv_eigenfunction_zero (m ℏ ω : ℝ) : deriv (eigenfunction m ℏ ω 0) =
    Complex.ofReal (- m * ω / ℏ) • Complex.ofReal * eigenfunction m ℏ ω 0 := by
  rw [eigenfunction_zero m ℏ ω]
  simp
  ext x
  have h1 : deriv (fun x => Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))) x =
      - m * ω * x /ℏ* Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ)) := by
    trans deriv (Complex.exp ∘ (fun x => -(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))) x
    · rfl
    rw [deriv_comp]
    simp
    have h1' : deriv (fun x => (Complex.ofReal x) ^ 2) x = 2 * x := by
      trans deriv (fun x => Complex.ofReal x * Complex.ofReal x) x
      · apply congr
        apply congrArg
        funext x
        ring
        rfl
      rw [deriv_mul]
      simp
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
  simp
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
  simp
  rw [deriv_eigenfunction_zero]
  simp
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
    * Complex.ofReal (hermitePolynomial (n + 1) (Real.sqrt (m * ω / ℏ) * x))
    * eigenfunction m ℏ ω 0 x := by
  funext x
  rw [eigenfunction, eigenfunction_zero]
  repeat rw [mul_assoc]
  congr 1
  simp
  rw [mul_comm, mul_assoc]
  congr 1
  simp
  ring_nf

lemma deriv_hermitePolynomial_succ (m ℏ ω : ℝ) (n : ℕ) :
    deriv (fun x => Complex.ofReal (hermitePolynomial (n + 1) (Real.sqrt (m * ω / ℏ) * x))) =
    fun x =>
    Complex.ofReal (Real.sqrt (m * ω / ℏ)) * 2 * (n + 1) *
    hermitePolynomial n (Real.sqrt (m * ω / ℏ) * x) := by
  funext x
  trans deriv (Complex.ofReal ∘ hermitePolynomial (n + 1) ∘
    fun (x : ℝ) => (Real.sqrt (m * ω / ℏ) * x)) x
  · rfl
  rw [fderiv_comp_deriv]
  rw [fderiv_comp_deriv]
  simp
  rw [deriv_mul]
  simp
  rw [deriv_hermitePolynomial]
  simp
  ring
  all_goals fun_prop

lemma deriv_eigenFunction_succ (m ℏ ω : ℝ) (n : ℕ) :
    deriv (eigenfunction m ℏ ω (n + 1)) = fun x =>
    Complex.ofReal (1/Real.sqrt (2 ^ (n + 1) * (n + 1) !)) •
    (((Real.sqrt (m * ω / ℏ)) * 2 * (↑n + 1) *
      ↑(hermitePolynomial n (Real.sqrt (m * ω / ℏ) * x))
      + ↑(hermitePolynomial (n + 1) (Real.sqrt (m * ω / ℏ) * x)) *
      (-(↑m * ↑ω) / ↑ℏ * ↑x)) * eigenfunction m ℏ ω 0 x) := by
  funext x
  rw [eigenFunction_succ_eq_mul_eigenfunction_zero]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp
  rw [deriv_hermitePolynomial_succ, deriv_eigenfunction_zero]
  simp
  ring

lemma deriv_deriv_eigenFunction_succ (m ℏ ω : ℝ) (n : ℕ) (x : ℝ) :
    deriv (fun x => deriv (eigenfunction m ℏ ω (n + 1)) x) x =
    Complex.ofReal (1/Real.sqrt (2 ^ (n + 1) * (n + 1) !)) *
      ((↑√(m * ω / ℏ) * 2 * (↑n + 1) *
      deriv (fun x => ↑(hermitePolynomial n (√(m * ω / ℏ) * x))) x +
      (-(↑m * ↑ω) / ↑ℏ) * ↑√(m * ω / ℏ) * (4 * (↑n + 1) * x) *
      (hermitePolynomial n (√(m * ω / ℏ) * x)) +
      (-(↑m * ↑ω) / ↑ℏ) * (1 + (-(↑m * ↑ω) / ↑ℏ) * x ^ 2) *
      (hermitePolynomial (n + 1) (√(m * ω / ℏ) * x))) * eigenfunction m ℏ ω 0 x) := by
  rw [deriv_eigenFunction_succ]
  simp
  left
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  rw [deriv_eigenfunction_zero]
  simp [← mul_assoc, ← add_mul]
  left
  rw [deriv_add (by fun_prop) (by fun_prop)]
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp
  rw [deriv_mul (by fun_prop) (by fun_prop)]
  simp
  rw [deriv_hermitePolynomial_succ]
  simp
  ring

lemma deriv_deriv_eigenFunction_one (m ℏ ω : ℝ) (x : ℝ) :
    deriv (fun x => deriv (eigenfunction m ℏ ω 1) x) x =
      Complex.ofReal (1/Real.sqrt (2 ^ 1 * 1 !)) *
      ((((-(↑m * ↑ω) / ↑ℏ) * ↑√(m * ω / ℏ) * (4 * x) +
        (-(↑m * ↑ω) / ↑ℏ) * (1 + (-(↑m * ↑ω) / ↑ℏ) * x ^ 2) * (2* (√(m * ω / ℏ) * x)))) *
        eigenfunction m ℏ ω 0 x) := by
  rw [deriv_deriv_eigenFunction_succ]
  congr 2
  simp [hermitePolynomial]

lemma schrodingerOperator_eigenfunction_one (m ℏ ω : ℝ) (x : ℝ) (hm : m ≠ 0) (hℏ : ℏ ≠ 0) :
    schrodingerOperator m ℏ ω (eigenfunction m ℏ ω 1) x=
    eigenValue ℏ ω 1 * eigenfunction m ℏ ω 1 x := by
  simp [schrodingerOperator, eigenValue]
  rw [deriv_deriv_eigenFunction_one]
  have hm' := Complex.ofReal_ne_zero.mpr hm
  have hℏ' := Complex.ofReal_ne_zero.mpr hℏ
  rw [eigenFunction_succ_eq_mul_eigenfunction_zero]
  simp [hermitePolynomial]
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
        (hermitePolynomial (n + 2) (√(m * ω / ℏ) * x))) * eigenfunction m ℏ ω 0 x)
  rw [deriv_deriv_eigenFunction_succ]
  congr 2
  trans (√(m * ω / ℏ) * 2 * (n + 1 + 1) * (√(m * ω / ℏ) *
    2 * (n + 1) * (hermitePolynomial n (√(m * ω / ℏ) * x))) +
    (-(m * ω) / ℏ) * √(m * ω / ℏ) * (4 * (n + 1 + 1) * x) *
    (hermitePolynomial (n + 1) (√(m * ω / ℏ) * x)) +
    (-(m * ω) / ℏ) * (1 + (-(m * ω) / ℏ) * x ^ 2) * (hermitePolynomial (n + 2) (√(m * ω / ℏ) * x)))
  · rw [deriv_hermitePolynomial_succ]
    simp
  trans ((m * ω / ℏ) * 2 * (n + 1 + 1) * (2 * (n + 1) * (hermitePolynomial n (√(m * ω / ℏ) * x))) +
        (- (m * ω) / ℏ) * √(m * ω / ℏ) * (4 * (n + 1 + 1) * x) *
        (hermitePolynomial (n + 1) (√(m * ω / ℏ) * x)) +
        (-(m * ω) / ℏ) * (1 + (-(m * ω) / ℏ) * x ^ 2) *
        (hermitePolynomial (n + 2) (√(m * ω / ℏ) * x)))
  · congr 2
    trans (↑√(m * ω / ℏ) * ↑√(m * ω / ℏ)) * 2 * (↑n + 1 + 1) *
    (2 * (↑n + 1) * ↑(hermitePolynomial n (√(m * ω / ℏ) * x)))
    · ring
    congr 3
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_div]
    congr 1
    refine Real.mul_self_sqrt ?_
    refine div_nonneg ?_ ?_
    exact (mul_nonneg_iff_of_pos_left hm).mpr hω
    exact le_of_lt hℏ
  trans (- m * ω / ℏ) * (2 * (n + 1 + 1) *
        (2 * (√(m * ω / ℏ) * x) * (hermitePolynomial (n + 1) (√(m * ω / ℏ) * x)) -
        2 * (n + 1) * (hermitePolynomial n (√(m * ω / ℏ) * x)))
        + (1 + (-(m * ω) / ℏ) * x ^ 2) * (hermitePolynomial (n + 2) (√(m * ω / ℏ) * x)))
  · ring
  trans (- m * ω / ℏ) * (2 * (n + 1 + 1) * (hermitePolynomial (n + 2) (√(m * ω / ℏ) * x))
        + (1 + (-(m * ω) / ℏ) * x ^ 2) * (hermitePolynomial (n + 2) (√(m * ω / ℏ) * x)))
  · congr
    simp [hermitePolynomial]
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

end HarmonicOscillator

end QuantumMechanics
