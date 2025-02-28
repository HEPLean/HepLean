/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Parity
import PhysLean.Meta.TODO.Basic
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

-/

/-!

## Some preliminary results about Complex.ofReal .

To be moved.

-/

lemma Complex.ofReal_hasDerivAt : HasDerivAt Complex.ofReal 1 x := by
  let f1 : ℂ → ℂ := id
  change HasDerivAt (f1 ∘ Complex.ofReal) 1 x
  apply HasDerivAt.comp_ofReal
  simp only [f1]
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

/-- A quantum harmonic oscillator specified by a three
  real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, and
  an angular frequency `ω`. All three of these parameters are assumed to be positive. -/
structure HarmonicOscillator where
  /-- The mass of the particle. -/
  m : ℝ
  /-- Reduced Planck's constant. -/
  ℏ : ℝ
  /-- The angular frequency of the harmonic oscillator. -/
  ω : ℝ
  hℏ : 0 < ℏ
  hω : 0 < ω
  hm : 0 < m

namespace HarmonicOscillator

open Nat
open PhysLean HilbertSpace
open MeasureTheory

variable (Q : HarmonicOscillator)

@[simp]
lemma m_mul_ω_div_two_ℏ_pos : 0 < Q.m * Q.ω / (2 * Q.ℏ) := by
  apply div_pos
  · exact mul_pos Q.hm Q.hω
  · exact mul_pos (by norm_num) Q.hℏ

@[simp]
lemma m_mul_ω_div_ℏ_pos : 0 < Q.m * Q.ω / Q.ℏ := by
  apply div_pos
  · exact mul_pos Q.hm Q.hω
  · exact Q.hℏ

lemma m_ne_zero : Q.m ≠ 0 := by
  have h1 := Q.hm
  linarith

lemma ℏ_ne_zero : Q.ℏ ≠ 0 := by
  have h1 := Q.hℏ
  linarith

/-!

## The characteristic length

-/

/-- The characteristic length `ξ` of the harmonic oscilator is defined
  as `√(ℏ /(m ω))`. -/
noncomputable def ξ : ℝ := √(Q.ℏ / (Q.m * Q.ω))

lemma ξ_nonneg : 0 ≤ Q.ξ := Real.sqrt_nonneg _

@[simp]
lemma ξ_pos : 0 < Q.ξ := by
  rw [ξ]
  apply Real.sqrt_pos.mpr
  apply div_pos
  · exact Q.hℏ
  · exact mul_pos Q.hm Q.hω

@[simp]
lemma ξ_ne_zero : Q.ξ ≠ 0 := Ne.symm (_root_.ne_of_lt Q.ξ_pos)

lemma ξ_sq : Q.ξ^2 = Q.ℏ / (Q.m * Q.ω) := by
  rw [ξ]
  apply Real.sq_sqrt
  apply div_nonneg
  · exact le_of_lt Q.hℏ
  · exact mul_nonneg (le_of_lt Q.hm) (le_of_lt Q.hω)

@[simp]
lemma ξ_abs : abs Q.ξ = Q.ξ := abs_of_nonneg Q.ξ_nonneg

lemma one_over_ξ : 1/Q.ξ = √(Q.m * Q.ω / Q.ℏ) := by
  have := Q.hℏ
  field_simp [ξ]

lemma ξ_inverse : Q.ξ⁻¹ = √(Q.m * Q.ω / Q.ℏ):= by
  rw [inv_eq_one_div]
  exact one_over_ξ Q

lemma one_over_ξ_sq : (1/Q.ξ)^2 = Q.m * Q.ω / Q.ℏ := by
  rw [one_over_ξ]
  refine Real.sq_sqrt (le_of_lt Q.m_mul_ω_div_ℏ_pos)

TODO "The momentum operator should be moved to a more general file."

/-- The momentum operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `- i ℏ ψ'`.

  The notation `Pᵒᵖ` can be used for the momentum operator. -/
noncomputable def momentumOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => - Complex.I * Q.ℏ * deriv ψ x

@[inherit_doc momentumOperator]
scoped[QuantumMechanics.OneDimension.HarmonicOscillator] notation "Pᵒᵖ" => momentumOperator

/-- The position operator is defined as the map from `ℝ → ℂ` to `ℝ → ℂ` taking
  `ψ` to `x ψ'`.

  The notation `Xᵒᵖ` can be used for the momentum operator. -/
noncomputable def positionOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => x * ψ x

@[inherit_doc positionOperator]
scoped[QuantumMechanics.OneDimension.HarmonicOscillator] notation "Xᵒᵖ" => positionOperator

/-- For a harmonic oscillator, the Schrodinger Operator corresponding to it
  is defined as the function from `ℝ → ℂ` to `ℝ → ℂ` taking

  `ψ ↦ - ℏ^2 / (2 * m) * ψ'' + 1/2 * m * ω^2 * x^2 * ψ`. -/
noncomputable def schrodingerOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => - Q.ℏ ^ 2 / (2 * Q.m) * (deriv (deriv ψ) x) + 1/2 * Q.m * Q.ω^2 * x^2 * ψ x

lemma schrodingerOperator_eq (ψ : ℝ → ℂ) :
    Q.schrodingerOperator ψ = (- Q.ℏ ^ 2 / (2 * Q.m)) •
    (deriv (deriv ψ)) + (1/2 * Q.m * Q.ω^2) • ((fun x => Complex.ofReal x ^2) * ψ) := by
  funext x
  simp only [schrodingerOperator, one_div, Pi.add_apply, Pi.smul_apply, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Pi.mul_apply, Complex.ofReal_inv, add_right_inj]
  ring

/-- The schrodinger operator written in terms of `ξ`. -/
lemma schrodingerOperator_eq_ξ (ψ : ℝ → ℂ) : Q.schrodingerOperator ψ =
    fun x => (Q.ℏ ^2 / (2 * Q.m)) * (- (deriv (deriv ψ) x) +  (1/Q.ξ^2 )^2 * x^2 * ψ x) := by
  funext x
  simp [schrodingerOperator_eq, ξ_sq, ξ_inverse, ξ_ne_zero, ξ_pos, ξ_abs, ← Complex.ofReal_pow]
  have hm' := Complex.ofReal_ne_zero.mpr Q.m_ne_zero
  have hℏ' := Complex.ofReal_ne_zero.mpr Q.ℏ_ne_zero
  field_simp
  ring

/-- The Schrodinger operator commutes with the parity operator. -/
lemma schrodingerOperator_parity (ψ : ℝ → ℂ) :
    Q.schrodingerOperator (parity ψ) = parity (Q.schrodingerOperator ψ) := by
  funext x
  simp only [schrodingerOperator, parity, LinearMap.coe_mk, AddHom.coe_mk, one_div,
    Complex.ofReal_neg, even_two, Even.neg_pow, add_left_inj, mul_eq_mul_left_iff, div_eq_zero_iff,
    neg_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    Complex.ofReal_eq_zero, _root_.mul_eq_zero, false_or]
  left
  have h1 (ψ : ℝ → ℂ) : (fun x => (deriv fun x => ψ (-x)) x) = fun x => - deriv ψ (-x) := by
    funext x
    rw [← deriv_comp_neg]
  change deriv (fun x=> (deriv fun x => ψ (-x)) x) x = _
  simp [h1]

end HarmonicOscillator
end OneDimension
end QuantumMechanics
