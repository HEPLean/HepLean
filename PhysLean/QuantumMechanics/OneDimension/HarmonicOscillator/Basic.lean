/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
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

/-- A quantum harmonic oscillator specified by a mass, a value of Plancck's and
  an angular frequency. -/
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
open PhysLean

variable (Q : HarmonicOscillator)

@[simp]
lemma m_mul_ω_div_two_ℏ_pos : 0 < Q.m * Q.ω / (2 * Q.ℏ) := by
  apply div_pos
  exact mul_pos Q.hm Q.hω
  exact mul_pos (by norm_num) Q.hℏ

@[simp]
lemma m_mul_ω_div_ℏ_pos : 0 < Q.m * Q.ω / Q.ℏ := by
  apply div_pos
  exact mul_pos Q.hm Q.hω
  exact Q.hℏ

lemma m_ne_zero : Q.m ≠ 0 := by
  have h1 := Q.hm
  linarith

lemma ℏ_ne_zero : Q.ℏ ≠ 0 := by
  have h1 := Q.hℏ
  linarith

/-- The Schrodinger Operator for the Harmonic oscillator on the space of functions.

  The prime `'` in the name is to signify that this is not defined on
  equivalence classes of square integrable functions. -/
noncomputable def schrodingerOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun y => - Q.ℏ ^ 2 / (2 * Q.m) * (deriv (deriv ψ) y) + 1/2 * Q.m * Q.ω^2 * y^2 * ψ y

end HarmonicOscillator
end OneDimension
end QuantumMechanics
