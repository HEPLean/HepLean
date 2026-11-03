/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Qubit.State

/-!
# Matrix qubit observable formulas

Pauli coordinates give the characteristic polynomial and observable expectations.

## i. Overview

The characteristic polynomial factors into the two expected roots. The trace pairing
of an observable and a Bloch state is a scalar plus a dot product. Measurement instruments
and outcome probabilities are not constructed here.

## ii. Key results

`QuantumMechanics.Qubit.det_pauliObservable_sub_smul_one`
and `trace_pauliObservable_mul_blochState`.

## iii. Table of contents

- A. Matrix qubit observable formulas

## iv. References

The imported modules provide the underlying algebraic and analytic results.

-/

@[expose] public section

/-! ## A. Matrix qubit observable formulas -/

open BigOperators
open scoped PauliMatrix

noncomputable section

namespace QuantumMechanics.Qubit

/-- The determinant of `A - xI` for `A = a₀I + a₁σ₁ + a₂σ₂ + a₃σ₃`. Thus the two
eigenvalues are `a₀ ± √(a₁² + a₂² + a₃²)`. -/
lemma det_pauliObservable_sub_smul_one (a₀ a₁ a₂ a₃ x : ℝ) :
    Matrix.det
      ((a₀ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (a₁ : ℂ) • σ (Sum.inr 0) + (a₂ : ℂ) • σ (Sum.inr 1) +
        (a₃ : ℂ) • σ (Sum.inr 2) - (x : ℂ) • 1) =
      ((a₀ + Real.sqrt (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) - x : ℝ) : ℂ) *
        (a₀ - Real.sqrt (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) - x : ℝ) := by
  simp [PauliMatrix.pauliMatrix, Matrix.det_fin_two, Matrix.one_fin_two]
  ring_nf
  rw [Complex.I_sq]
  norm_cast
  rw [Real.sq_sqrt (by positivity)]
  norm_num
  ring_nf

/-- The component formula `Tr(Aρ) = a₀ + a₁r₁ + a₂r₂ + a₃r₃` for
`A = a₀I + a · σ` and `ρ = (I + r · σ)/2`. -/
lemma trace_pauliObservable_mul_blochState (a₀ a₁ a₂ a₃ r₁ r₂ r₃ : ℝ) :
    (Matrix.trace
      (((a₀ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (a₁ : ℂ) • σ (Sum.inr 0) + (a₂ : ℂ) • σ (Sum.inr 1) +
          (a₃ : ℂ) • σ (Sum.inr 2)) *
        ((1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          (r₁ : ℂ) • σ (Sum.inr 0) + (r₂ : ℂ) • σ (Sum.inr 1) +
          (r₃ : ℂ) • σ (Sum.inr 2))))).re =
      a₀ + a₁ * r₁ + a₂ * r₂ + a₃ * r₃ := by
  simp [PauliMatrix.pauliMatrix, Matrix.trace_fin_two, Matrix.one_fin_two]
  ring_nf

end QuantumMechanics.Qubit
