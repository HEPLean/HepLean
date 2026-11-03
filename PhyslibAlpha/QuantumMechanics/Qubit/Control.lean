/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Qubit.State

/-!
# Piecewise-constant qubit control

Constant pulses and chronological pulse sequences describe qubit control protocols.

## i. Overview

Pulse duration and Rabi frequency determine a formal angle. The Hamiltonian and its
evolution matrix are defined for each pulse. A chronological list composes the matrices
in reverse product order. A separate Rodrigues-rotation calculation gives the ideal
Ramsey signal. Its identification with the pulse Hamiltonians remains future work.
The pulse axis is an arbitrary vector and is not assumed to have unit length.

## ii. Key results

`QuantumMechanics.Qubit.ramsey_z_signal`, `Pulse.ofAngle_angle`
and `PulseSequence.evolutionMatrix_cons`.

## iii. Table of contents

- A. Piecewise-constant qubit control

## iv. References

The imported modules provide the underlying algebraic and analytic results.

-/

@[expose] public section

/-! ## A. Piecewise-constant qubit control -/

open Constants
open scoped PauliMatrix

noncomputable section

namespace QuantumMechanics.Qubit

/-- Cartesian x-axis on the Bloch sphere. -/
def xAxis : Fin 3 → ℝ := ![1, 0, 0]

/-- Cartesian z-axis on the Bloch sphere. -/
def zAxis : Fin 3 → ℝ := ![0, 0, 1]

/-- Cartesian y-axis on the Bloch sphere. -/
def yAxis : Fin 3 → ℝ := ![0, 1, 0]

/-- Ramsey readout: a y-axis π/2 pulse, free z-precession through phase `φ`, and a
negative-y π/2 pulse convert the accumulated phase into the population signal `cos φ`. -/
lemma ramsey_z_signal (φ : ℝ) :
    rotateBloch (-yAxis)
      (rotateBloch zAxis (rotateBloch yAxis zAxis (Real.pi / 2)) φ)
      (Real.pi / 2) 2 = Real.cos φ := by
  simp [rotateBloch, yAxis, zAxis, dotProduct, cross_apply, Fin.sum_univ_succ]

/-- A constant resonant pulse with Hamiltonian `H = ℏΩ(n·σ)/2`. -/
structure Pulse where
  /-- Rotation axis. -/
  axis : Fin 3 → ℝ
  /-- Rabi frequency. -/
  rabiFrequency : ℝ
  /-- Pulse duration. -/
  duration : ℝ

namespace Pulse

/-- The rotation angle produced by a pulse. -/
def angle (P : Pulse) : ℝ := P.rabiFrequency * P.duration

/-- The constant Hamiltonian applied during a pulse. -/
def hamiltonian (P : Pulse) : Hamiltonian :=
  (ℏ * P.rabiFrequency / 2) •
    ∑ i : Fin 3, P.axis i • PauliMatrix.pauliSelfAdjoint (Sum.inr i)

/-- The explicit matrix applied by a pulse. -/
def evolutionMatrix (P : Pulse) : Matrix (Fin 2) (Fin 2) ℂ :=
  Qubit.evolutionMatrix P.hamiltonian P.duration

/-- A pulse whose duration produces a rotation through `θ`. -/
def ofAngle (axis : Fin 3 → ℝ) (Ω θ : ℝ) : Pulse where
  axis := axis
  rabiFrequency := Ω
  duration := θ / Ω

lemma ofAngle_angle (axis : Fin 3 → ℝ) (Ω θ : ℝ) (hΩ : Ω ≠ 0) :
    (ofAngle axis Ω θ).angle = θ := by
  simp [ofAngle, angle]
  field_simp [hΩ]

/-- A π pulse about `axis`. -/
def piPulse (axis : Fin 3 → ℝ) (Ω : ℝ) : Pulse := ofAngle axis Ω Real.pi

/-- A π/2 pulse about `axis`. -/
def piHalfPulse (axis : Fin 3 → ℝ) (Ω : ℝ) : Pulse := ofAngle axis Ω (Real.pi / 2)

lemma piPulse_angle (axis : Fin 3 → ℝ) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    (piPulse axis Ω).angle = Real.pi := ofAngle_angle axis Ω Real.pi hΩ

lemma piHalfPulse_angle (axis : Fin 3 → ℝ) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    (piHalfPulse axis Ω).angle = Real.pi / 2 := ofAngle_angle axis Ω (Real.pi / 2) hΩ

end Pulse

/-- A piecewise-constant control protocol, in chronological order. -/
abbrev PulseSequence := List Pulse

namespace PulseSequence

/-- Total duration of a pulse sequence. -/
def duration (S : PulseSequence) : ℝ := (S.map Pulse.duration).sum

/-- Ordered product of the pulse matrices. -/
def evolutionMatrix (S : PulseSequence) : Matrix (Fin 2) (Fin 2) ℂ :=
  (S.map Pulse.evolutionMatrix).reverse.prod

@[simp] lemma evolutionMatrix_nil : evolutionMatrix [] = 1 := rfl

@[simp] lemma evolutionMatrix_cons (P : Pulse) (S : PulseSequence) :
    evolutionMatrix (P :: S) = evolutionMatrix S * P.evolutionMatrix := by
  simp [evolutionMatrix]

end PulseSequence

end QuantumMechanics.Qubit
