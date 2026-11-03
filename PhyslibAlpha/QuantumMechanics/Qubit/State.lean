/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Qubit.Hamiltonian
public import PhyslibAlpha.QuantumMechanics.StinespringDilation
public import Mathlib.Analysis.Matrix.Spectrum
public import PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Matrix qubit states and Bloch evolution

Density matrices have Bloch coordinates with explicit purity, entropy and evolution formulas.

## i. Overview

The Bloch components are Pauli expectation values. The Pauli expansion gives the
purity and von Neumann entropy in terms of the Bloch radius. Unitary conjugation gives
the explicit Bloch trajectory. The state-space equivalence with the closed Bloch ball
is not constructed in this file.

## ii. Key results

`QuantumMechanics.Qubit.eq_bloch`, `vonNeumannEntropy_eq_blochRadius`
and `evolvedBlochVector_eq_blochTrajectory`.

## iii. Table of contents

- A. Bloch decomposition and state invariants
- B. Time evolution of the Bloch vector

## iv. References

The imported modules provide the underlying algebraic and analytic results.

-/

@[expose] public section

open BigOperators
open Constants
open scoped PauliMatrix
open scoped Matrix ComplexOrder

noncomputable section

namespace QuantumMechanics.Qubit

/-- A qubit state is an Alpha density matrix on the two-dimensional Hilbert space. -/
abbrev State := densityMatrix (Fin 2) (R := ℂ)

/-- A qubit density matrix as a self-adjoint observable. -/
def stateObservable (rho : State) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨rho.val, rho.property.1.isHermitian⟩

/-- The purity `Tr(ρ²)` of a qubit density matrix. -/
def purity (rho : State) : ℝ := (Matrix.trace (rho.val * rho.val)).re

/-- The real eigenvalues of a qubit density matrix. -/
noncomputable def stateEigenvalues (rho : State) : Fin 2 → ℝ :=
  rho.property.1.isHermitian.eigenvalues

/-- The von Neumann entropy of a qubit density matrix, with natural logarithms. -/
noncomputable def vonNeumannEntropy (rho : State) : ℝ :=
  ∑ i, Real.negMulLog (stateEigenvalues rho i)

variable (rho : State)

/-! ## A. Bloch decomposition and state invariants -/

/-- A spatial Pauli matrix regarded as a qubit observable. -/
def qubitPauliObservable (i : Fin 3) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  PauliMatrix.pauliSelfAdjoint (Sum.inr i)

/-- The coefficient of a Pauli matrix in the real Pauli-basis expansion of `rho`. -/
noncomputable def qubitPauliCoeff (mu : Fin 1 ⊕ Fin 3) : ℝ :=
  (1 / 2 : ℝ) * (Matrix.trace (PauliMatrix.pauliMatrix mu * rho.val)).re

/-- The Bloch-vector component `r_i = Tr(sigma_i rho)`. -/
noncomputable def blochComponent (i : Fin 3) : ℝ :=
  2 * qubitPauliCoeff rho (Sum.inr i)

/-- The Bloch vector of a qubit state. -/
noncomputable def blochVector : Fin 3 → ℝ := fun i ↦ blochComponent rho i

/-- Length of the Bloch vector. -/
noncomputable def blochRadius : ℝ :=
  Real.sqrt (∑ i : Fin 3, blochVector rho i ^ 2)

/-- Every qubit density matrix is a real linear combination of the four Pauli matrices. -/
lemma state_eq_sum_pauli :
    stateObservable rho = ∑ mu, qubitPauliCoeff rho mu • PauliMatrix.pauliSelfAdjoint mu := by
  symm
  apply PauliMatrix.selfAdjoint_ext
  all_goals
    simp only [qubitPauliCoeff, Fintype.sum_sum_type, Finset.univ_unique,
      Fin.default_eq_zero, Finset.sum_singleton, Fin.sum_univ_three,
      PauliMatrix.pauliSelfAdjoint, stateObservable, AddSubgroup.coe_add, selfAdjoint.val_smul,
      mul_add, Algebra.mul_smul_comm, Matrix.trace_add, Matrix.trace_smul]
  all_goals simp [KroneckerDelta.kroneckerDelta]; ring

/-- The identity coefficient of a density matrix is `1 / 2`, because its trace is one. -/
lemma qubitPauliCoeff_identity :
    qubitPauliCoeff rho (Sum.inl 0) = 1 / 2 := by
  simp [qubitPauliCoeff, PauliMatrix.pauliMatrix, rho.property.2]

/-- The Bloch-sphere form of an arbitrary qubit density matrix. -/
lemma eq_bloch :
    stateObservable rho = (1 / 2 : ℝ) •
      ((1 : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) +
        ∑ i : Fin 3, blochComponent rho i • qubitPauliObservable i) := by
  rw [state_eq_sum_pauli rho]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, qubitPauliCoeff_identity, blochComponent,
    qubitPauliObservable]
  simp [PauliMatrix.pauliSelfAdjoint, PauliMatrix.pauliMatrix]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Subtype.ext
  change qubitPauliCoeff rho (Sum.inr i) • PauliMatrix.pauliMatrix (Sum.inr i) =
    (2⁻¹ : ℝ) • ((2 * qubitPauliCoeff rho (Sum.inr i)) •
      PauliMatrix.pauliMatrix (Sum.inr i))
  rw [smul_smul]
  congr 1
  ring

/-- The purity is `(1 + |r|²)/2` for a qubit. -/
lemma purity_eq_blochRadius :
    purity rho = (1 + blochRadius rho ^ 2) / 2 := by
  unfold purity
  rw [blochRadius, Real.sq_sqrt (by positivity)]
  have h00 := congrArg Complex.im (rho.property.1.isHermitian.apply 0 0)
  have h11 := congrArg Complex.im (rho.property.1.isHermitian.apply 1 1)
  have h01r := congrArg Complex.re (rho.property.1.isHermitian.apply 0 1)
  have h01i := congrArg Complex.im (rho.property.1.isHermitian.apply 0 1)
  have htr : (rho.val 0 0).re + (rho.val 1 1).re = 1 := by
    simpa only [Matrix.trace_fin_two, Complex.add_re, Complex.one_re] using
      congrArg Complex.re rho.property.2
  simp only [Complex.star_def, Complex.conj_im, Complex.conj_re] at h00 h11 h01r h01i
  change (Matrix.trace (rho.val * rho.val)).re = _
  simp [blochVector, blochComponent, qubitPauliCoeff, PauliMatrix.pauliMatrix,
    Matrix.trace_fin_two, Matrix.one_fin_two, Matrix.mul_apply, Fin.sum_univ_succ]
  have hd0 : (rho.val 0 0).im = 0 := by linarith
  have hd1 : (rho.val 1 1).im = 0 := by linarith
  rw [hd0, hd1, ← h01r, ← h01i]
  nlinarith [congrArg (fun x : ℝ => x ^ 2) htr]

lemma spectrum_sq_sum_eq_purity :
    ∑ i, stateEigenvalues rho i ^ 2 = purity rho := by
  have h : ∑ i, (rho.property.1.isHermitian.eigenvalues i) ^ 2 = (rho.val * rho.val).trace := by
    have hspectral := Matrix.IsHermitian.spectral_theorem rho.property.1.isHermitian
    conv_rhs => rw [hspectral]
    simp [Matrix.trace_mul_comm, Matrix.mul_assoc]
    ring
  simpa [purity, stateEigenvalues, ← Complex.ofReal_pow] using congrArg Complex.re h

/-- A qubit's von Neumann entropy is the binary entropy determined by its Bloch radius. -/
lemma vonNeumannEntropy_eq_blochRadius :
    vonNeumannEntropy rho = Real.binEntropy ((1 + blochRadius rho) / 2) := by
  have hsum : stateEigenvalues rho 0 + stateEigenvalues rho 1 = 1 := by
    calc
      _ = (rho.val.trace).re := by
        simpa [Fin.sum_univ_two, stateEigenvalues] using
          congrArg Complex.re rho.property.1.isHermitian.trace_eq_sum_eigenvalues.symm
      _ = 1 := congrArg Complex.re rho.property.2
  have hsq : stateEigenvalues rho 0 ^ 2 + stateEigenvalues rho 1 ^ 2 =
      (1 + blochRadius rho ^ 2) / 2 := by
    rw [← purity_eq_blochRadius rho]
    simpa [Fin.sum_univ_two] using spectrum_sq_sum_eq_purity rho
  have hr : 0 ≤ blochRadius rho := Real.sqrt_nonneg _
  have hroot : stateEigenvalues rho 0 = (1 + blochRadius rho) / 2 ∨
      stateEigenvalues rho 0 = (1 - blochRadius rho) / 2 := by
    have hfactor :
        (2 * stateEigenvalues rho 0 - 1 - blochRadius rho) *
          (2 * stateEigenvalues rho 0 - 1 + blochRadius rho) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · left
      nlinarith
    · right
      nlinarith
  unfold vonNeumannEntropy
  rw [Fin.sum_univ_two]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rcases hroot with h | h
  · rw [h]
    have hq : stateEigenvalues rho 1 = 1 - (1 + blochRadius rho) / 2 := by
      nlinarith
    rw [hq]
  · rw [h]
    have hq : stateEigenvalues rho 1 = (1 + blochRadius rho) / 2 := by
      nlinarith
    have hminus : 1 - (1 + blochRadius rho) / 2 = (1 - blochRadius rho) / 2 := by
      ring
    rw [hq, hminus, add_comm]

/-! ## B. Time evolution of the Bloch vector -/

/-- Rodrigues rotation of a Bloch vector about `n` through angle `θ`. -/
noncomputable def rotateBloch (n r : Fin 3 → ℝ) (θ : ℝ) : Fin 3 → ℝ :=
  fun i ↦ Real.cos θ * r i + Real.sin θ * (n ⨯₃ r) i +
    (1 - Real.cos θ) * (n ⬝ᵥ r) * n i

/-- The rotation axis determined by the non-scalar part of a Hamiltonian. -/
noncomputable def hamiltonianAxis (A : Hamiltonian) : Fin 3 → ℝ :=
  fun i ↦ pauliCoeff A (Sum.inr i) / pauliRadius A

/-- For `A = a₀ I + a · σ`, the Bloch vector is constant when `a = 0`; otherwise it
rotates about `a / |a|` through the angle `2t|a| / ℏ`. The scalar part `a₀ I` has no effect. -/
noncomputable def blochTrajectory (A : Hamiltonian) (rho : State) (t : ℝ) :
    Fin 3 → ℝ :=
  if pauliRadius A = 0 then blochVector rho
  else
    let c := Real.cos (t * pauliRadius A / ℏ)
    let q := Real.sin (t * pauliRadius A / ℏ) / pauliRadius A
    let a : Fin 3 → ℝ := fun i ↦ pauliCoeff A (Sum.inr i)
    fun i ↦ c ^ 2 * blochVector rho i + 2 * c * q * (a ⨯₃ blochVector rho) i +
      q ^ 2 * (2 * (a ⬝ᵥ blochVector rho) * a i -
        (∑ j, a j ^ 2) * blochVector rho i)

/-- The Bloch vector obtained by evolving `rho` with the time-evolution matrix generated by `A`. -/
noncomputable def evolvedBlochVector (A : Hamiltonian) (rho : State) (t : ℝ) :
    Fin 3 → ℝ := fun i ↦
  (Matrix.trace (PauliMatrix.pauliMatrix (Sum.inr i) *
    (evolutionMatrix A t * rho.val * (evolutionMatrix A t).conjTranspose))).re

set_option maxRecDepth 2000 in
/-- Hamiltonian time evolution rotates the initial Bloch vector according to `blochTrajectory`. -/
lemma evolvedBlochVector_eq_blochTrajectory (A : Hamiltonian) (rho : State) (t : ℝ) :
    evolvedBlochVector A rho t = blochTrajectory A rho t := by
  funext i
  have hphase :
      Complex.exp (-((t : ℂ) * Complex.I * scalarPart A) / ℏ) *
        starRingEnd ℂ (Complex.exp (-((t : ℂ) * Complex.I * scalarPart A) / ℏ)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp
  by_cases h : pauliRadius A = 0
  · have hevol : evolutionMatrix A t * rho.val * (evolutionMatrix A t).conjTranspose =
        rho.val := by
      ext j k
      fin_cases j <;> fin_cases k <;>
        simp [evolutionMatrix, h, Matrix.mul_apply, Fin.sum_univ_two] <;>
        rw [mul_right_comm, hphase, one_mul]
    simp [evolvedBlochVector, blochTrajectory, h, hevol, blochVector,
      blochComponent, qubitPauliCoeff]
  · let phase := Complex.exp (-((t : ℂ) * Complex.I * scalarPart A) / ℏ)
    let c := Real.cos (t * pauliRadius A / ℏ)
    let q := Real.sin (t * pauliRadius A / ℏ) / pauliRadius A
    let a : Fin 3 → ℝ := fun j ↦ pauliCoeff A (Sum.inr j)
    let R : Matrix (Fin 2) (Fin 2) ℂ :=
      (c : ℂ) • 1 + (-(q : ℂ) * Complex.I) • vectorPart A
    have hevolution : evolutionMatrix A t = phase • R := by
      simp [evolutionMatrix, h, phase, R, c, q]
      module
    have hcancel :
        (phase • R) * rho.val * (phase • R).conjTranspose =
          R * rho.val * R.conjTranspose := by
      rw [Matrix.conjTranspose_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm (star phase) phase, show phase * star phase = 1 by exact hphase]
      simp
    simp only [evolvedBlochVector]
    rw [hevolution, hcancel]
    have hR : R = !![(c : ℂ) - Complex.I * (q * a 2),
        -(q * a 1 : ℝ) - Complex.I * (q * a 0);
        (q * a 1 : ℝ) - Complex.I * (q * a 0),
        (c : ℂ) + Complex.I * (q * a 2)] := by
      ext j k
      fin_cases j <;> fin_cases k <;>
        simp [R, a, vectorPart, PauliMatrix.pauliMatrix, Fin.sum_univ_succ] <;>
        ring_nf <;> simp [Complex.I_sq]
      all_goals ring
    rw [hR]
    fin_cases i <;>
      simp [blochTrajectory, h,
        a, blochVector, blochComponent, qubitPauliCoeff,
        PauliMatrix.pauliMatrix, Matrix.trace_fin_two, Matrix.one_fin_two,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, cross_apply] <;>
      dsimp [c, q, a] <;>
      ring

end QuantumMechanics.Qubit
