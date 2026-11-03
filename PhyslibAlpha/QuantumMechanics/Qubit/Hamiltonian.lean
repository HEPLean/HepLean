/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.ForMathlib.OneParameterSubgroups.Unitary
public import Physlib.QuantumMechanics.PlanckConstant
public import PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint
public import QuantumInfo.States.Pure.Qubit
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Matrix qubit Hamiltonians and time evolution

A Hermitian two-level Hamiltonian has an explicit Pauli-decomposition evolution formula.

## i. Overview

The Hamiltonian splits into a scalar part and a Pauli vector. Stone’s bounded-generator
correspondence supplies unitary time evolution. Its matrix formula includes both zero
and nonzero Pauli radius.

## ii. Key results

`QuantumMechanics.Qubit.eq_sum_pauli` and `timeEvolution_apply_eq_evolutionMatrix`.

## iii. Table of contents

- A. Matrix qubit Hamiltonians and time evolution

## iv. References

The imported modules provide the underlying algebraic and analytic results.

-/

@[expose] public section

/-! ## A. Matrix qubit Hamiltonians and time evolution -/

open Constants
open scoped PauliMatrix

noncomputable section

namespace QuantumMechanics

namespace Qubit

section Qubit

/-- The standard two-dimensional complex Hilbert space of a qubit. -/
abbrev HilbertSpace := EuclideanSpace ℂ (Fin 2)

/-- A Hamiltonian of a qubit in the standard basis. -/
abbrev Hamiltonian := selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)

variable (H : Hamiltonian)

/-- The four real Pauli coefficients of a two-level Hamiltonian. -/
noncomputable def pauliCoeff : Fin 1 ⊕ Fin 3 → ℝ :=
  PauliMatrix.pauliBasis.repr H

/-- Every Hermitian `2 × 2` matrix is a real linear combination of the identity and the three
Pauli matrices. -/
lemma eq_sum_pauli :
    H = ∑ μ, pauliCoeff H μ • PauliMatrix.pauliSelfAdjoint μ := by
  simpa only [pauliCoeff, PauliMatrix.pauliBasis, Module.Basis.mk_apply] using
    (PauliMatrix.pauliBasis.sum_repr H).symm

/-- The familiar component form `A = a₀ I + a₁ σ₁ + a₂ σ₂ + a₃ σ₃`. -/
lemma eq_pauli_components :
    H.val = (pauliCoeff H (Sum.inl 0) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      (pauliCoeff H (Sum.inr 0) : ℂ) • σ (Sum.inr 0) +
      (pauliCoeff H (Sum.inr 1) : ℂ) • σ (Sum.inr 1) +
      (pauliCoeff H (Sum.inr 2) : ℂ) • σ (Sum.inr 2) := by
  let ι := (selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)).subtype
  have h := congrArg ι (eq_sum_pauli H)
  change ι H = ι (∑ μ, pauliCoeff H μ • PauliMatrix.pauliSelfAdjoint μ) at h
  rw [map_sum] at h
  simp_rw [show ∀ (r : ℝ) (A : Hamiltonian),
      ι (r • A) = r • A.val by intro r A; rfl] at h
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, PauliMatrix.pauliSelfAdjoint,
    PauliMatrix.pauliMatrix_inl_zero_eq_one] at h
  change H.val = _ at h
  rw [h]
  module

/-- The coefficient of the identity in the Pauli decomposition. -/
noncomputable def scalarPart : ℝ := pauliCoeff H (Sum.inl 0)

/-- The traceless, Pauli-vector part `a₁ σ₁ + a₂ σ₂ + a₃ σ₃`. -/
noncomputable def vectorPart : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 3, (pauliCoeff H (Sum.inr i) : ℂ) • σ (Sum.inr i)

/-- The length `√(a₁² + a₂² + a₃²)` of the Pauli vector. -/
noncomputable def pauliRadius : ℝ :=
  Real.sqrt (∑ i : Fin 3, (pauliCoeff H (Sum.inr i)) ^ 2)

lemma matrix_eq_scalar_add_vector (A : Hamiltonian) :
    A.val = (scalarPart A : ℂ) • 1 + vectorPart A := by
  rw [eq_pauli_components A]
  simp [scalarPart, vectorPart, Fin.sum_univ_three, PauliMatrix.pauliMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma vectorPart_sq (A : Hamiltonian) :
    vectorPart A * vectorPart A = (pauliRadius A ^ 2 : ℝ) • 1 := by
  simp only [vectorPart, pauliRadius, Fin.sum_univ_three, PauliMatrix.pauliMatrix]
  rw [Real.sq_sqrt]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two, Complex.real_smul] <;> ring_nf
    all_goals (rw [show Complex.I ^ 2 = -1 by rw [pow_two, Complex.I_mul_I]]; ring_nf)
  · positivity

lemma pauliRadius_nonneg (A : Hamiltonian) : 0 ≤ pauliRadius A :=
  Real.sqrt_nonneg _

lemma vectorPart_eq_zero_of_pauliRadius_eq_zero (A : Hamiltonian)
    (h : pauliRadius A = 0) : vectorPart A = 0 := by
  have hs : ∑ i : Fin 3, (pauliCoeff A (Sum.inr i)) ^ 2 = 0 := by
    rw [pauliRadius, Real.sqrt_eq_zero'] at h
    exact le_antisymm h (by positivity)
  have hcoeff (i : Fin 3) : pauliCoeff A (Sum.inr i) = 0 := by
    rw [Fin.sum_univ_three] at hs
    have h0 : pauliCoeff A (Sum.inr 0) ^ 2 = 0 := by
      nlinarith [sq_nonneg (pauliCoeff A (Sum.inr 0)),
        sq_nonneg (pauliCoeff A (Sum.inr 1)), sq_nonneg (pauliCoeff A (Sum.inr 2))]
    have h1 : pauliCoeff A (Sum.inr 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (pauliCoeff A (Sum.inr 0)),
        sq_nonneg (pauliCoeff A (Sum.inr 1)), sq_nonneg (pauliCoeff A (Sum.inr 2))]
    have h2 : pauliCoeff A (Sum.inr 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (pauliCoeff A (Sum.inr 0)),
        sq_nonneg (pauliCoeff A (Sum.inr 1)), sq_nonneg (pauliCoeff A (Sum.inr 2))]
    fin_cases i <;> simp_all
  simp [vectorPart, hcoeff]

end Qubit

end Qubit

/-- The bounded operator represented by a `2 × 2` matrix. -/
def Qubit.operator (A : Matrix (Fin 2) (Fin 2) ℂ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A

lemma Qubit.operator_isSelfAdjoint {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.IsHermitian) : IsSelfAdjoint (operator A) := by
  rw [isSelfAdjoint_iff]
  calc
    star (operator A) = operator (star A) := by
      exact (map_star (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) A).symm
    _ = operator A := by
      exact congrArg (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) hA

/-- The unitary time evolution generated by a qubit Hamiltonian. -/
def Qubit.timeEvolution (A : Qubit.Hamiltonian) :
    UnitaryOneParameterGroup Qubit.HilbertSpace :=
  UnitaryOneParameterGroup.ofSelfAdjoint (A := ((ℏ : ℂ)⁻¹) • Qubit.operator A.val)
    ((show IsSelfAdjoint (ℏ : ℂ) by simp [isSelfAdjoint_iff]).inv₀.smul
      (Qubit.operator_isSelfAdjoint A.property))

@[simp]
lemma Qubit.timeEvolution_apply (A : Qubit.Hamiltonian) (t : ℝ) :
    (timeEvolution A t :
      EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) =
      NormedSpace.exp
        ((-(t : ℂ) * Complex.I / ℏ) • operator A.val) := by
  rw [timeEvolution, UnitaryOneParameterGroup.ofSelfAdjoint_apply, smul_smul]
  congr 1

/-- The operator `-irA`. -/
noncomputable def ContinuousLinearMap.negIMul
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : K →L[ℂ] K) (r : ℝ) : K →L[ℂ] K := (-(r : ℂ) * Complex.I) • A

lemma ContinuousLinearMap.negIMul_pow_even
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : K →L[ℂ] K) (hA : A * A = 1) (r : ℝ) (n : ℕ) :
    negIMul A r ^ (2 * n) = ((-1 : ℂ) ^ n * (r : ℂ) ^ (2 * n)) • 1 := by
  rw [negIMul, smul_pow]
  have hApow : A ^ (2 * n) = 1 := by rw [pow_mul, pow_two, hA, one_pow]
  rw [hApow]
  apply congrArg (fun z : ℂ ↦ z • (1 : K →L[ℂ] K))
  have hc : (-(r : ℂ) * Complex.I) ^ 2 = -(r : ℂ) ^ 2 := by
    calc
      (-(r : ℂ) * Complex.I) ^ 2 = (r : ℂ) ^ 2 * (Complex.I * Complex.I) := by ring_nf
      _ = -(r : ℂ) ^ 2 := by rw [Complex.I_mul_I, mul_neg, mul_one]
  rw [pow_mul, hc, neg_pow]
  conv_rhs => rw [pow_mul]

lemma ContinuousLinearMap.negIMul_pow_odd
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : K →L[ℂ] K) (hA : A * A = 1) (r : ℝ) (n : ℕ) :
    negIMul A r ^ (2 * n + 1) =
      ((-1 : ℂ) ^ n * (r : ℂ) ^ (2 * n + 1) * (-Complex.I)) • A := by
  rw [pow_succ, negIMul_pow_even A hA]
  rw [negIMul, Algebra.smul_mul_assoc, one_mul, smul_smul]
  apply congrArg (fun z : ℂ ↦ z • A)
  simp only [mul_comm 2 n, pow_succ]
  ring_nf

lemma ContinuousLinearMap.hasSum_even_negIMul
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : K →L[ℂ] K) (hA : A * A = 1) (r : ℝ) :
    HasSum (fun n : ℕ ↦ ((2 * n).factorial : ℂ)⁻¹ • negIMul A r ^ (2 * n))
      ((Real.cos r : ℂ) • 1) := by
  convert (Complex.hasSum_cos (r : ℂ)).smul_const (1 : K →L[ℂ] K) using 1
  · funext n
    rw [negIMul_pow_even A hA, smul_smul]
    congr 1
    simp [div_eq_mul_inv]
    ring_nf
  · simp

lemma ContinuousLinearMap.hasSum_odd_negIMul
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (A : K →L[ℂ] K) (hA : A * A = 1) (r : ℝ) :
    HasSum (fun n : ℕ ↦ ((2 * n + 1).factorial : ℂ)⁻¹ • negIMul A r ^ (2 * n + 1))
      ((-(Real.sin r : ℂ) * Complex.I) • A) := by
  have hs := (Complex.hasSum_sin (r : ℂ)).smul_const ((-Complex.I) • A)
  convert hs using 1
  · funext n
    rw [negIMul_pow_odd A hA]
    simp [div_eq_mul_inv]
    module
  · rw [smul_smul]
    push_cast
    ring_nf

/-- If `A² = 1`, then `exp (-irA) = cos r • 1 - i sin r • A`. -/
lemma ContinuousLinearMap.exp_neg_I_mul_of_sq_eq_one
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : K →L[ℂ] K) (hA : A * A = 1) (r : ℝ) :
    NormedSpace.exp ((-(r : ℂ) * Complex.I) • A) =
      (Real.cos r : ℂ) • 1 + (-(Real.sin r : ℂ) * Complex.I) • A := by
  let x := negIMul A r
  have hexp := NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) x
  simp_rw [NormedSpace.expSeries_apply_eq] at hexp
  replace hexp := (Nat.divModEquiv 2).symm.hasSum_iff.mpr hexp
  dsimp [Function.comp_def] at hexp
  have hsplit : HasSum
      (fun n : ℕ ↦ ((2 * n).factorial : ℂ)⁻¹ • x ^ (2 * n) +
        ((2 * n + 1).factorial : ℂ)⁻¹ • x ^ (2 * n + 1)) (NormedSpace.exp x) := by
    simpa [Fin.sum_univ_two, Nat.divModEquiv, mul_comm, pow_succ] using
      hexp.prod_fiberwise (fun k ↦ hasSum_fintype (fun j : Fin 2 ↦
        ((Nat.divModEquiv 2).symm (k, j)).factorial.cast⁻¹ •
          x ^ (Nat.divModEquiv 2).symm (k, j)))
  exact HasSum.unique hsplit
    ((hasSum_even_negIMul A hA r).add (hasSum_odd_negIMul A hA r))

lemma ContinuousLinearMap.exp_smul_one
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (z : ℂ) :
    NormedSpace.exp (z • (1 : K →L[ℂ] K)) = Complex.exp z • 1 := by
  change NormedSpace.exp (algebraMap ℂ (K →L[ℂ] K) z) = _
  rw [← NormedSpace.algebraMap_exp_comm, Complex.exp_eq_exp_ℂ]
  simp [Algebra.algebraMap_eq_smul_one]

namespace Qubit

section Qubit

/-- The bounded operator corresponding to the Pauli-vector part of `A`. -/
noncomputable def vectorOperator (A : Hamiltonian) : HilbertSpace →L[ℂ] HilbertSpace :=
  operator (vectorPart A)

lemma hamiltonian_eq_scalar_add_vector (A : Hamiltonian) :
    operator A.val = (scalarPart A : ℂ) • 1 + vectorOperator A := by
  rw [matrix_eq_scalar_add_vector A]
  ext v i
  fin_cases i <;>
  simp [operator, vectorOperator, Matrix.mulVec, dotProduct]

lemma vectorOperator_sq (A : Hamiltonian) :
    vectorOperator A * vectorOperator A = (pauliRadius A ^ 2 : ℝ) • 1 := by
  ext v i
  change (vectorPart A).mulVec ((vectorPart A).mulVec v.ofLp) i = _
  rw [Matrix.mulVec_mulVec, vectorPart_sq A]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct]

/-- If the Pauli vector vanishes, time evolution is the global phase generated by the scalar
part of the Hamiltonian. -/
lemma timeEvolution_apply_of_pauliRadius_eq_zero (A : Hamiltonian)
    (h : pauliRadius A = 0) (t : ℝ) :
    (timeEvolution A t :
      EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) =
      Complex.exp (-(t : ℂ) * Complex.I * scalarPart A / ℏ) • 1 := by
  rw [timeEvolution_apply, hamiltonian_eq_scalar_add_vector A]
  have hvector : vectorOperator A = 0 := by
    rw [vectorOperator, vectorPart_eq_zero_of_pauliRadius_eq_zero A h]
    ext
    simp [operator]
  rw [hvector, add_zero, smul_smul]
  rw [ContinuousLinearMap.exp_smul_one]
  congr 2
  ring_nf

lemma exp_vectorOperator (A : Hamiltonian) (h : pauliRadius A ≠ 0) (t : ℝ) :
    NormedSpace.exp ((-(t : ℂ) * Complex.I / ℏ) • vectorOperator A) =
      (Real.cos (t * pauliRadius A / ℏ) : ℂ) • 1 +
        (-(Real.sin (t * pauliRadius A / ℏ) : ℂ) * Complex.I /
          pauliRadius A) • vectorOperator A := by
  let C : HilbertSpace →L[ℂ] HilbertSpace :=
    (pauliRadius A : ℂ)⁻¹ • vectorOperator A
  have hC : C * C = 1 := by
    have hr : (pauliRadius A : ℂ) ≠ 0 := by exact_mod_cast h
    change ((pauliRadius A : ℂ)⁻¹ • vectorOperator A) *
      ((pauliRadius A : ℂ)⁻¹ • vectorOperator A) = 1
    calc
      _ = ((pauliRadius A : ℂ)⁻¹ * (pauliRadius A : ℂ)⁻¹) •
          (vectorOperator A * vectorOperator A) := by
        ext v i
        simp [smul_smul]
      _ = 1 := by
        rw [vectorOperator_sq]
        ext v i
        simp [Complex.real_smul]
        field_simp [hr]
  rw [show (-(t : ℂ) * Complex.I / ℏ) • vectorOperator A =
      ((-(t * pauliRadius A / ℏ : ℝ) : ℂ) * Complex.I) • C by
    dsimp [C]
    rw [smul_smul]
    congr 1
    push_cast
    have hr : (pauliRadius A : ℂ) ≠ 0 := by exact_mod_cast h
    field_simp [hr]]
  rw [ContinuousLinearMap.exp_neg_I_mul_of_sq_eq_one C hC]
  congr 1
  dsimp [C]
  rw [smul_smul]
  congr 1

/-- For nonzero Pauli radius, the time evolution of `A = a₀ I + a · σ` is a global phase
times the usual cosine–sine rotation generated by its normalized Pauli vector. -/
lemma timeEvolution_apply_of_pauliRadius_ne_zero (A : Hamiltonian)
    (h : pauliRadius A ≠ 0) (t : ℝ) :
    (timeEvolution A t :
      EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) =
      Complex.exp (-(t : ℂ) * Complex.I * scalarPart A / ℏ) •
        ((Real.cos (t * pauliRadius A / ℏ) : ℂ) • 1 +
          (-(Real.sin (t * pauliRadius A / ℏ) : ℂ) * Complex.I /
            pauliRadius A) • vectorOperator A) := by
  let : NormedAlgebra ℚ
      (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) :=
    .restrictScalars ℚ ℂ _
  rw [timeEvolution_apply, hamiltonian_eq_scalar_add_vector A, smul_add]
  let c : ℂ := -(t : ℂ) * Complex.I / ℏ
  let B := vectorOperator A
  have hcomm : Commute (c • ((scalarPart A : ℂ) •
      (1 : HilbertSpace →L[ℂ] HilbertSpace))) (c • B) := by
    change _ * _ = _ * _
    ext v i
    simp [smul_smul]
    left
    ring
  rw [NormedSpace.exp_add_of_commute hcomm]
  have hscalar : NormedSpace.exp (c • ((scalarPart A : ℂ) •
      (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)))) =
      Complex.exp (-(t : ℂ) * Complex.I * scalarPart A / ℏ) • 1 := by
    rw [smul_smul, ContinuousLinearMap.exp_smul_one]
    congr 2
    dsimp [c]
    ring_nf
  rw [hscalar]
  change Complex.exp (-(t : ℂ) * Complex.I * scalarPart A / ℏ) •
      NormedSpace.exp (c • B) = _
  congr 1
  exact exp_vectorOperator A h t

/-- The explicit time-evolution matrix of a two-level Hamiltonian. -/
noncomputable def evolutionMatrix (A : Hamiltonian) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  let phase := Complex.exp (-(t : ℂ) * Complex.I * scalarPart A / ℏ)
  if pauliRadius A = 0 then
    phase • 1
  else
    phase • ((Real.cos (t * pauliRadius A / ℏ) : ℂ) • 1 +
      (-(Real.sin (t * pauliRadius A / ℏ) : ℂ) * Complex.I /
        pauliRadius A) • vectorPart A)

/-- The evolution generated by any Hermitian `2 × 2` matrix is represented by its explicit
Pauli-decomposition formula `e⁻ⁱᵗᵃ⁰/ℏ (cos (tr/ℏ) I - i sin (tr/ℏ) (a · σ)/r)`, with the
scalar case included. -/
lemma timeEvolution_apply_eq_evolutionMatrix (A : Hamiltonian) (t : ℝ) :
    (timeEvolution A t :
      EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) =
      operator (evolutionMatrix A t) := by
  by_cases h : pauliRadius A = 0
  · rw [timeEvolution_apply_of_pauliRadius_eq_zero A h]
    simp [evolutionMatrix, h]
    ext v i
    simp [operator]
  · rw [timeEvolution_apply_of_pauliRadius_ne_zero A h]
    simp [evolutionMatrix, h]
    ext v i
    simp [operator, vectorOperator, Matrix.mulVec, dotProduct]

end Qubit

end Qubit

end QuantumMechanics
