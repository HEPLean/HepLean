/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.PiTensorProduct
import Mathlib.RepresentationTheory.Rep
import PhysLean.Relativity.Lorentz.Group.Basic
/-!

## Pauli matrices

-/

namespace PauliMatrix

open Complex
open Matrix

/-- The zeroth Pauli-matrix as a `2 x 2` complex matrix.
  That is the matrix `!![1, 0; 0, 1]`. -/
def σ0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

/-- The first Pauli-matrix as a `2 x 2` complex matrix.
  That is, the matrix `!![0, 1; 1, 0]`. -/
def σ1 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The second Pauli-matrix as a `2 x 2` complex matrix.
  That is, the matrix `!![0, -I; I, 0]`. -/
def σ2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- The third Pauli-matrix as a `2 x 2` complex matrix.
  That is, the matrix `!![1, 0; 0, -1]`. -/
def σ3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The conjugate transpose of `σ0` is equal to `σ0`. -/
@[simp]
lemma σ0_selfAdjoint : σ0ᴴ = σ0 := by
  rw [eta_fin_two σ0ᴴ]
  simp [σ0]

/-- The conjugate transpose of `σ1` is equal to `σ1`. -/
@[simp]
lemma σ1_selfAdjoint : σ1ᴴ = σ1 := by
  rw [eta_fin_two σ1ᴴ]
  simp [σ1]

/-- The conjugate transpose of `σ2` is equal to `σ2`. -/
@[simp]
lemma σ2_selfAdjoint : σ2ᴴ = σ2 := by
  rw [eta_fin_two σ2ᴴ]
  simp [σ2]

/-- The conjugate transpose of `σ3` is equal to `σ3`. -/
@[simp]
lemma σ3_selfAdjoint : σ3ᴴ = σ3 := by
  rw [eta_fin_two σ3ᴴ]
  simp [σ3]

/-!

## Traces

-/

/-- The trace of `σ0` multiplied by `σ0` is equal to `2`. -/
@[simp]
lemma σ0_σ0_trace : Matrix.trace (σ0 * σ0) = 2 := by
  simp only [σ0, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, one_smul,
    tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply,
    trace_fin_two_of]
  norm_num

/-- The trace of `σ0` multiplied by `σ1` is equal to `0`. -/
@[simp]
lemma σ0_σ1_trace : Matrix.trace (σ0 * σ1) = 0 := by
  simp [σ0, σ1]

/-- The trace of `σ0` multiplied by `σ2` is equal to `0`. -/
@[simp]
lemma σ0_σ2_trace : Matrix.trace (σ0 * σ2) = 0 := by
  simp [σ0, σ2]

/-- The trace of `σ0` multiplied by `σ3` is equal to `0`. -/
@[simp]
lemma σ0_σ3_trace : Matrix.trace (σ0 * σ3) = 0 := by
  simp [σ0, σ3]

/-- The trace of `σ1` multiplied by `σ0` is equal to `0`. -/
@[simp]
lemma σ1_σ0_trace : Matrix.trace (σ1 * σ0) = 0 := by
  simp [σ1, σ0]

/-- The trace of `σ1` multiplied by `σ1` is equal to `2`. -/
@[simp]
lemma σ1_σ1_trace : Matrix.trace (σ1 * σ1) = 2 := by
  simp only [σ1, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, one_smul,
    tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply,
    trace_fin_two_of]
  norm_num

/-- The trace of `σ1` multiplied by `σ2` is equal to `0`. -/
@[simp]
lemma σ1_σ2_trace : Matrix.trace (σ1 * σ2) = 0 := by
  simp [σ1, σ2]

/-- The trace of `σ1` multiplied by `σ3` is equal to `0`. -/
@[simp]
lemma σ1_σ3_trace : Matrix.trace (σ1 * σ3) = 0 := by
  simp [σ1, σ3]

/-- The trace of `σ2` multiplied by `σ0` is equal to `0`. -/
@[simp]
lemma σ2_σ0_trace : Matrix.trace (σ2 * σ0) = 0 := by
  simp [σ2, σ0]

/-- The trace of `σ2` multiplied by `σ1` is equal to `0`. -/
@[simp]
lemma σ2_σ1_trace : Matrix.trace (σ2 * σ1) = 0 := by
  simp [σ2, σ1]

/-- The trace of `σ2` multiplied by `σ2` is equal to `2`. -/
@[simp]
lemma σ2_σ2_trace : Matrix.trace (σ2 * σ2) = 2 := by
  simp only [σ2, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, one_smul,
    tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply,
    trace_fin_two_of]
  norm_num

/-- The trace of `σ2` multiplied by `σ3` is equal to `0`. -/
@[simp]
lemma σ2_σ3_trace : Matrix.trace (σ2 * σ3) = 0 := by
  simp [σ2, σ3]

/-- The trace of `σ3` multiplied by `σ0` is equal to `0`. -/
@[simp]
lemma σ3_σ0_trace : Matrix.trace (σ3 * σ0) = 0 := by
  simp [σ3, σ0]

/-- The trace of `σ3` multiplied by `σ1` is equal to `0`. -/
@[simp]
lemma σ3_σ1_trace : Matrix.trace (σ3 * σ1) = 0 := by
  simp [σ3, σ1]

/-- The trace of `σ3` multiplied by `σ2` is equal to `0`. -/
@[simp]
lemma σ3_σ2_trace : Matrix.trace (σ3 * σ2) = 0 := by
  simp [σ3, σ2]

/-- The trace of `σ3` multiplied by `σ3` is equal to `2`. -/
@[simp]
lemma σ3_σ3_trace : Matrix.trace (σ3 * σ3) = 2 := by
  simp only [σ3, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, one_smul,
    tail_cons, zero_smul, empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply,
    trace_fin_two_of]
  norm_num

end PauliMatrix
