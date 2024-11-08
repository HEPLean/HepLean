/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Basic
import Mathlib.Algebra.Lie.Classical
/-!

# The Minkowski matrix


-/

open Matrix
open InnerProductSpace
/-!

# The definition of the Minkowski Matrix

-/
/-- The `d.succ`-dimensional real matrix of the form `diag(1, -1, -1, -1, ...)`. -/
def minkowskiMatrix {d : ℕ} : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 1) (Fin d) ℝ

namespace minkowskiMatrix

variable {d : ℕ}

/-- Notation for `minkowskiMatrix`. -/
scoped[minkowskiMatrix] notation "η" => minkowskiMatrix

@[simp]
lemma sq : @minkowskiMatrix d * minkowskiMatrix = 1 := by
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_mul_diagonal]
  ext1 i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [diagonal, of_apply, Sum.inl.injEq, Sum.elim_inl, mul_one]
    split
    · rename_i h
      subst h
      simp_all only [one_apply_eq]
    · simp_all only [ne_eq, Sum.inl.injEq, not_false_eq_true, one_apply_ne]
  · rfl
  · rfl
  · simp only [diagonal, of_apply, Sum.inr.injEq, Sum.elim_inr, mul_neg, mul_one, neg_neg]
    split
    · rename_i h
      subst h
      simp_all only [one_apply_eq]
    · simp_all only [ne_eq, Sum.inr.injEq, not_false_eq_true, one_apply_ne]

@[simp]
lemma eq_transpose : minkowskiMatrixᵀ = @minkowskiMatrix d := by
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_transpose]

@[simp]
lemma det_eq_neg_one_pow_d : (@minkowskiMatrix d).det = (- 1) ^ d := by
  simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]

@[simp]
lemma η_apply_mul_η_apply_diag (μ : Fin 1 ⊕ Fin d) : η μ μ * η μ μ = 1 := by
  match μ with
  | Sum.inl _ => simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]
  | Sum.inr _ => simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]

lemma as_block : @minkowskiMatrix d =
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (-1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, ← fromBlocks_diagonal]
  refine fromBlocks_inj.mpr ?_
  simp only [diagonal_one, true_and]
  funext i j
  rw [← diagonal_neg]
  rfl

@[simp]
lemma off_diag_zero {μ ν : Fin 1 ⊕ Fin d} (h : μ ≠ ν) : η μ ν = 0 := by
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]
  exact diagonal_apply_ne _ h

lemma inl_0_inl_0 : @minkowskiMatrix d (Sum.inl 0) (Sum.inl 0) = 1 := by
  rfl

lemma inr_i_inr_i (i : Fin d) : @minkowskiMatrix d (Sum.inr i) (Sum.inr i) = -1 := by
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]
  simp_all only [diagonal_apply_eq, Sum.elim_inr]


variable (Λ Λ' : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)

/-- The dual of a matrix with respect to the Minkowski metric. -/
def dual : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ := η * Λᵀ * η

@[simp]
lemma dual_id : @dual d 1 = 1 := by
  simpa only [dual, transpose_one, mul_one] using minkowskiMatrix.sq

@[simp]
lemma dual_mul : dual (Λ * Λ') = dual Λ' * dual Λ := by
  simp only [dual, transpose_mul]
  trans η * Λ'ᵀ * (η * η) * Λᵀ * η
  · noncomm_ring [minkowskiMatrix.sq]
  · noncomm_ring

@[simp]
lemma dual_dual : dual (dual Λ) = Λ := by
  simp only [dual, transpose_mul, transpose_transpose, eq_transpose]
  trans (η * η) * Λ * (η * η)
  · noncomm_ring
  · noncomm_ring [minkowskiMatrix.sq]

@[simp]
lemma dual_eta : @dual d η = η := by
  simp only [dual, eq_transpose]
  noncomm_ring [minkowskiMatrix.sq]

@[simp]
lemma dual_transpose : dual Λᵀ = (dual Λ)ᵀ := by
  simp only [dual, transpose_transpose, transpose_mul, eq_transpose]
  noncomm_ring

@[simp]
lemma det_dual : (dual Λ).det = Λ.det := by
  simp only [dual, det_mul, minkowskiMatrix.det_eq_neg_one_pow_d, det_transpose]
  group
  norm_cast
  simp

lemma dual_apply (μ ν : Fin 1 ⊕ Fin d) :
    dual Λ μ ν = η μ μ * Λ ν μ * η ν ν := by
  simp only [dual, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mul_diagonal,
    diagonal_mul, transpose_apply, diagonal_apply_eq]

lemma dual_apply_minkowskiMatrix (μ ν : Fin 1 ⊕ Fin d) :
    dual Λ μ ν * η ν ν = η μ μ * Λ ν μ := by
  rw [dual_apply, mul_assoc]
  simp

end minkowskiMatrix
