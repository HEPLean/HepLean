/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
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

/-- The Minkowski matrix is self-inverting. -/
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

/-- The Minkowski matrix is symmetric. -/
@[simp]
lemma eq_transpose : minkowskiMatrixᵀ = @minkowskiMatrix d := by
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_transpose]

/-- The determinant of the Minkowski matrix is equal to `-1` to the power
  of the number of spatial dimensions. -/
@[simp]
lemma det_eq_neg_one_pow_d : (@minkowskiMatrix d).det = (- 1) ^ d := by
  simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]

/-- Multiplying any element on the diagonal of the Minkowski matrix by itself gives `1`. -/
@[simp]
lemma η_apply_mul_η_apply_diag (μ : Fin 1 ⊕ Fin d) : η μ μ * η μ μ = 1 := by
  match μ with
  | Sum.inl _ => simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]
  | Sum.inr _ => simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]

/-- The Minkowski matrix as a block matrix. -/
lemma as_block : @minkowskiMatrix d =
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (-1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, ← fromBlocks_diagonal]
  refine fromBlocks_inj.mpr ?_
  simp only [diagonal_one, true_and]
  funext i j
  rw [← diagonal_neg]
  rfl

/-- The off diagonal elements of the Minkowski matrix are zero. -/
@[simp]
lemma off_diag_zero {μ ν : Fin 1 ⊕ Fin d} (h : μ ≠ ν) : η μ ν = 0 := by
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]
  exact diagonal_apply_ne _ h

/-- The `time-time` component of the Minkowski matrix is `1`. -/
lemma inl_0_inl_0 : @minkowskiMatrix d (Sum.inl 0) (Sum.inl 0) = 1 := by
  rfl

/-- The space diagonal components of the Minkowski matrix are `-1`. -/
lemma inr_i_inr_i (i : Fin d) : @minkowskiMatrix d (Sum.inr i) (Sum.inr i) = -1 := by
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]
  simp_all only [diagonal_apply_eq, Sum.elim_inr]

/-- The time components of a vector acted on by the Minkowski matrix remains unchanged. -/
@[simp]
lemma mulVec_inl_0 (v : (Fin 1 ⊕ Fin d) → ℝ) :
    (η *ᵥ v) (Sum.inl 0)= v (Sum.inl 0) := by
  simp only [mulVec, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mulVec_diagonal]
  simp only [Fin.isValue, diagonal_dotProduct, Sum.elim_inl, one_mul]

/-- The space components of a vector acted on by the Minkowski matrix swaps sign. -/
@[simp]
lemma mulVec_inr_i (v : (Fin 1 ⊕ Fin d) → ℝ) (i : Fin d) :
    (η *ᵥ v) (Sum.inr i)= - v (Sum.inr i) := by
  simp only [mulVec, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mulVec_diagonal]
  simp only [diagonal_dotProduct, Sum.elim_inr, neg_mul, one_mul]

variable (Λ Λ' : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)

/-- The dual of a matrix with respect to the Minkowski metric.
  A suitable name fo this construction is the Minkowski dual. -/
def dual : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ := η * Λᵀ * η

/-- The Minkowski dual of the identity is the identity. -/
@[simp]
lemma dual_id : @dual d 1 = 1 := by
  simpa only [dual, transpose_one, mul_one] using minkowskiMatrix.sq

/-- The Minkowski dual swaps multiplications (acts contravariantly). -/
@[simp]
lemma dual_mul : dual (Λ * Λ') = dual Λ' * dual Λ := by
  simp only [dual, transpose_mul]
  trans η * Λ'ᵀ * (η * η) * Λᵀ * η
  · noncomm_ring [minkowskiMatrix.sq]
  · noncomm_ring

/-- The Minkowski dual is involutive (i.e. `dual (dual Λ)) = Λ`). -/
@[simp]
lemma dual_dual : Function.Involutive (@dual d) := by
  intro Λ
  simp only [dual, transpose_mul, transpose_transpose, eq_transpose]
  trans (η * η) * Λ * (η * η)
  · noncomm_ring
  · noncomm_ring [minkowskiMatrix.sq]

/-- The Minkowski dual preserves the Minkowski matrix. -/
@[simp]
lemma dual_eta : @dual d η = η := by
  simp only [dual, eq_transpose]
  noncomm_ring [minkowskiMatrix.sq]

/-- The Minkowski dual commutes with the transpose. -/
@[simp]
lemma dual_transpose : dual Λᵀ = (dual Λ)ᵀ := by
  simp only [dual, transpose_transpose, transpose_mul, eq_transpose]
  noncomm_ring

/-- The Minkowski dual preserves determinants. -/
@[simp]
lemma det_dual : (dual Λ).det = Λ.det := by
  simp only [dual, det_mul, minkowskiMatrix.det_eq_neg_one_pow_d, det_transpose]
  group
  norm_cast
  simp

/-- Expansion of the components of the Minkowski dual in terms of the components
  of the original matrix. -/
lemma dual_apply (μ ν : Fin 1 ⊕ Fin d) :
    dual Λ μ ν = η μ μ * Λ ν μ * η ν ν := by
  simp only [dual, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mul_diagonal,
    diagonal_mul, transpose_apply, diagonal_apply_eq]

/-- The components of the Minkowski dual of a matrix multiplied by the Minkowski matrix
  in terms of the original matrix. -/
lemma dual_apply_minkowskiMatrix (μ ν : Fin 1 ⊕ Fin d) :
    dual Λ μ ν * η ν ν = η μ μ * Λ ν μ := by
  rw [dual_apply, mul_assoc]
  simp

end minkowskiMatrix
