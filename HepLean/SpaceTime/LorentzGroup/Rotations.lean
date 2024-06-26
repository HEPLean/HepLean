/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup.Basic
import HepLean.GroupTheory.SO3.Basic
import Mathlib.Topology.Constructions
/-!
# Rotations

-/
noncomputable section
namespace SpaceTime

namespace lorentzGroup
open GroupTheory

/-- Given a element of `SO(3)` the matrix corresponding to a space-time rotation. -/
@[simp]
def SO3ToMatrix (A : SO(3)) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 A.1)

lemma SO3ToMatrix_PreservesηLin (A : SO(3)) : PreservesηLin $ SO3ToMatrix A  := by
  rw [PreservesηLin.iff_matrix]
  simp only [η_block, Nat.reduceAdd, Matrix.reindex_apply, SO3ToMatrix, Matrix.transpose_submatrix,
    Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, mul_one, Matrix.mul_zero, add_zero,
    Matrix.zero_mul, Matrix.mul_one, neg_mul, one_mul, zero_add, Matrix.mul_neg, neg_zero, mul_neg,
    neg_neg, Matrix.mul_eq_one_comm.mpr A.2.2, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

lemma SO3ToMatrix_injective : Function.Injective SO3ToMatrix := by
  intro A B h
  erw [Equiv.apply_eq_iff_eq] at h
  have h1 := congrArg Matrix.toBlocks₂₂ h
  rw [Matrix.toBlocks_fromBlocks₂₂, Matrix.toBlocks_fromBlocks₂₂] at h1
  apply Subtype.eq
  exact h1

/-- Given a element of `SO(3)` the element of the Lorentz group corresponding to a
space-time rotation. -/
def SO3ToLorentz : SO(3) →* 𝓛 where
  toFun A := ⟨SO3ToMatrix A, SO3ToMatrix_PreservesηLin A⟩
  map_one' := by
    apply Subtype.eq
    simp only [SO3ToMatrix, Nat.reduceAdd, Matrix.reindex_apply, lorentzGroupIsGroup_one_coe]
    erw [Matrix.fromBlocks_one]
    exact Matrix.submatrix_one_equiv finSumFinEquiv.symm
  map_mul' A B := by
    apply Subtype.eq
    simp [Matrix.fromBlocks_multiply]


end lorentzGroup


end SpaceTime
end
