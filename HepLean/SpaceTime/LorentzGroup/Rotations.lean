/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup.Orthochronous
import HepLean.SpaceTime.LorentzGroup.Proper
import HepLean.GroupTheory.SO3.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Topology.Constructions
/-!
# Rotations

-/
noncomputable section
namespace spaceTime

namespace lorentzGroup
open GroupTheory

@[simp]
def SO3ToMatrix (A : SO(3)) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 0 0 A.1)

@[simp]
lemma SO3ToMatrix_det (A : SO(3)) : (SO3ToMatrix A).det = 1 := by
  simp only [SO3ToMatrix, Nat.reduceAdd, Matrix.reindex_apply, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Fin.default_eq_zero, Fin.isValue,
    Matrix.one_apply_eq, A.2, mul_one]

lemma SO3ToMatrix_lorentz (A : SO(3)) : η * (SO3ToMatrix A).transpose * η  * SO3ToMatrix A = 1 := by
  simp only [η_block, Nat.reduceAdd, Matrix.reindex_apply, SO3ToMatrix, Matrix.transpose_submatrix,
    Matrix.fromBlocks_transpose, Matrix.transpose_one, Matrix.transpose_zero,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, mul_one, Matrix.mul_zero, add_zero,
    Matrix.zero_mul, Matrix.mul_one, neg_mul, one_mul, zero_add, Matrix.mul_neg, neg_zero, mul_neg,
    neg_neg, Matrix.mul_eq_one_comm.mpr A.2.2, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]


end lorentzGroup


end spaceTime
end
