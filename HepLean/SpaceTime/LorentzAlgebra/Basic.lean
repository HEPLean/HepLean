/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Basic
import HepLean.SpaceTime.Metric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!
# The Lorentz Algebra


-/


namespace spaceTime
open Matrix
open TensorProduct

/-- The Lorentz algebra as a subalgebra of `Matrix (Fin 4) (Fin 4) ℝ`.  -/
def lorentzAlgebra : LieSubalgebra ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  LieSubalgebra.map (Matrix.reindexLieEquiv (@finSumFinEquiv 1 3)).toLieHom
  (LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ)


namespace lorentzAlgebra

lemma transpose_eta (A : lorentzAlgebra) :  A.1ᵀ * η  = - η * A.1  := by
  have h := A.2
  simp [lorentzAlgebra] at h
  obtain ⟨B, hB1, hB2⟩ := h
  simp [LieAlgebra.Orthogonal.so', IsSkewAdjoint, IsAdjointPair] at hB1
  apply (Equiv.apply_eq_iff_eq
    (Matrix.reindexAlgEquiv ℝ (@finSumFinEquiv 1 3).symm).toEquiv).mp
  erw [Matrix.reindexAlgEquiv_mul]
  simp only [Nat.reduceAdd, reindexAlgEquiv_apply, Equiv.symm_symm, AlgEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, map_neg, _root_.map_mul]
  rw [← Matrix.transpose_reindex]
  have h1 : (reindex finSumFinEquiv.symm finSumFinEquiv.symm) A = B :=
    (Equiv.apply_eq_iff_eq_symm_apply (reindex finSumFinEquiv.symm finSumFinEquiv.symm)).mpr
    (id hB2.symm)
  rw [h1]
  erw [η_reindex]
  simpa using hB1

lemma mem_of_transpose_eta_eq_eta_mul_self {A : Matrix (Fin 4) (Fin 4) ℝ}
    (h :  Aᵀ * η  = - η * A) : A ∈ lorentzAlgebra := by
  simp [lorentzAlgebra]
  use (Matrix.reindexLieEquiv (@finSumFinEquiv 1 3)).symm A
  apply And.intro
  swap
  change (reindexLieEquiv finSumFinEquiv) _ = _
  simp only [Nat.reduceAdd, reindexLieEquiv_symm, reindexLieEquiv_apply, reindex_apply,
    Equiv.symm_symm, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  simp only [Nat.reduceAdd, reindexLieEquiv_symm, reindexLieEquiv_apply,
    LieAlgebra.Orthogonal.so', mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule, IsSkewAdjoint, IsAdjointPair, mul_neg]
  have h1 :=  (Equiv.apply_eq_iff_eq
    (Matrix.reindexAlgEquiv ℝ (@finSumFinEquiv 1 3).symm).toEquiv).mpr h
  erw [Matrix.reindexAlgEquiv_mul] at h1
  simp only [Nat.reduceAdd, reindexAlgEquiv_apply, Equiv.symm_symm, AlgEquiv.toEquiv_eq_coe,
    EquivLike.coe_coe, map_neg, _root_.map_mul] at h1
  erw [η_reindex] at h1
  simpa using h1


lemma mem_iff {A : Matrix (Fin 4) (Fin 4) ℝ} : A ∈ lorentzAlgebra ↔
    Aᵀ * η  = - η * A := by
  apply Iff.intro
  · intro h
    exact transpose_eta ⟨A, h⟩
  · intro h
    exact mem_of_transpose_eta_eq_eta_mul_self h

lemma mem_iff'  (A : Matrix (Fin 4) (Fin 4) ℝ) : A ∈ lorentzAlgebra ↔ A  = - η * Aᵀ * η := by
  apply Iff.intro
  intro h
  rw [mul_assoc, mem_iff.mp h]
  simp only [neg_mul, mul_neg, ← mul_assoc, η_sq, one_mul, neg_neg]
  intro h
  rw [mem_iff]
  nth_rewrite 2 [h]
  simp [← mul_assoc, η_sq]


end lorentzAlgebra

@[simps!]
instance spaceTimeAsLieRingModule : LieRingModule lorentzAlgebra spaceTime where
  bracket Λ x :=  Λ.1.mulVec  x
  add_lie Λ1 Λ2 x := by
    simp [add_mulVec]
  lie_add Λ x1 x2 := by
    simp only
    exact mulVec_add _ _ _
  leibniz_lie Λ1 Λ2 x := by
    simp [mulVec_add, Bracket.bracket, sub_mulVec]

@[simps!]
instance spaceTimeAsLieModule : LieModule ℝ lorentzAlgebra spaceTime where
  smul_lie r Λ x  := by
    simp [Bracket.bracket, smul_mulVec_assoc]
  lie_smul r Λ x := by
    simp [Bracket.bracket]
    rw [mulVec_smul]

@[simps!]
local instance : LieRingModule lorentzAlgebra ℝ where
  bracket _ _ := 0
  add_lie _ _ _ := by simp
  lie_add _ _ _ := by simp
  leibniz_lie _ _ _ := by simp

@[simps!]
local instance : LieModule ℝ lorentzAlgebra ℝ where
  smul_lie _ _ _ := by simp [Bracket.bracket]
  lie_smul _ _ _ := by simp [Bracket.bracket]





end spaceTime
