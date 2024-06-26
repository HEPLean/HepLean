/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Basic
import HepLean.SpaceTime.Metric
import Mathlib.Algebra.Lie.Classical
/-!
# The Lorentz Algebra

We define

- Define `lorentzAlgebra` via `LieAlgebra.Orthogonal.so'` as a subalgebra of
  `Matrix (Fin 4) (Fin 4) ℝ`.
- In `mem_iff` prove that a matrix is in the Lorentz algebra if and only if it satisfies the
  condition `Aᵀ * η  = - η * A`.

-/


namespace SpaceTime
open Matrix
open TensorProduct

/-- The Lorentz algebra as a subalgebra of `Matrix (Fin 4) (Fin 4) ℝ`.  -/
def lorentzAlgebra : LieSubalgebra ℝ (Matrix (Fin 4) (Fin 4) ℝ) :=
  LieSubalgebra.map (Matrix.reindexLieEquiv (@finSumFinEquiv 1 3)).toLieHom
  (LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ)

namespace lorentzAlgebra

lemma transpose_eta (A : lorentzAlgebra) :  A.1ᵀ * η  = - η * A.1  := by
  obtain ⟨B, hB1, hB2⟩ := A.2
  apply (Equiv.apply_eq_iff_eq
    (Matrix.reindexAlgEquiv ℝ (@finSumFinEquiv 1 3).symm).toEquiv).mp
  simp only [Nat.reduceAdd, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe, _root_.map_mul,
    reindexAlgEquiv_apply, ← transpose_reindex, map_neg]
  rw [(Equiv.apply_eq_iff_eq_symm_apply (reindex finSumFinEquiv.symm finSumFinEquiv.symm)).mpr
    hB2.symm]
  erw [η_reindex]
  simpa [LieAlgebra.Orthogonal.so', IsSkewAdjoint, IsAdjointPair] using hB1

lemma mem_of_transpose_eta_eq_eta_mul_self {A : Matrix (Fin 4) (Fin 4) ℝ}
    (h :  Aᵀ * η  = - η * A) : A ∈ lorentzAlgebra := by
  simp only [lorentzAlgebra, Nat.reduceAdd, LieSubalgebra.mem_map]
  use (Matrix.reindexLieEquiv (@finSumFinEquiv 1 3)).symm A
  apply And.intro
  · have h1 := (Equiv.apply_eq_iff_eq
      (Matrix.reindexAlgEquiv ℝ (@finSumFinEquiv 1 3).symm).toEquiv).mpr h
    erw [Matrix.reindexAlgEquiv_mul] at h1
    simp only [Nat.reduceAdd, reindexAlgEquiv_apply, Equiv.symm_symm, AlgEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, map_neg, _root_.map_mul] at h1
    erw [η_reindex] at h1
    simpa  [Nat.reduceAdd, reindexLieEquiv_symm, reindexLieEquiv_apply,
      LieAlgebra.Orthogonal.so', mem_skewAdjointMatricesLieSubalgebra,
      mem_skewAdjointMatricesSubmodule, IsSkewAdjoint, IsAdjointPair, mul_neg] using h1
  · exact LieEquiv.apply_symm_apply (reindexLieEquiv finSumFinEquiv) _


lemma mem_iff {A : Matrix (Fin 4) (Fin 4) ℝ} : A ∈ lorentzAlgebra ↔ Aᵀ * η  = - η * A :=
  Iff.intro (fun h => transpose_eta ⟨A, h⟩) (fun h => mem_of_transpose_eta_eq_eta_mul_self h)

lemma mem_iff'  (A : Matrix (Fin 4) (Fin 4) ℝ) : A ∈ lorentzAlgebra ↔ A  = - η * Aᵀ * η := by
  apply Iff.intro
  intro h
  simp_rw [mul_assoc, mem_iff.mp h, neg_mul, mul_neg, ← mul_assoc, η_sq, one_mul, neg_neg]
  intro h
  rw [mem_iff]
  nth_rewrite 2 [h]
  simp [← mul_assoc, η_sq]

lemma diag_comp (Λ : lorentzAlgebra) (μ : Fin 4) : Λ.1 μ μ = 0 := by
  have h := congrArg (fun M ↦ M μ μ) $ mem_iff.mp Λ.2
  simp at h
  fin_cases μ <;>
    rw [η_mul, mul_η, η_explicit] at h
    <;> simpa using h

lemma time_comps (Λ : lorentzAlgebra) (i : Fin 3) : Λ.1 i.succ 0 = Λ.1 0 i.succ := by
  have h := congrArg (fun M ↦ M 0 i.succ) $ mem_iff.mp Λ.2
  simp at h
  fin_cases i <;>
    rw [η_mul, mul_η, η_explicit] at h <;>
    simpa using h

lemma space_comps (Λ : lorentzAlgebra) (i j : Fin 3) :
    Λ.1 i.succ j.succ = - Λ.1 j.succ i.succ := by
  have h := congrArg (fun M ↦ M i.succ j.succ) $ mem_iff.mp Λ.2
  simp at h
  fin_cases i <;> fin_cases j <;>
    rw [η_mul, mul_η, η_explicit] at h <;>
    simpa using h.symm


end lorentzAlgebra

@[simps!]
instance spaceTimeAsLieRingModule : LieRingModule lorentzAlgebra SpaceTime where
  bracket Λ x :=  Λ.1.mulVec  x
  add_lie Λ1 Λ2 x := by
    simp [add_mulVec]
  lie_add Λ x1 x2 := by
    simp only
    exact mulVec_add _ _ _
  leibniz_lie Λ1 Λ2 x := by
    simp [mulVec_add, Bracket.bracket, sub_mulVec]

@[simps!]
instance spaceTimeAsLieModule : LieModule ℝ lorentzAlgebra SpaceTime where
  smul_lie r Λ x  := by
    simp [Bracket.bracket, smul_mulVec_assoc]
  lie_smul r Λ x := by
    simp [Bracket.bracket]
    rw [mulVec_smul]


end SpaceTime
