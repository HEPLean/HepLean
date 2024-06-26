/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Basic
import Mathlib.Algebra.Lie.Classical
import Mathlib.LinearAlgebra.QuadraticForm.Basic
/-!
# Spacetime Metric

This file introduces the metric on spacetime in the (+, -, -, -) signature.

-/

noncomputable section

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorProduct

/-- The metric as a `4×4` real matrix. -/
def η : Matrix (Fin 4) (Fin 4) ℝ := Matrix.reindex finSumFinEquiv finSumFinEquiv
  $ LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 1) (Fin 3) ℝ

/-- The metric with lower indices. -/
notation "η_[" μ "]_[" ν "]" => η μ ν

/-- The inverse of `η`. Used for notation. -/
def ηInv : Matrix (Fin 4) (Fin 4) ℝ := η

/-- The metric with upper indices. -/
notation "η^[" μ "]^[" ν "]" => ηInv μ ν

/-- A matrix with one lower and one upper index. -/
notation "["Λ"]^[" μ "]_[" ν "]" => (Λ : Matrix (Fin 4) (Fin 4) ℝ) μ ν

/-- A matrix with both lower indices. -/
notation "["Λ"]_[" μ "]_[" ν "]" => ∑ ρ, η_[μ]_[ρ] * [Λ]^[ρ]_[ν]

/--  `η` with $η^μ_ν$ indices. This is equivalent to the identity. This is used for notation. -/
def ηUpDown : Matrix (Fin 4) (Fin 4) ℝ := 1

/-- The metric with one lower and one upper index. -/
notation "η^[" μ "]_[" ν "]" => ηUpDown μ ν


lemma η_block : η = Matrix.reindex finSumFinEquiv finSumFinEquiv (
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (-1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  rw [η]
  congr
  simp [LieAlgebra.Orthogonal.indefiniteDiagonal]
  rw [← fromBlocks_diagonal]
  refine fromBlocks_inj.mpr ?_
  simp only [diagonal_one, true_and]
  funext i j
  rw [← diagonal_neg]
  rfl

lemma η_reindex : (Matrix.reindex finSumFinEquiv finSumFinEquiv).symm η =
    LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 1) (Fin 3) ℝ :=
  (Equiv.symm_apply_eq (reindex finSumFinEquiv finSumFinEquiv)).mpr rfl

lemma η_explicit : η = !![(1 : ℝ), 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  rw [η_block]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
    <;> simp_all only [Fin.zero_eta, reindex_apply, submatrix_apply]
  any_goals rfl
  all_goals simp [finSumFinEquiv, Fin.addCases, η, vecHead, vecTail]
  any_goals rfl
  all_goals split
  all_goals simp
  all_goals rfl

@[simp]
lemma η_off_diagonal {μ ν : Fin 4} (h : μ ≠ ν) : η μ ν = 0 := by
  fin_cases μ <;>
    fin_cases ν <;>
      simp_all [η_explicit, Fin.mk_one, Fin.mk_one, vecHead, vecTail]

lemma η_symmetric (μ ν : Fin 4) : η μ ν = η ν μ := by
  by_cases h : μ = ν
  rw [h]
  rw [η_off_diagonal h]
  exact Eq.symm (η_off_diagonal fun a => h (id (Eq.symm a)))

@[simp]
lemma η_transpose : η.transpose = η := by
  funext μ ν
  rw [transpose_apply, η_symmetric]

@[simp]
lemma det_η : η.det = - 1 := by
  simp [η_explicit, det_succ_row_zero, Fin.sum_univ_succ]

@[simp]
lemma η_sq : η * η = 1 := by
  funext μ ν
  fin_cases μ <;> fin_cases ν <;>
     simp [η_explicit, vecHead, vecTail]

lemma η_diag_mul_self (μ : Fin 4) : η μ μ * η μ μ  = 1 := by
  fin_cases μ <;> simp [η_explicit]

lemma η_mulVec (x : SpaceTime) : η *ᵥ x = ![x 0, -x 1, -x 2, -x 3] := by
  rw [explicit x, η_explicit]
  funext i
  fin_cases i <;>
  simp [vecHead, vecTail]

lemma η_as_diagonal : η = diagonal ![1, -1, -1, -1] := by
  rw [η_explicit]
  apply Matrix.ext
  intro μ ν
  fin_cases μ <;> fin_cases ν <;> rfl

lemma η_mul (Λ : Matrix (Fin 4) (Fin 4) ℝ) (μ ρ : Fin 4) :
    [η * Λ]^[μ]_[ρ] = [η]^[μ]_[μ] * [Λ]^[μ]_[ρ] := by
  rw  [η_as_diagonal, @diagonal_mul, diagonal_apply_eq ![1, -1, -1, -1] μ]

lemma mul_η (Λ : Matrix (Fin 4) (Fin 4) ℝ) (μ ρ : Fin 4) :
    [Λ * η]^[μ]_[ρ] =  [Λ]^[μ]_[ρ] * [η]^[ρ]_[ρ] := by
  rw [η_as_diagonal, @mul_diagonal, diagonal_apply_eq ![1, -1, -1, -1] ρ]

lemma η_mul_self (μ ν : Fin 4) : η^[ν]_[μ] * η_[ν]_[ν] = η_[μ]_[ν] := by
  fin_cases μ <;> fin_cases ν <;> simp [ηUpDown]

lemma η_contract_self (μ ν : Fin 4) : ∑ x, (η^[x]_[μ] * η_[x]_[ν]) = η_[μ]_[ν] := by
  rw [Fin.sum_univ_four]
  fin_cases μ <;> fin_cases ν <;> simp [ηUpDown]

lemma η_contract_self' (μ ν : Fin 4) : ∑ x, (η^[x]_[μ] * η_[ν]_[x]) = η_[ν]_[μ] := by
  rw [Fin.sum_univ_four]
  fin_cases μ <;> fin_cases ν <;> simp [ηUpDown]



/-- Given a point in spaceTime `x` the linear map `y → x ⬝ᵥ (η *ᵥ y)`. -/
@[simps!]
def linearMapForSpaceTime (x : SpaceTime) : SpaceTime →ₗ[ℝ] ℝ where
  toFun y := x ⬝ᵥ (η *ᵥ y)
  map_add' y z := by
    simp only
    rw [mulVec_add, dotProduct_add]
  map_smul' c y := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [mulVec_smul, dotProduct_smul]
    rfl

/-- The metric as a bilinear map from `spaceTime` to `ℝ`. -/
def ηLin : LinearMap.BilinForm ℝ SpaceTime where
  toFun x := linearMapForSpaceTime x
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp only [linearMapForSpaceTime_apply, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    simp only [linearMapForSpaceTime_apply, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [smul_dotProduct]
    rfl

lemma ηLin_expand (x y : SpaceTime) : ηLin x y = x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 := by
  rw [ηLin]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, linearMapForSpaceTime_apply, Fin.isValue]
  erw [η_mulVec]
  nth_rewrite 1 [explicit x]
  simp only [dotProduct, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.sum_univ_four,
    cons_val_zero, cons_val_one, head_cons, mul_neg, cons_val_two, tail_cons, cons_val_three]
  ring

lemma ηLin_expand_self (x : SpaceTime) : ηLin x x = x 0 ^ 2 - ‖x.space‖ ^ 2 := by
  rw [← @real_inner_self_eq_norm_sq, @PiLp.inner_apply, Fin.sum_univ_three, ηLin_expand]
  noncomm_ring

lemma time_elm_sq_of_ηLin (x : SpaceTime) : x 0 ^ 2 = ηLin x x + ‖x.space‖ ^ 2 := by
  rw [ηLin_expand_self]
  ring

lemma ηLin_leq_time_sq (x : SpaceTime) : ηLin x x ≤ x 0 ^ 2 := by
  rw [time_elm_sq_of_ηLin]
  exact (le_add_iff_nonneg_right _).mpr $ sq_nonneg ‖x.space‖

lemma ηLin_space_inner_product (x y : SpaceTime) :
    ηLin x y = x 0 * y 0 - ⟪x.space, y.space⟫_ℝ  := by
  rw [ηLin_expand, @PiLp.inner_apply, Fin.sum_univ_three]
  noncomm_ring

lemma ηLin_ge_abs_inner_product (x y : SpaceTime) :
    x 0 * y 0 - ‖⟪x.space, y.space⟫_ℝ‖ ≤ (ηLin x y)  := by
  rw [ηLin_space_inner_product, sub_le_sub_iff_left]
  exact Real.le_norm_self ⟪x.space, y.space⟫_ℝ

lemma ηLin_ge_sub_norm (x y : SpaceTime) :
    x 0 * y 0 - ‖x.space‖ * ‖y.space‖ ≤ (ηLin x y)  := by
  apply le_trans ?_ (ηLin_ge_abs_inner_product x y)
  rw [sub_le_sub_iff_left]
  exact norm_inner_le_norm x.space y.space


lemma ηLin_symm (x y : SpaceTime) : ηLin x y = ηLin y x := by
  rw [ηLin_expand, ηLin_expand]
  ring

lemma ηLin_stdBasis_apply (μ : Fin 4) (x : SpaceTime) : ηLin (stdBasis μ) x = η μ μ * x μ := by
  rw [ηLin_expand]
  fin_cases μ
   <;> simp [stdBasis_0, stdBasis_1, stdBasis_2, stdBasis_3, η_explicit]


lemma ηLin_η_stdBasis (μ ν : Fin 4) : ηLin (stdBasis μ) (stdBasis ν) = η μ ν := by
  rw [ηLin_stdBasis_apply]
  by_cases h : μ = ν
  · rw [stdBasis_apply]
    subst h
    simp
  · rw [stdBasis_not_eq, η_off_diagonal h]
    exact CommMonoidWithZero.mul_zero η_[μ]_[μ]
    exact fun a ↦ h (id a.symm)

set_option maxHeartbeats 0
lemma ηLin_mulVec_left (x y : SpaceTime) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    ηLin (Λ *ᵥ x) y = ηLin x ((η * Λᵀ * η) *ᵥ y) := by
  simp [ηLin, LinearMap.coe_mk, AddHom.coe_mk, linearMapForSpaceTime_apply,
    mulVec_mulVec, (vecMul_transpose Λ x).symm, ← dotProduct_mulVec, mulVec_mulVec,
    ← mul_assoc, ← mul_assoc, η_sq, one_mul]

lemma ηLin_mulVec_right (x y : SpaceTime) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    ηLin x (Λ *ᵥ y) = ηLin ((η * Λᵀ * η) *ᵥ x) y := by
  rw [ηLin_symm, ηLin_symm ((η * Λᵀ * η) *ᵥ x) _ ]
  exact ηLin_mulVec_left y x Λ

lemma ηLin_matrix_stdBasis (μ ν : Fin 4) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    ηLin (stdBasis ν) (Λ *ᵥ stdBasis μ)  = η ν ν * Λ ν μ := by
  rw [ηLin_stdBasis_apply, stdBasis_mulVec]

lemma ηLin_matrix_stdBasis' (μ ν : Fin 4) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    Λ ν μ  = η ν ν *  ηLin (stdBasis ν) (Λ *ᵥ stdBasis μ)  := by
  rw [ηLin_matrix_stdBasis, ← mul_assoc, η_diag_mul_self, one_mul]

lemma ηLin_matrix_eq_identity_iff (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    Λ = 1 ↔ ∀ (x y : SpaceTime), ηLin x y = ηLin x (Λ *ᵥ y) := by
  apply Iff.intro
  · intro h
    subst h
    simp only [ηLin, one_mulVec, implies_true]
  · intro h
    funext μ ν
    have h1 := h (stdBasis μ) (stdBasis ν)
    rw [ηLin_matrix_stdBasis, ηLin_η_stdBasis] at h1
    fin_cases μ <;> fin_cases ν <;>
    simp_all [η_explicit,  Fin.mk_one, Fin.mk_one, vecHead, vecTail]

/-- The metric as a quadratic form on `spaceTime`. -/
def quadraticForm : QuadraticForm ℝ SpaceTime := ηLin.toQuadraticForm

end SpaceTime

end
