/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.TensorProduct
/-!
# Spacetime Metric

This file introduces the metric on spacetime in the (+, -, -, -) signature.

-/

noncomputable section

namespace spaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorProduct

/-- The metric as a `4×4` real matrix. -/
def η : Matrix (Fin 4) (Fin 4) ℝ := Matrix.reindex finSumFinEquiv finSumFinEquiv
  $ LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 1) (Fin 3) ℝ

lemma η_block : η = Matrix.reindex finSumFinEquiv finSumFinEquiv (
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (-1 : Matrix (Fin 3) (Fin 3) ℝ)) := by
  rw [η]
  congr
  simp [LieAlgebra.Orthogonal.indefiniteDiagonal]
  rw [← @fromBlocks_diagonal]
  refine fromBlocks_inj.mpr ?_
  simp only [diagonal_one, true_and]
  funext i j
  fin_cases i <;> fin_cases j <;> simp

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
  all_goals simp [finSumFinEquiv, Fin.addCases, η, Fin.zero_eta, Matrix.cons_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.empty_val', Matrix.head_cons,
      Matrix.head_fin_const, Matrix.head_cons, Matrix.vecCons_const, Fin.mk_one, Fin.mk_one,
      vecHead, vecTail, Function.comp_apply]
  any_goals rfl
  all_goals split
  all_goals simp
  all_goals rfl

@[simp]
lemma η_off_diagonal {μ ν : Fin 4} (h : μ ≠ ν) : η μ ν = 0 := by
  fin_cases μ <;>
    fin_cases ν <;>
      simp_all [η_explicit, Fin.zero_eta, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_one,
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.empty_val', Matrix.head_cons,
      Matrix.head_fin_const, Matrix.head_cons, Matrix.vecCons_const, Fin.mk_one, Fin.mk_one,
      vecHead, vecTail, Function.comp_apply]

lemma η_symmetric (μ ν : Fin 4) : η μ ν = η ν μ := by
  by_cases h : μ = ν
  rw [h]
  rw [η_off_diagonal h]
  refine (η_off_diagonal ?_).symm
  exact fun a => h (id a.symm)

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
  fin_cases μ
    <;> simp [η_explicit]

lemma η_mulVec (x : spaceTime) : η *ᵥ x = ![x 0, -x 1, -x 2, -x 3] := by
  rw [explicit x, η_explicit]
  funext i
  fin_cases i <;>
  simp [vecHead, vecTail]

/-- Given a point in spaceTime `x` the linear map `y → x ⬝ᵥ (η *ᵥ y)`. -/
@[simps!]
def linearMapForSpaceTime (x : spaceTime) : spaceTime →ₗ[ℝ] ℝ where
  toFun y := x ⬝ᵥ (η *ᵥ y)
  map_add' y z := by
    simp only
    rw [mulVec_add, dotProduct_add]
  map_smul' c y := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [mulVec_smul, dotProduct_smul]
    rfl

/-- The metric as a bilinear map from `spaceTime` to `ℝ`. -/
def ηLin : LinearMap.BilinForm ℝ spaceTime where
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

lemma ηLin_expand (x y : spaceTime) : ηLin x y = x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 := by
  rw [ηLin]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, linearMapForSpaceTime_apply, Fin.isValue]
  erw [η_mulVec]
  nth_rewrite 1 [explicit x]
  simp only [dotProduct, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.sum_univ_four,
    cons_val_zero, cons_val_one, head_cons, mul_neg, cons_val_two, tail_cons, cons_val_three]
  ring

lemma ηLin_expand_self (x : spaceTime) : ηLin x x = x 0 ^ 2 - ‖x.space‖ ^ 2 := by
  rw [← @real_inner_self_eq_norm_sq, @PiLp.inner_apply, Fin.sum_univ_three, ηLin_expand]
  simp only [Fin.isValue, space, cons_val_zero, RCLike.inner_apply, conj_trivial, cons_val_one,
    head_cons, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons]
  ring

lemma time_elm_sq_of_ηLin (x : spaceTime) : x 0 ^ 2 = ηLin x x + ‖x.space‖ ^ 2 := by
  rw [ηLin_expand_self]
  ring

lemma ηLin_leq_time_sq (x : spaceTime) : ηLin x x ≤ x 0 ^ 2 := by
  rw [time_elm_sq_of_ηLin]
  apply (le_add_iff_nonneg_right _).mpr $ sq_nonneg ‖x.space‖

lemma ηLin_space_inner_product (x y : spaceTime) :
    ηLin x y = x 0 * y 0 - ⟪x.space, y.space⟫_ℝ  := by
  rw [ηLin_expand, @PiLp.inner_apply, Fin.sum_univ_three]
  simp only [Fin.isValue, space, cons_val_zero, RCLike.inner_apply, conj_trivial, cons_val_one,
    head_cons, cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons]
  ring

lemma ηLin_ge_abs_inner_product (x y : spaceTime) :
    x 0 * y 0 - ‖⟪x.space, y.space⟫_ℝ‖ ≤ (ηLin x y)  := by
  rw [ηLin_space_inner_product, sub_le_sub_iff_left]
  exact Real.le_norm_self ⟪x.space, y.space⟫_ℝ

lemma ηLin_ge_sub_norm (x y : spaceTime) :
    x 0 * y 0 - ‖x.space‖ * ‖y.space‖ ≤ (ηLin x y)  := by
  apply le_trans ?_ (ηLin_ge_abs_inner_product x y)
  rw [sub_le_sub_iff_left]
  exact norm_inner_le_norm x.space y.space


lemma ηLin_symm (x y : spaceTime) : ηLin x y = ηLin y x := by
  rw [ηLin_expand, ηLin_expand]
  ring

lemma ηLin_stdBasis_apply (μ : Fin 4) (x : spaceTime) : ηLin (stdBasis μ) x = η μ μ * x μ := by
  rw [ηLin_expand]
  fin_cases μ
   <;> simp [stdBasis_0, stdBasis_1, stdBasis_2, stdBasis_3, η_explicit]


lemma ηLin_η_stdBasis (μ ν : Fin 4) : ηLin (stdBasis μ) (stdBasis ν) = η μ ν := by
  rw [ηLin_stdBasis_apply]
  by_cases h : μ = ν
  rw [stdBasis_apply]
  subst h
  simp only [↓reduceIte, mul_one]
  rw [stdBasis_not_eq, η_off_diagonal h]
  simp only [mul_zero]
  exact fun a => h (id a.symm)

lemma ηLin_mulVec_left (x y : spaceTime) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    ηLin (Λ *ᵥ x) y = ηLin x ((η * Λᵀ * η) *ᵥ y) := by
  simp only [ηLin, LinearMap.coe_mk, AddHom.coe_mk, linearMapForSpaceTime_apply, mulVec_mulVec]
  rw [(vecMul_transpose Λ x).symm, ← dotProduct_mulVec, mulVec_mulVec]
  rw [← mul_assoc, ← mul_assoc, η_sq, one_mul]

lemma ηLin_mulVec_right (x y : spaceTime) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
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
    Λ = 1 ↔ ∀ (x y : spaceTime), ηLin x y = ηLin x (Λ *ᵥ y) := by
  apply Iff.intro
  intro h
  subst h
  simp only [ηLin, one_mulVec, implies_true]
  intro h
  funext μ ν
  have h1 := h (stdBasis μ) (stdBasis ν)
  rw [ηLin_matrix_stdBasis, ηLin_η_stdBasis] at h1
  fin_cases μ <;> fin_cases ν <;>
    simp_all [η_explicit, Fin.zero_eta, Matrix.cons_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_one,
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.empty_val', Matrix.head_cons,
      Matrix.head_fin_const, Matrix.head_cons, Matrix.vecCons_const, Fin.mk_one, Fin.mk_one,
      vecHead, vecTail, Function.comp_apply]

/-- The metric as a quadratic form on `spaceTime`. -/
def quadraticForm : QuadraticForm ℝ spaceTime := ηLin.toQuadraticForm




end spaceTime

end
