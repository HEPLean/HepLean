/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Basic
import Mathlib.Algebra.Lie.Classical
/-!

# The Minkowski Metric

This file introduces the Minkowski metric on spacetime in the mainly-minus signature.

We define the Minkowski metric as a bilinear map on the vector space
of Lorentz vectors in d dimensions.

-/

open Matrix

/-!

# The definition of the Minkowski Matrix

-/
/-- The `d.succ`-dimensional real of the form `diag(1, -1, -1, -1, ...)`. -/
def minkowskiMatrix {d : ℕ} : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  LieAlgebra.Orthogonal.indefiniteDiagonal (Fin 1) (Fin d) ℝ

namespace minkowskiMatrix

variable {d : ℕ}

/-- Notation for `minkowskiMatrix`. -/
scoped[minkowskiMatrix] notation "η" => minkowskiMatrix

@[simp]
lemma sq : @minkowskiMatrix d * minkowskiMatrix = 1 := by
  simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]
  ext1 i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [diagonal, of_apply, Sum.inl.injEq, Sum.elim_inl, mul_one]
    split
    · simp_all only [one_apply_eq]
    · simp_all only [ne_eq, Sum.inl.injEq, not_false_eq_true, one_apply_ne]
  · simp only [ne_eq, not_false_eq_true, diagonal_apply_ne, one_apply_ne]
  · simp only [ne_eq, not_false_eq_true, diagonal_apply_ne, one_apply_ne]
  · simp only [diagonal, of_apply, Sum.inr.injEq, Sum.elim_inr, mul_neg, mul_one, neg_neg]
    split
    · simp_all only [one_apply_eq]
    · simp_all only [ne_eq, Sum.inr.injEq, not_false_eq_true, one_apply_ne]

@[simp]
lemma eq_transpose : minkowskiMatrixᵀ = @minkowskiMatrix d := by
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_transpose]

@[simp]
lemma det_eq_neg_one_pow_d : (@minkowskiMatrix d).det = (- 1) ^ d := by
  simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]

lemma as_block : @minkowskiMatrix d = (
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0 (-1 : Matrix (Fin d) (Fin d) ℝ)) := by
  rw [minkowskiMatrix]
  simp [LieAlgebra.Orthogonal.indefiniteDiagonal]
  rw [← fromBlocks_diagonal]
  refine fromBlocks_inj.mpr ?_
  simp only [diagonal_one, true_and]
  funext i j
  rw [← diagonal_neg]
  rfl

end minkowskiMatrix

/-!

# The definition of the Minkowski Metric

-/

/-- Given a Lorentz vector `v` we define the the linear map `w ↦ v * η * w`. -/
@[simps!]
def minkowskiLinearForm {d : ℕ} (v : LorentzVector d) : LorentzVector d →ₗ[ℝ] ℝ where
  toFun w := v ⬝ᵥ (minkowskiMatrix *ᵥ w)
  map_add' y z := by
    noncomm_ring
    rw [mulVec_add, dotProduct_add]
  map_smul' c y := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [mulVec_smul, dotProduct_smul]
    rfl

/-- The Minkowski metric as a bilinear map. -/
def minkowskiMetric {d : ℕ} : LorentzVector d →ₗ[ℝ] LorentzVector d →ₗ[ℝ] ℝ where
  toFun v := minkowskiLinearForm v
  map_add' y z := by
    ext1 x
    simp only [minkowskiLinearForm_apply, LinearMap.add_apply]
    apply add_dotProduct
  map_smul' c y := by
    ext1 x
    simp only [minkowskiLinearForm_apply, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [smul_dotProduct]
    rfl

namespace minkowskiMetric

open minkowskiMatrix

open LorentzVector

variable {d : ℕ}
variable (v w : LorentzVector d)

/-- Notation for `minkowskiMetric`. -/
scoped[minkowskiMetric] notation "⟪" v "," w "⟫ₘ" => minkowskiMetric v w
/-!

# Equalitites involving the Minkowski metric

-/

/-- The Minkowski metric expressed as a sum. -/
lemma as_sum :
    ⟪v, w⟫ₘ = v.time * w.time - ∑ i, v.space i * w.space i := by
  simp only [minkowskiMetric, LinearMap.coe_mk, AddHom.coe_mk, minkowskiLinearForm_apply,
    dotProduct, LieAlgebra.Orthogonal.indefiniteDiagonal, mulVec_diagonal, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Sum.elim_inl, one_mul,
    Finset.sum_singleton, Sum.elim_inr, neg_mul, mul_neg, Finset.sum_neg_distrib, time, space,
    Function.comp_apply, minkowskiMatrix]
  ring

/-- The Minkowski metric expressed as a sum for a single vector. -/
lemma as_sum_self : ⟪v, v⟫ₘ = v.time ^ 2 - ‖v.space‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, as_sum]
  noncomm_ring

lemma eq_time_minus_inner_prod : ⟪v, w⟫ₘ = v.time * w.time - ⟪v.space, w.space⟫_ℝ := by
  rw [as_sum, @PiLp.inner_apply]
  noncomm_ring

lemma self_eq_time_minus_norm : ⟪v, v⟫ₘ = v.time ^ 2 - ‖v.space‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply, as_sum]
  noncomm_ring

/-- The Minkowski metric is symmetric. -/
lemma symm : ⟪v, w⟫ₘ = ⟪w, v⟫ₘ := by
  simp only [as_sum]
  ac_rfl

lemma time_sq_eq_metric_add_space : v.time ^ 2 = ⟪v, v⟫ₘ + ‖v.space‖ ^ 2 := by
  rw [self_eq_time_minus_norm]
  exact Eq.symm (sub_add_cancel (v.time ^ 2) (‖v.space‖ ^ 2))

/-!

# Minkowski metric and space reflections

-/

lemma right_spaceReflection : ⟪v, w.spaceReflection⟫ₘ = v.time * w.time + ⟪v.space, w.space⟫_ℝ := by
  rw [eq_time_minus_inner_prod, spaceReflection_space, spaceReflection_time]
  simp only [time, Fin.isValue, space, inner_neg_right, PiLp.inner_apply, Function.comp_apply,
    RCLike.inner_apply, conj_trivial, sub_neg_eq_add]

lemma self_spaceReflection_eq_zero_iff : ⟪v, v.spaceReflection⟫ₘ = 0 ↔ v = 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [right_spaceReflection] at h
    have h2 : 0 ≤ ⟪v.space, v.space⟫_ℝ := real_inner_self_nonneg
    have h3 : v.time * v.time = 0 := by linarith [mul_self_nonneg v.time]
    have h4 : ⟪v.space, v.space⟫_ℝ = 0 := by linarith
    simp only [time, Fin.isValue, mul_eq_zero, or_self] at h3
    rw [@inner_self_eq_zero] at h4
    funext i
    rcases i with i | i
    · fin_cases i
      exact h3
    · simpa using congrFun h4 i
  · rw [h]
    simp only [map_zero, LinearMap.zero_apply]
/-!

# Non degeneracy of the Minkowski metric

-/

/-- The metric tensor is non-degenerate. -/
lemma nondegenerate : (∀ w, ⟪w, v⟫ₘ = 0) ↔ v = 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · exact (self_spaceReflection_eq_zero_iff _ ).mp ((symm _ _).trans $ h v.spaceReflection)
  · simp [h]

/-!

# Inequalities involving the Minkowski metric

-/

lemma leq_time_sq : ⟪v, v⟫ₘ ≤ v.time ^ 2 := by
  rw [time_sq_eq_metric_add_space]
  exact (le_add_iff_nonneg_right _).mpr $ sq_nonneg ‖v.space‖

lemma ge_abs_inner_product : v.time * w.time - ‖⟪v.space, w.space⟫_ℝ‖ ≤ ⟪v, w⟫ₘ := by
  rw [eq_time_minus_inner_prod, sub_le_sub_iff_left]
  exact Real.le_norm_self ⟪v.space, w.space⟫_ℝ

lemma ge_sub_norm : v.time * w.time - ‖v.space‖ * ‖w.space‖ ≤ ⟪v, w⟫ₘ := by
  apply le_trans ?_ (ge_abs_inner_product v w)
  rw [sub_le_sub_iff_left]
  exact norm_inner_le_norm v.space w.space

/-!

# The Minkowski metric and matrices

-/
section matrices

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
  noncomm_ring [minkowskiMatrix.sq]
  noncomm_ring

@[simp]
lemma dual_dual : dual (dual Λ) = Λ := by
  simp only [dual, transpose_mul, transpose_transpose, eq_transpose]
  trans (η * η) * Λ * (η * η)
  noncomm_ring
  noncomm_ring [minkowskiMatrix.sq]

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

@[simp]
lemma dual_mulVec_right : ⟪x, (dual Λ) *ᵥ y⟫ₘ = ⟪Λ *ᵥ x, y⟫ₘ := by
  simp only [minkowskiMetric, LinearMap.coe_mk, AddHom.coe_mk, dual, minkowskiLinearForm_apply,
    mulVec_mulVec, ← mul_assoc, minkowskiMatrix.sq, one_mul, (vecMul_transpose Λ x).symm, ←
    dotProduct_mulVec]

@[simp]
lemma dual_mulVec_left : ⟪(dual Λ) *ᵥ x, y⟫ₘ = ⟪x, Λ *ᵥ y⟫ₘ := by
  rw [symm, dual_mulVec_right, symm]

lemma matrix_apply_eq_iff_sub : ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, Λ' *ᵥ w⟫ₘ ↔ ⟪v, (Λ - Λ') *ᵥ w⟫ₘ = 0 := by
  rw [← sub_eq_zero, ← LinearMap.map_sub, sub_mulVec]

lemma matrix_eq_iff_eq_forall' : (∀ v, Λ *ᵥ v= Λ' *ᵥ v) ↔ ∀ w v, ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, Λ' *ᵥ w⟫ₘ := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · intro w v
    rw [h w]
  · simp only [matrix_apply_eq_iff_sub] at h
    intro v
    refine sub_eq_zero.1 ?_
    have h1 := h v
    rw [nondegenerate] at h1
    simp [sub_mulVec] at h1
    exact h1

lemma matrix_eq_iff_eq_forall : Λ = Λ' ↔ ∀ w v, ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, Λ' *ᵥ w⟫ₘ := by
  rw [← matrix_eq_iff_eq_forall']
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [h]
    simp
  · rw [← (LinearMap.toMatrix stdBasis stdBasis).toEquiv.symm.apply_eq_iff_eq]
    ext1 x
    simp only [LinearEquiv.coe_toEquiv_symm, LinearMap.toMatrix_symm, EquivLike.coe_coe,
      toLin_apply, h, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton]

lemma matrix_eq_id_iff : Λ = 1 ↔ ∀ w v, ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, w⟫ₘ := by
  rw [matrix_eq_iff_eq_forall]
  simp

/-!

# The Minkowski metric and the standard basis

-/

@[simp]
lemma basis_left (μ : Fin 1 ⊕ Fin d) : ⟪e μ, v⟫ₘ = η μ μ * v μ := by
  rw [as_sum]
  rcases μ with μ | μ
  · fin_cases μ
    simp [stdBasis_apply, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]
  · simp [stdBasis_apply, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]

lemma on_timeVec : ⟪timeVec, @timeVec d⟫ₘ = 1 := by
  simp only [timeVec, Fin.isValue, basis_left, minkowskiMatrix,
    LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_apply_eq, Sum.elim_inl, stdBasis_apply,
    ↓reduceIte, mul_one]

lemma on_basis_mulVec (μ ν : Fin 1 ⊕ Fin d) : ⟪e μ, Λ *ᵥ e ν⟫ₘ = η μ μ * Λ μ ν := by
  simp [basis_left, mulVec, dotProduct, stdBasis_apply]

lemma on_basis (μ ν : Fin 1 ⊕ Fin d) : ⟪e μ, e ν⟫ₘ = η μ ν := by
  rw [basis_left, stdBasis_apply]
  by_cases h : μ = ν
  · simp [h]
  · simp [h, LieAlgebra.Orthogonal.indefiniteDiagonal, minkowskiMatrix]
    exact fun a => False.elim (h (id (Eq.symm a)))

lemma matrix_apply_stdBasis (ν μ : Fin 1 ⊕ Fin d):
    Λ ν μ = η ν ν * ⟪e ν, Λ *ᵥ e μ⟫ₘ := by
  rw [on_basis_mulVec, ← mul_assoc]
  have h1 : η ν ν * η ν ν = 1 := by
    simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal]
    rcases μ
    · rcases ν
      · simp_all only [Sum.elim_inl, mul_one]
      · simp_all only [Sum.elim_inr, mul_neg, mul_one, neg_neg]
    · rcases ν
      · simp_all only [Sum.elim_inl, mul_one]
      · simp_all only [Sum.elim_inr, mul_neg, mul_one, neg_neg]
  simp [h1]

end matrices
end minkowskiMetric
