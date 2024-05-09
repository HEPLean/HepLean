/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.Basic
import HepLean.StandardModel.Representations
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.Polyrith
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Geometry.Manifold.ContMDiff.Product
import Mathlib.Algebra.QuadraticDiscriminant
/-!
# The Higgs vector space

This file defines the target vector space of the Higgs boson, the potential on it,
and the representation of the SM gauge group acting on it.

This file is a import of `SM.HiggsBoson.Basic`.

## References

- We use conventions given in: https://pdg.lbl.gov/2019/reviews/rpp2019-rev-higgs-boson.pdf

-/
universe v u
namespace StandardModel
noncomputable section

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The complex vector space in which the Higgs field takes values. -/
abbrev higgsVec := EuclideanSpace ℂ (Fin 2)

section higgsVec

/-- The continous linear map from the vector space `higgsVec` to `(Fin 2 → ℂ)` acheived by
casting vectors. -/
def higgsVecToFin2ℂ : higgsVec →L[ℝ] (Fin 2 → ℂ) where
  toFun x := x
  map_add' x y := by
    simp
  map_smul' a x := by
    simp

lemma smooth_higgsVecToFin2ℂ : Smooth 𝓘(ℝ, higgsVec) 𝓘(ℝ, Fin 2 → ℂ) higgsVecToFin2ℂ :=
  ContinuousLinearMap.smooth higgsVecToFin2ℂ

namespace higgsVec

@[simps!]
noncomputable def higgsRepUnitary : guageGroup →* unitaryGroup (Fin 2) ℂ where
  toFun g := repU1 g.2.2 * fundamentalSU2 g.2.1
  map_mul'  := by
    intro ⟨_, a2, a3⟩ ⟨_, b2, b3⟩
    change repU1 (a3 * b3) *  fundamentalSU2 (a2 * b2) = _
    rw [repU1.map_mul, fundamentalSU2.map_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (repU1 b3) _ _, repU1_fundamentalSU2_commute]
    repeat rw [mul_assoc]
  map_one' := by
    simp only [Prod.snd_one, _root_.map_one, Prod.fst_one, mul_one]

/-- An orthonomral basis of higgsVec. -/
noncomputable def orthonormBasis : OrthonormalBasis (Fin 2) ℂ higgsVec :=
  EuclideanSpace.basisFun (Fin 2) ℂ

/-- Takes in a `2×2`-matrix and returns a linear map of `higgsVec`. -/
@[simps!]
noncomputable def matrixToLin : Matrix (Fin 2) (Fin 2) ℂ →* (higgsVec →L[ℂ] higgsVec) where
  toFun g := LinearMap.toContinuousLinearMap
    $ Matrix.toLin orthonormBasis.toBasis orthonormBasis.toBasis g
  map_mul' g h := ContinuousLinearMap.coe_inj.mp $
    Matrix.toLin_mul orthonormBasis.toBasis orthonormBasis.toBasis orthonormBasis.toBasis g h
  map_one' := ContinuousLinearMap.coe_inj.mp $ Matrix.toLin_one orthonormBasis.toBasis

lemma matrixToLin_star (g : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixToLin (star g) = star (matrixToLin g) :=
  ContinuousLinearMap.coe_inj.mp $ Matrix.toLin_conjTranspose orthonormBasis orthonormBasis g

lemma matrixToLin_unitary (g : unitaryGroup (Fin 2) ℂ) :
    matrixToLin g ∈ unitary (higgsVec →L[ℂ] higgsVec) := by
  rw [@unitary.mem_iff, ← matrixToLin_star, ← matrixToLin.map_mul, ← matrixToLin.map_mul]
  rw [mem_unitaryGroup_iff.mp g.prop, mem_unitaryGroup_iff'.mp g.prop, matrixToLin.map_one]
  simp

@[simps!]
noncomputable def unitaryToLin : unitaryGroup (Fin 2) ℂ →* unitary (higgsVec →L[ℂ] higgsVec) where
  toFun g := ⟨matrixToLin g, matrixToLin_unitary g⟩
  map_mul' g h := by
    ext
    simp
  map_one' := by
    ext
    simp

@[simps!]
def unitToLinear : unitary (higgsVec →L[ℂ] higgsVec) →* higgsVec →ₗ[ℂ] higgsVec :=
  DistribMulAction.toModuleEnd ℂ higgsVec

@[simps!]
def rep : Representation ℂ guageGroup higgsVec :=
   unitToLinear.comp (unitaryToLin.comp higgsRepUnitary)

lemma higgsRepUnitary_mul (g : guageGroup) (φ : higgsVec) :
    (higgsRepUnitary g).1 *ᵥ φ = g.2.2 ^ 3 • (g.2.1.1 *ᵥ φ) := by
  simp only [higgsRepUnitary_apply_coe]
  exact smul_mulVec_assoc (g.2.2 ^ 3) (g.2.1.1) φ

lemma rep_apply (g : guageGroup) (φ : higgsVec) : rep g φ = g.2.2 ^ 3 • (g.2.1.1 *ᵥ φ) :=
  higgsRepUnitary_mul g φ


lemma norm_invariant (g : guageGroup) (φ : higgsVec) : ‖rep g φ‖ = ‖φ‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (unitaryToLin (higgsRepUnitary g)).2 φ

/-- The higgs potential for `higgsVec`, i.e. for constant higgs fields. -/
def potential (μSq lambda : ℝ) (φ : higgsVec) : ℝ := - μSq  * ‖φ‖ ^ 2  +
  lambda * ‖φ‖ ^ 4

lemma potential_invariant (μSq lambda : ℝ) (φ : higgsVec)  (g : guageGroup) :
    potential μSq lambda (rep g φ) = potential μSq lambda φ := by
  simp only [potential, neg_mul]
  rw [norm_invariant]

lemma potential_snd_term_nonneg {lambda : ℝ} (hLam : 0 < lambda) (φ : higgsVec) :
    0 ≤ lambda * ‖φ‖ ^ 4 := by
  rw [mul_nonneg_iff]
  apply Or.inl
  simp_all only [ge_iff_le, norm_nonneg, pow_nonneg, and_true]
  exact le_of_lt hLam

lemma potential_as_quad (μSq lambda : ℝ) (φ : higgsVec) :
    lambda  * ‖φ‖ ^ 2 * ‖φ‖ ^ 2 + (- μSq ) * ‖φ‖ ^ 2 + (- potential μSq lambda φ ) = 0 := by
  simp [potential]
  ring

lemma zero_le_potential_discrim (μSq lambda : ℝ) (φ : higgsVec) (hLam : 0 < lambda) :
    0 ≤ discrim (lambda) (- μSq ) (- potential μSq lambda φ) := by
  have h1 := potential_as_quad μSq lambda φ
  rw [quadratic_eq_zero_iff_discrim_eq_sq] at h1
  rw [h1]
  exact sq_nonneg (2 * (lambda ) * ‖φ‖ ^ 2 + -μSq)
  simp only [ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
  exact ne_of_gt hLam


lemma potential_eq_zero_sol (μSq lambda : ℝ) (hLam : 0 < lambda)(φ : higgsVec)
    (hV : potential μSq lambda φ = 0) : φ = 0 ∨ ‖φ‖ ^ 2 = μSq / lambda := by
  have h1 := potential_as_quad μSq lambda φ
  rw [hV] at h1
  have h2 : ‖φ‖ ^ 2 * (lambda  * ‖φ‖ ^ 2  + -μSq ) = 0 := by
    linear_combination h1
  simp at h2
  cases' h2 with h2 h2
  simp_all
  apply Or.inr
  field_simp at h2 ⊢
  ring_nf
  linear_combination h2

lemma potential_eq_zero_sol_of_μSq_nonpos {μSq lambda : ℝ} (hLam : 0 < lambda) (hμSq : μSq ≤ 0)
    (φ : higgsVec)  (hV : potential μSq lambda φ = 0) : φ = 0 := by
  cases' (potential_eq_zero_sol μSq lambda hLam φ hV) with h1 h1
  exact h1
  by_cases hμSqZ : μSq = 0
  simpa [hμSqZ] using h1
  refine ((?_ : ¬ 0 ≤  μSq / lambda) (?_)).elim
  · simp_all [div_nonneg_iff]
    intro h
    exact lt_imp_lt_of_le_imp_le (fun _ => h) (lt_of_le_of_ne hμSq hμSqZ)
  · rw [← h1]
    exact sq_nonneg ‖φ‖

lemma potential_bounded_below (μSq lambda : ℝ) (hLam : 0 < lambda) (φ : higgsVec) :
    - μSq ^ 2 / (4 * lambda) ≤ potential μSq lambda φ  := by
  have h1 := zero_le_potential_discrim μSq lambda φ hLam
  simp [discrim] at h1
  ring_nf at h1
  rw [← neg_le_iff_add_nonneg'] at h1
  have h3 : lambda * potential μSq lambda φ * 4 = (4 * lambda) * potential μSq lambda φ := by
    ring
  rw [h3] at h1
  have h2 :=  (div_le_iff' (by simp [hLam] : 0 < 4 * lambda )).mpr h1
  ring_nf at h2 ⊢
  exact h2

lemma potential_bounded_below_of_μSq_nonpos {μSq lambda : ℝ} (hLam : 0 < lambda)
    (hμSq : μSq ≤ 0) (φ : higgsVec) : 0 ≤ potential μSq lambda φ := by
  simp only [potential, neg_mul, add_zero]
  refine add_nonneg ?_ (potential_snd_term_nonneg hLam φ)
  field_simp
  rw [@mul_nonpos_iff]
  simp_all only [ge_iff_le, norm_nonneg, pow_nonneg, and_self, or_true]


lemma potential_eq_bound_discrim_zero (μSq lambda : ℝ) (hLam : 0 < lambda)(φ : higgsVec)
    (hV : potential μSq lambda φ = - μSq ^ 2 / (4  * lambda)) :
    discrim (lambda) (- μSq) (- potential μSq lambda φ) = 0 := by
  simp [discrim, hV]
  field_simp
  ring

lemma potential_eq_bound_higgsVec_sq (μSq lambda : ℝ) (hLam : 0 < lambda)(φ : higgsVec)
    (hV : potential μSq lambda φ = - μSq ^ 2 / (4  * lambda)) :
    ‖φ‖ ^ 2 = μSq / (2 * lambda) := by
  have h1 := potential_as_quad μSq lambda φ
  rw [quadratic_eq_zero_iff_of_discrim_eq_zero _
    (potential_eq_bound_discrim_zero μSq lambda hLam φ hV)] at h1
  rw [h1]
  field_simp
  ring_nf
  simp only [ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
  exact ne_of_gt hLam

lemma potential_eq_bound_iff (μSq lambda : ℝ) (hLam : 0 < lambda)(φ : higgsVec) :
    potential μSq lambda φ = - μSq ^ 2 / (4  * lambda) ↔ ‖φ‖ ^ 2 = μSq / (2 * lambda) := by
  apply Iff.intro
  · intro h
    exact potential_eq_bound_higgsVec_sq μSq lambda hLam φ h
  · intro h
    have hv : ‖φ‖  ^ 4 = ‖φ‖ ^ 2 * ‖φ‖ ^ 2 := by
      ring_nf
    field_simp [potential, hv, h]
    ring

lemma potential_eq_bound_iff_of_μSq_nonpos {μSq lambda : ℝ} (hLam : 0 < lambda)
    (hμSq : μSq ≤ 0) (φ : higgsVec) : potential μSq lambda φ = 0 ↔ φ = 0 := by
  apply Iff.intro
  · intro h
    exact potential_eq_zero_sol_of_μSq_nonpos hLam hμSq φ h
  · intro h
    simp [potential, h]

lemma potential_eq_bound_IsMinOn (μSq lambda : ℝ) (hLam : 0 < lambda)  (φ : higgsVec)
    (hv : potential μSq lambda φ = - μSq ^ 2 / (4  * lambda)) :
    IsMinOn (potential μSq lambda) Set.univ φ := by
  rw [isMinOn_univ_iff]
  intro x
  rw [hv]
  exact potential_bounded_below μSq lambda hLam x

lemma potential_eq_bound_IsMinOn_of_μSq_nonpos {μSq lambda : ℝ} (hLam : 0 < lambda)
    (hμSq : μSq ≤ 0) (φ : higgsVec) (hv : potential μSq lambda φ = 0) :
    IsMinOn (potential μSq lambda) Set.univ φ := by
  rw [isMinOn_univ_iff]
  intro x
  rw [hv]
  exact potential_bounded_below_of_μSq_nonpos hLam hμSq x

lemma potential_bound_reached_of_μSq_nonneg {μSq lambda : ℝ} (hLam : 0 < lambda) (hμSq : 0 ≤ μSq) :
    ∃ (φ : higgsVec), potential μSq lambda φ = - μSq ^ 2 / (4  * lambda) := by
  use ![√(μSq/(2 * lambda)), 0]
  refine (potential_eq_bound_iff μSq lambda hLam _).mpr ?_
  simp [@PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  field_simp [mul_pow]

lemma IsMinOn_potential_iff_of_μSq_nonneg {μSq lambda : ℝ} (hLam : 0 < lambda) (hμSq : 0 ≤ μSq) :
    IsMinOn (potential μSq lambda) Set.univ φ ↔ ‖φ‖ ^ 2 = μSq /(2 * lambda) := by
  apply Iff.intro
  · intro h
    obtain ⟨φm, hφ⟩ := potential_bound_reached_of_μSq_nonneg hLam hμSq
    have hm := isMinOn_univ_iff.mp h φm
    rw [hφ] at hm
    have h1 := potential_bounded_below μSq lambda hLam φ
    rw [← potential_eq_bound_iff μSq lambda hLam φ]
    exact (Real.partialOrder.le_antisymm _ _ h1 hm).symm
  · intro h
    rw [← potential_eq_bound_iff μSq lambda hLam φ] at h
    exact potential_eq_bound_IsMinOn μSq lambda hLam φ h


lemma IsMinOn_potential_iff_of_μSq_nonpos {μSq lambda : ℝ} (hLam : 0 < lambda) (hμSq : μSq ≤ 0) :
    IsMinOn (potential μSq lambda) Set.univ φ ↔ φ = 0 := by
  apply Iff.intro
  · intro h
    have h0 := isMinOn_univ_iff.mp h 0
    rw [(potential_eq_bound_iff_of_μSq_nonpos hLam hμSq 0).mpr (by rfl)] at h0
    have h1 := potential_bounded_below_of_μSq_nonpos hLam hμSq φ
    rw [← (potential_eq_bound_iff_of_μSq_nonpos hLam hμSq φ)]
    exact (Real.partialOrder.le_antisymm _ _ h1 h0).symm
  · intro h
    rw [← potential_eq_bound_iff_of_μSq_nonpos hLam hμSq φ] at h
    exact potential_eq_bound_IsMinOn_of_μSq_nonpos hLam hμSq φ h

/-- Given a Higgs vector, a rotation matrix which puts the fst component of the
vector to zero, and the snd componenet to a real -/
def rotateMatrix (φ : higgsVec) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![φ 1 /‖φ‖ , - φ 0 /‖φ‖], ![conj (φ 0) / ‖φ‖ , conj (φ 1) / ‖φ‖] ]

lemma rotateMatrix_star (φ : higgsVec) :
    star φ.rotateMatrix =
    ![![conj (φ 1) /‖φ‖ ,  φ 0 /‖φ‖], ![- conj (φ 0) / ‖φ‖ , φ 1 / ‖φ‖] ] := by
  simp [star]
  rw [rotateMatrix, conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conj_ofReal]


lemma rotateMatrix_det {φ : higgsVec} (hφ : φ ≠ 0) : (rotateMatrix φ).det = 1 := by
  simp [rotateMatrix, det_fin_two]
  have h1 : (‖φ‖ : ℂ)  ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
  field_simp
  rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, Complex.inner,  neg_mul, sub_neg_eq_add,
    Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm, add_comm]
  rfl

lemma rotateMatrix_unitary {φ : higgsVec} (hφ : φ ≠ 0) :
    (rotateMatrix φ) ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff', rotateMatrix_star, rotateMatrix]
  erw [mul_fin_two, one_fin_two]
  have : (‖φ‖ : ℂ)  ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
  congr
  field_simp
  ext i j
  fin_cases i <;> fin_cases j <;> field_simp
  · rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply, Complex.inner,  neg_mul, sub_neg_eq_add,
      Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm, add_comm]
    rfl
  · ring_nf
  · ring_nf
  · rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
    simp only [PiLp.inner_apply, Complex.inner,  neg_mul, sub_neg_eq_add,
      Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm]
    rfl

lemma rotateMatrix_specialUnitary {φ : higgsVec} (hφ : φ ≠ 0) :
    (rotateMatrix φ) ∈ specialUnitaryGroup (Fin 2) ℂ :=
  mem_specialUnitaryGroup_iff.mpr ⟨rotateMatrix_unitary hφ, rotateMatrix_det hφ⟩

/-- Given a Higgs vector, an element of the gauge group which puts the fst component of the
vector to zero, and the snd componenet to a real -/
def rotateGuageGroup {φ : higgsVec} (hφ : φ ≠ 0) : guageGroup :=
    ⟨1, ⟨(rotateMatrix φ), rotateMatrix_specialUnitary hφ⟩, 1⟩

lemma rotateGuageGroup_apply {φ : higgsVec} (hφ : φ ≠ 0) :
    rep (rotateGuageGroup hφ) φ = ![0, ofReal ‖φ‖] := by
  rw [rep_apply]
  simp [rotateGuageGroup, rotateMatrix]
  ext i
  fin_cases i
  simp [mulVec, vecHead, vecTail]
  ring_nf
  simp only [Fin.mk_one, Fin.isValue, cons_val_one, head_cons]
  simp [mulVec, vecHead, vecTail]
  have : (‖φ‖ : ℂ)  ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
  field_simp
  rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, Complex.inner,  neg_mul, sub_neg_eq_add,
      Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm]
  rfl

theorem rotate_fst_zero_snd_real (φ : higgsVec) :
    ∃ (g : guageGroup), rep g φ = ![0, ofReal ‖φ‖] := by
  by_cases h : φ = 0
  · use ⟨1, 1, 1⟩
    simp [h]
    ext i
    fin_cases i <;> rfl
  · use rotateGuageGroup h
    exact rotateGuageGroup_apply h

end higgsVec
end higgsVec

end
end StandardModel
