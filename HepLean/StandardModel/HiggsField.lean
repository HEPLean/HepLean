/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.Polyrith
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Product
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Algebra.QuadraticDiscriminant
/-!
# The Higgs field

This file defines the basic properties for the higgs field in the standard model.

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

/-- The trivial vector bundle 𝓡² × ℂ². (TODO: Make associated bundle.) -/
abbrev higgsBundle := Bundle.Trivial spaceTime higgsVec

instance : SmoothVectorBundle higgsVec higgsBundle (𝓡 4)  :=
  Bundle.Trivial.smoothVectorBundle higgsVec 𝓘(ℝ, spaceTime)

/-- A higgs field is a smooth section of the higgs bundle. -/
abbrev higgsField : Type := SmoothSection (𝓡 4) higgsVec higgsBundle

instance : NormedAddCommGroup (Fin 2 → ℂ) := by
  exact Pi.normedAddCommGroup



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

/-- Given an element of `gaugeGroup` the linear automorphism of `higgsVec` it gets taken to. -/
@[simps!]
noncomputable def higgsRepMap (g : guageGroup) : higgsVec →ₗ[ℂ] higgsVec where
  toFun S :=  (g.2.2 ^ 3) • (g.2.1.1 *ᵥ S)
  map_add' S T := by
    simp [Matrix.mulVec_add, smul_add]
    rw [Matrix.mulVec_add, smul_add]
  map_smul' a S := by
    simp [Matrix.mulVec_smul]
    rw [Matrix.mulVec_smul]
    exact smul_comm  _ _ _


/-- The representation of the SM guage group acting on `ℂ²`. -/
noncomputable def higgsRep : Representation ℂ guageGroup higgsVec where
  toFun := higgsRepMap
  map_mul' U V := by
    apply LinearMap.ext
    intro S
    simp only [higgsRepMap, Prod.snd_mul, Submonoid.coe_inf, Prod.fst_mul, Submonoid.coe_mul,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply, LinearMap.map_smul_of_tower,
      mulVec_mulVec]
    simp  [mul_pow, smul_smul, mul_comm]
  map_one' := by
    apply LinearMap.ext
    intro S
    simp only [higgsRepMap, LinearMap.mul_apply, AddHom.coe_mk, LinearMap.coe_mk]
    change 1 ^ 3 • (1 *ᵥ _) = _
    rw [one_pow, Matrix.one_mulVec]
    simp only [one_smul, LinearMap.one_apply]

namespace higgsVec

/-- Given a vector `ℂ²` the constant higgs field with value equal to that
section. -/
noncomputable def toField (φ : higgsVec) : higgsField where
  toFun := fun _ => φ
  contMDiff_toFun := by
    intro x
    rw [Bundle.contMDiffAt_section]
    exact smoothAt_const

/-- The higgs potential for `higgsVec`, i.e. for constant higgs fields. -/
def potential (μSq lambda : ℝ) (φ : higgsVec) : ℝ := - μSq  * ‖φ‖ ^ 2  +
  lambda * ‖φ‖ ^ 4

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
    0 ≤ discrim (lambda ) (- μSq ) (- potential μSq lambda φ) := by
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
    higgsRep (rotateGuageGroup hφ) φ = ![0, ofReal ‖φ‖] := by
  simp [higgsRep, higgsRepMap, rotateGuageGroup, rotateMatrix, higgsRepMap]
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
    ∃ (g : guageGroup), higgsRep g φ = ![0, ofReal ‖φ‖] := by
  by_cases h : φ = 0
  · use ⟨1, 1, 1⟩
    simp [h, higgsRep, higgsRepMap]
    ext i
    fin_cases i <;> rfl
  · use rotateGuageGroup h
    exact rotateGuageGroup_apply h

end higgsVec
end higgsVec

namespace higgsField
open  Complex Real

/-- Given a `higgsField`, the corresponding map from `spaceTime` to `higgsVec`. -/
def toHiggsVec (φ : higgsField) : spaceTime → higgsVec := φ


lemma toHiggsVec_smooth (φ : higgsField) : Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, higgsVec) φ.toHiggsVec := by
  intro x0
  have h1 := φ.contMDiff x0
  rw [Bundle.contMDiffAt_section] at h1
  have h2 :
    (fun x => ((trivializationAt higgsVec (Bundle.Trivial spaceTime higgsVec) x0)
    { proj := x, snd := φ x }).2) = φ := by
    rfl
  simp only [h2] at h1
  exact h1

lemma toField_toHiggsVec_apply (φ : higgsField) (x : spaceTime) :
    (φ.toHiggsVec x).toField x = φ x := by
  rfl

lemma higgsVecToFin2ℂ_toHiggsVec (φ : higgsField) : higgsVecToFin2ℂ ∘ φ.toHiggsVec = φ := by
  ext x
  rfl

lemma toVec_smooth (φ : higgsField) : Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, Fin 2 → ℂ) φ := by
  rw [← φ.higgsVecToFin2ℂ_toHiggsVec]
  exact Smooth.comp smooth_higgsVecToFin2ℂ (φ.toHiggsVec_smooth)

lemma apply_smooth (φ : higgsField) :
    ∀ i, Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℂ) (fun (x : spaceTime) => (φ x i)) := by
  rw [← smooth_pi_space]
  exact φ.toVec_smooth

lemma apply_re_smooth (φ : higgsField) (i : Fin 2):
    Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℝ) (reCLM ∘ (fun (x : spaceTime) =>  (φ x i))) :=
  Smooth.comp (ContinuousLinearMap.smooth reCLM) (φ.apply_smooth i)

lemma apply_im_smooth (φ : higgsField) (i : Fin 2):
    Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℝ) (imCLM ∘ (fun (x : spaceTime) =>  (φ x i))) :=
  Smooth.comp (ContinuousLinearMap.smooth imCLM) (φ.apply_smooth i)

/-- Given a `higgsField`, the map `spaceTime → ℝ` obtained by taking the square norm of the
 higgs vector.  -/
@[simp]
def normSq (φ : higgsField) : spaceTime → ℝ := fun x => ( ‖φ x‖ ^ 2)

lemma toHiggsVec_norm (φ : higgsField) (x : spaceTime) :
    ‖φ x‖  = ‖φ.toHiggsVec x‖ := rfl

lemma normSq_expand (φ : higgsField)  :
    φ.normSq  = fun x => (conj (φ x 0) * (φ x 0) + conj (φ x 1) * (φ x 1) ).re := by
  funext x
  simp only [normSq, add_re, mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add]
  rw [@norm_sq_eq_inner ℂ]
  simp

lemma normSq_smooth (φ : higgsField) : Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℝ) φ.normSq := by
  rw [normSq_expand]
  refine Smooth.add ?_ ?_
  simp only [mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add]
  refine Smooth.add ?_ ?_
  refine Smooth.smul ?_ ?_
  exact φ.apply_re_smooth 0
  exact φ.apply_re_smooth 0
  refine Smooth.smul ?_ ?_
  exact φ.apply_im_smooth 0
  exact φ.apply_im_smooth 0
  simp only [mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add]
  refine Smooth.add ?_ ?_
  refine Smooth.smul ?_ ?_
  exact φ.apply_re_smooth 1
  exact φ.apply_re_smooth 1
  refine Smooth.smul ?_ ?_
  exact φ.apply_im_smooth 1
  exact φ.apply_im_smooth 1

lemma normSq_nonneg (φ : higgsField) (x : spaceTime) : 0 ≤ φ.normSq x := by
  simp only [normSq, ge_iff_le, norm_nonneg, pow_nonneg]

lemma normSq_zero (φ : higgsField) (x : spaceTime) : φ.normSq x = 0 ↔ φ x = 0 := by
  simp only [normSq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero]

/-- The Higgs potential of the form `- μ² * |φ|² + λ * |φ|⁴`. -/
@[simp]
def potential (φ : higgsField) (μSq lambda : ℝ ) (x : spaceTime) :  ℝ :=
  - μSq * φ.normSq x + lambda * φ.normSq x * φ.normSq x

lemma potential_smooth (φ : higgsField) (μSq lambda : ℝ) :
    Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℝ) (fun x => φ.potential μSq lambda x) := by
  simp only [potential, normSq, neg_mul]
  exact Smooth.add
    (Smooth.neg (Smooth.smul smooth_const φ.normSq_smooth))
    (Smooth.smul (Smooth.smul smooth_const φ.normSq_smooth) φ.normSq_smooth)


lemma potential_apply (φ : higgsField) (μSq lambda : ℝ) (x : spaceTime) :
    (φ.potential μSq lambda) x = higgsVec.potential μSq lambda (φ.toHiggsVec x) := by
  simp [higgsVec.potential, toHiggsVec_norm]
  ring


/-- A higgs field is constant if it is equal for all `x` `y` in `spaceTime`. -/
def isConst (Φ : higgsField) : Prop := ∀ x y, Φ x = Φ y

lemma isConst_of_higgsVec (φ : higgsVec) : φ.toField.isConst := by
  intro x _
  simp [higgsVec.toField]

lemma isConst_iff_of_higgsVec (Φ : higgsField) : Φ.isConst ↔ ∃ (φ : higgsVec), Φ = φ.toField := by
  apply Iff.intro
  intro h
  use Φ 0
  ext x y
  rw [← h x 0]
  rfl
  intro h
  intro x y
  obtain ⟨φ, hφ⟩ := h
  subst hφ
  rfl

lemma normSq_of_higgsVec (φ : higgsVec) : φ.toField.normSq = fun x => (norm φ) ^ 2 := by
  simp only [normSq, higgsVec.toField]
  funext x
  simp

lemma potential_of_higgsVec (φ : higgsVec) (μSq lambda : ℝ) :
    φ.toField.potential μSq lambda = fun _ => higgsVec.potential μSq lambda φ := by
  simp [higgsVec.potential]
  unfold potential
  rw [normSq_of_higgsVec]
  funext x
  simp only [neg_mul, add_right_inj]
  ring_nf



end higgsField
end
end StandardModel
