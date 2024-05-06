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

-/
universe v u
namespace StandardModel
noncomputable section

open Manifold
open Matrix
open Complex
open ComplexConjugate

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

def higgsVecToFin2ℂ : higgsVec →L[ℝ] (Fin 2 → ℂ) where
  toFun x := x
  map_add' x y := by
    simp
  map_smul' a x := by
    simp

lemma smooth_higgsVecToFin2ℂ : Smooth 𝓘(ℝ, higgsVec) 𝓘(ℝ, Fin 2 → ℂ) higgsVecToFin2ℂ :=
  ContinuousLinearMap.smooth higgsVecToFin2ℂ

@[simps!]
noncomputable def higgsRepMap (g : guageGroup) : higgsVec →ₗ[ℂ] higgsVec where
  toFun S :=  (g.2 ^ 3) • (g.1.1 *ᵥ S)
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

end higgsVec

namespace higgsField
open  Complex Real

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

lemma higgsVecToFin2ℂ_toHiggsVec (φ : higgsField) : higgsVecToFin2ℂ ∘ φ.toHiggsVec = φ := by
  ext x
  rfl

lemma toVec_smooth (φ : higgsField) : Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, Fin 2 → ℂ) φ := by
  rw [← φ.higgsVecToFin2ℂ_toHiggsVec]
  exact Smooth.comp smooth_higgsVecToFin2ℂ (φ.toHiggsVec_smooth)

lemma comp_smooth (φ : higgsField) :
    ∀ i, Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℂ) (fun (x : spaceTime) => (φ x i)) := by
  rw [← smooth_pi_space]
  exact φ.toVec_smooth

lemma comp_re_smooth (φ : higgsField) (i : Fin 2):
    Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℝ) (reCLM ∘ (fun (x : spaceTime) =>  (φ x i))) :=
  Smooth.comp (ContinuousLinearMap.smooth reCLM) (φ.comp_smooth i)

lemma comp_im_smooth (φ : higgsField) (i : Fin 2):
    Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℝ) (imCLM ∘ (fun (x : spaceTime) =>  (φ x i))) :=
  Smooth.comp (ContinuousLinearMap.smooth imCLM) (φ.comp_smooth i)

@[simp]
def normSq (φ : higgsField) : spaceTime → ℝ := fun x => ( ‖φ x‖ ^ 2)

lemma normSq_expand (φ : higgsField)  :
    φ.normSq  = fun x => (conj (φ x 0) * (φ x 0) + conj (φ x 1) * (φ x 1) ).re := by
  funext x
  simp
  rw [@norm_sq_eq_inner ℂ]
  simp

lemma normSq_smooth (φ : higgsField) : Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℝ) φ.normSq := by
  rw [normSq_expand]
  refine Smooth.add ?_ ?_
  simp
  refine Smooth.add ?_ ?_
  refine Smooth.smul ?_ ?_
  exact φ.comp_re_smooth 0
  exact φ.comp_re_smooth 0
  refine Smooth.smul ?_ ?_
  exact φ.comp_im_smooth 0
  exact φ.comp_im_smooth 0
  simp
  refine Smooth.add ?_ ?_
  refine Smooth.smul ?_ ?_
  exact φ.comp_re_smooth 1
  exact φ.comp_re_smooth 1
  refine Smooth.smul ?_ ?_
  exact φ.comp_im_smooth 1
  exact φ.comp_im_smooth 1

lemma normSq_nonneg (φ : higgsField) (x : spaceTime) : 0 ≤ φ.normSq x := by
  simp only [normSq, ge_iff_le, norm_nonneg, pow_nonneg]

lemma normSq_zero (φ : higgsField) (x : spaceTime) : φ.normSq x = 0 ↔ φ x = 0 := by
  simp only [normSq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero]

@[simp]
def potential (φ : higgsField) (μSq lambda : ℝ ) (x : spaceTime) :  ℝ :=
  - μSq * φ.normSq x + lambda * φ.normSq x * φ.normSq x

lemma potential_smooth (φ : higgsField) (μSq lambda : ℝ ) :
    Smooth 𝓘(ℝ, spaceTime) 𝓘(ℝ, ℝ) (fun x => φ.potential μSq lambda x) := by
  simp only [potential, normSq, neg_mul]
  exact Smooth.add
    (Smooth.neg (Smooth.smul smooth_const φ.normSq_smooth))
    (Smooth.smul (Smooth.smul smooth_const φ.normSq_smooth) φ.normSq_smooth)





/-- A higgs field is constant if it is equal for all `x` `y` in `spaceTime`. -/
def isConst (Φ : higgsField) : Prop := ∀ x y, Φ x = Φ y

/-- Given a vector `ℂ²` the constant higgs field with value equal to that
section. -/
noncomputable def const (φ : higgsVec) : higgsField where
  toFun := fun _ => φ
  contMDiff_toFun := by
    intro x
    rw [Bundle.contMDiffAt_section]
    exact smoothAt_const

lemma normSq_const (φ : higgsVec) : (const φ).normSq = fun x => (norm φ) ^ 2 := by
  simp only [normSq, const]
  funext x
  simp

lemma potential_const (φ : higgsVec) (μSq lambda : ℝ ) :
    (const φ).potential μSq lambda = fun x => - μSq * (norm φ) ^ 2 + lambda * (norm φ) ^ 4 := by
  unfold potential
  rw [normSq_const]
  ring_nf

def constStd (v : ℝ) : higgsField := const ![0, v/√2]

lemma normSq_constStd (v : ℝ) : (constStd v).normSq = fun x => v ^ 2 / 2 := by
  simp only [normSq_const, constStd]
  funext x
  rw [@PiLp.norm_sq_eq_of_L2]
  rw [Fin.sum_univ_two]
  simp

def potentialConstStd (μSq lambda v: ℝ) : ℝ := - μSq /2 * v ^ 2  + lambda /4 * v ^ 4

lemma potential_constStd (v μSq lambda : ℝ) :
    (constStd v).potential μSq lambda = fun _ => potentialConstStd μSq lambda v := by
  unfold potential potentialConstStd
  rw [normSq_constStd]
  simp
  ring_nf

lemma smooth_potentialConstStd (μSq lambda : ℝ) :
    Smooth 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun v => potentialConstStd μSq lambda v) := by
  simp only [potentialConstStd]
  have h1 (v : ℝ) : v ^ 4 = v * v * v * v := by
    ring
  simp [sq, h1]
  refine Smooth.add ?_ ?_
  exact Smooth.smul smooth_const (Smooth.smul smooth_id smooth_id)
  exact Smooth.smul smooth_const
    (Smooth.smul (Smooth.smul (Smooth.smul smooth_id smooth_id)  smooth_id)  smooth_id)


lemma deriv_potentialConstStd (μSq lambda v : ℝ) :
    deriv (fun v => potentialConstStd μSq lambda v) v = - μSq * v + lambda * v ^ 3 := by
  simp only [potentialConstStd]
  rw [deriv_add, deriv_mul, deriv_mul,  deriv_const, deriv_const, deriv_pow, deriv_pow]
  simp
  ring
  exact differentiableAt_const _
  exact differentiableAt_pow _
  exact differentiableAt_const _
  exact differentiableAt_pow _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _
  exact DifferentiableAt.const_mul (differentiableAt_pow _) _

lemma deriv_potentialConstStd_zero (μSq lambda v : ℝ) (hLam : 0 < lambda)
    (hv : deriv (fun v => potentialConstStd μSq lambda v) v = 0) : v = 0 ∨ v ^ 2 = μSq/lambda:= by
  rw [deriv_potentialConstStd] at hv
  ring_nf at hv
  have h1 : v * (- μSq + lambda * v ^ 2) = 0 := by
    ring_nf
    linear_combination hv
  simp at h1
  cases'  h1 with h1 h1
  simp_all
  apply Or.inr
  field_simp
  linear_combination h1

lemma potentialConstStd_bounded' (μSq lambda v x : ℝ) (hLam : 0 < lambda) :
    potentialConstStd μSq lambda v = x → - μSq ^ 2 / (4  * lambda) ≤ x  := by
  simp only [potentialConstStd]
  intro h
  let y := v ^2
  have h1 :  lambda / 4 * y * y + (- μSq / 2) * y + (-x) = 0 := by
    simp [y]
    linear_combination h
  rw [quadratic_eq_zero_iff_discrim_eq_sq] at h1
  simp [discrim] at h1
  have h2 : 0 ≤ μSq ^ 2 / 2 ^ 2 + 4 * (lambda / 4) * x  := by
    rw [h1]
    exact sq_nonneg (2 * (lambda / 4) * y + -μSq / 2)
  ring_nf at h2
  rw [← neg_le_iff_add_nonneg'] at h2
  have h4 :=  (div_le_iff' hLam).mpr h2
  ring_nf at h4
  ring_nf
  exact h4
  simp
  exact OrderIso.mulLeft₀.proof_1 lambda hLam

lemma potentialConstStd_bounded (μSq lambda v : ℝ) (hLam : 0 < lambda) :
    - μSq ^ 2 / (4  * lambda) ≤ potentialConstStd μSq lambda v := by
  apply potentialConstStd_bounded' μSq lambda v (potentialConstStd μSq lambda v) hLam
  rfl

lemma potentialConstStd_IsMinOn_of_eq_bound (μSq lambda v : ℝ) (hLam : 0 < lambda)
    (hv : potentialConstStd μSq lambda v = - μSq ^ 2 / (4  * lambda)) :
    IsMinOn (potentialConstStd μSq lambda) Set.univ v := by
  rw [isMinOn_univ_iff]
  intro x
  rw [hv]
  exact potentialConstStd_bounded μSq lambda x hLam

lemma potentialConstStd_vsq_of_eq_bound (μSq lambda v : ℝ) (hLam : 0 < lambda) :
    potentialConstStd μSq lambda v = - μSq ^ 2 / (4  * lambda) ↔ v ^ 2 = μSq / lambda := by
  apply Iff.intro
  intro h
  simp [potentialConstStd] at h
  field_simp at h
  have h1 :  (8 * lambda ^ 2) * v ^ 2 * v ^ 2 + (- 16 * μSq * lambda ) * v ^ 2 + (8 * μSq ^ 2) = 0 := by
    linear_combination h
  have hd : discrim (8 * lambda ^ 2) (- 16 * μSq * lambda) (8 * μSq ^ 2) = 0 := by
    simp [discrim]
    ring_nf
  rw [quadratic_eq_zero_iff_of_discrim_eq_zero _ hd] at h1
  field_simp at h1 ⊢
  ring_nf at h1
  have hx :  16 * lambda ≠ 0 := by
    simp [hLam]
    exact OrderIso.mulLeft₀.proof_1 lambda hLam
  apply mul_left_cancel₀ hx
  ring_nf
  rw [← h1]
  ring
  simp
  exact OrderIso.mulLeft₀.proof_1 lambda hLam
  intro h
  simp [potentialConstStd, h]
  have hv : v ^ 4 = v^2 * v^2 := by
    ring
  rw [hv, h]
  field_simp
  ring

lemma potentialConstStd_IsMinOn (μSq lambda v : ℝ) (hLam : 0 < lambda) (hμSq : 0 ≤ μSq) :
    IsMinOn (potentialConstStd μSq lambda) Set.univ v ↔ v ^ 2 = μSq / lambda := by
  apply Iff.intro
  intro h
  have h1 := potentialConstStd_bounded μSq lambda v hLam
  rw [isMinOn_univ_iff] at h
  let vmin := √(μSq / lambda)
  have hvmin : vmin ^ 2 = μSq / lambda := by
    simp [vmin]
    field_simp
  have h2 := h vmin
  have h3 := (potentialConstStd_vsq_of_eq_bound μSq lambda vmin hLam).mpr hvmin
  rw [h3] at h2
  rw [(potentialConstStd_vsq_of_eq_bound μSq lambda v hLam).mp]
  exact (Real.partialOrder.le_antisymm _ _ h1 h2).symm
  intro h
  rw [← potentialConstStd_vsq_of_eq_bound μSq lambda v hLam] at h
  exact potentialConstStd_IsMinOn_of_eq_bound μSq lambda v hLam h





lemma potentialConstStd_muSq_le_zero_nonneg (μSq lambda v : ℝ) (hLam : 0 < lambda)
    (hμSq : μSq ≤ 0) : 0 ≤ potentialConstStd μSq lambda v := by
  simp [potentialConstStd]
  apply add_nonneg
  field_simp
  refine div_nonneg ?_ (by simp)
  refine neg_nonneg.mpr ?_
  rw [@mul_nonpos_iff]
  simp_all
  apply Or.inr
  exact sq_nonneg v
  rw [mul_nonneg_iff]
  apply Or.inl
  apply And.intro
  refine div_nonneg ?_ (by simp)
  exact le_of_lt hLam
  have hv : v ^ 4 = (v ^ 2) ^ 2 := by ring
  rw [hv]
  exact sq_nonneg (v ^ 2)

lemma potentialConstStd_zero_muSq_le_zero (μSq lambda v : ℝ) (hLam : 0 < lambda)
    (hμSq : μSq ≤ 0) : potentialConstStd μSq lambda v = 0 ↔ v = 0 := by
  apply Iff.intro
  · intro h
    simp [potentialConstStd] at h
    field_simp at h
    have h1 :  v ^ 2 * ((2 * lambda ) * v ^ 2  + (- 4 * μSq  )) = 0 := by
      linear_combination h
    simp at h1
    cases' h1 with h1 h1
    exact h1
    have h2 :   v ^ 2 = (4 * μSq) / (2 * lambda) := by
      field_simp
      ring_nf
      linear_combination h1
    by_cases hμSqZ : μSq = 0
    rw [hμSqZ] at h2
    simpa using h2
    have h3 :  ¬ (0 ≤ 4 * μSq / (2 * lambda)) := by
      rw [div_nonneg_iff]
      simp
      rw [not_or]
      apply And.intro
      simp
      intro hm
      exact (hμSqZ (le_antisymm hμSq hm)).elim
      simp
      intro _
      simp_all only [true_or]
    rw [← h2] at h3
    refine (h3 ?_).elim
    exact sq_nonneg v
  · intro h
    simp [potentialConstStd, h]


lemma potentialConstStd_IsMinOn_muSq_le_zero (μSq lambda v : ℝ) (hLam : 0 < lambda)
    (hμSq : μSq ≤ 0) :
    IsMinOn (potentialConstStd μSq lambda) Set.univ v ↔ v = 0 := by
  have hx := (potentialConstStd_zero_muSq_le_zero μSq lambda 0 hLam hμSq)
  simp at hx
  apply Iff.intro
  intro h
  rw [isMinOn_univ_iff] at h
  have h1 := potentialConstStd_muSq_le_zero_nonneg μSq lambda v hLam hμSq
  have h2 := h 0
  rw [hx] at h2
  exact (potentialConstStd_zero_muSq_le_zero μSq lambda v hLam hμSq).mp
    (Real.partialOrder.le_antisymm _ _ h1 h2).symm
  intro h
  rw [h, isMinOn_univ_iff, hx]
  intro x
  exact potentialConstStd_muSq_le_zero_nonneg μSq lambda x hLam hμSq




lemma const_isConst (φ : Fin 2 → ℂ) : (const φ).isConst := by
  intro x _
  simp [const]

lemma isConst_iff_exists_const (Φ : higgsField) : Φ.isConst ↔ ∃ φ, Φ = const φ := by
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


end higgsField
end
end StandardModel
