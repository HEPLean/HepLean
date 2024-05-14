/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.Basic
import HepLean.StandardModel.HiggsBoson.TargetSpace
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.Polyrith
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Geometry.Manifold.ContMDiff.Product
import Mathlib.Analysis.Complex.RealDeriv
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
open spaceTime

/-- The trivial vector bundle 𝓡² × ℂ². (TODO: Make associated bundle.) -/
abbrev higgsBundle := Bundle.Trivial spaceTime higgsVec

instance : SmoothVectorBundle higgsVec higgsBundle spaceTime.asSmoothManifold  :=
  Bundle.Trivial.smoothVectorBundle higgsVec 𝓘(ℝ, spaceTime)

/-- A higgs field is a smooth section of the higgs bundle. -/
abbrev higgsField : Type := SmoothSection spaceTime.asSmoothManifold higgsVec higgsBundle

instance : NormedAddCommGroup (Fin 2 → ℂ) := by
  exact Pi.normedAddCommGroup

/-- Given a vector `ℂ²` the constant higgs field with value equal to that
section. -/
noncomputable def higgsVec.toField (φ : higgsVec) : higgsField where
  toFun := fun _ => φ
  contMDiff_toFun := by
    intro x
    rw [Bundle.contMDiffAt_section]
    exact smoothAt_const

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
