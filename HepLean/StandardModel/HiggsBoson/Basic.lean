/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Basic
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
import Mathlib.Algebra.QuadraticDiscriminant
/-!
# The Higgs field

This file defines the basic properties for the higgs field in the standard model.

## References

- We use conventions given in: [Review of Particle Physics, PDG][ParticleDataGroup:2018ovx]

-/
universe v u
namespace StandardModel
noncomputable section

open Manifold
open Matrix
open Complex
open ComplexConjugate
open SpaceTime
/-!

## Definition of the Higgs bundle

-/

/-! TODO: Make `HiggsBundle` an associated bundle. -/
/-- The trivial vector bundle 𝓡² × ℂ². -/
abbrev HiggsBundle := Bundle.Trivial SpaceTime HiggsVec

instance : SmoothVectorBundle HiggsVec HiggsBundle SpaceTime.asSmoothManifold  :=
  Bundle.Trivial.smoothVectorBundle HiggsVec 𝓘(ℝ, SpaceTime)

/-- A higgs field is a smooth section of the higgs bundle. -/
abbrev HiggsField : Type := SmoothSection SpaceTime.asSmoothManifold HiggsVec HiggsBundle

instance : NormedAddCommGroup (Fin 2 → ℂ) := by
  exact Pi.normedAddCommGroup

/-- Given a vector `ℂ²` the constant higgs field with value equal to that
section. -/
noncomputable def HiggsVec.toField (φ : HiggsVec) : HiggsField where
  toFun := fun _ ↦ φ
  contMDiff_toFun := by
    intro x
    rw [Bundle.contMDiffAt_section]
    exact smoothAt_const

namespace HiggsField
open  Complex Real

/-!

## Relation to `HiggsVec`

-/

/-- Given a `higgsField`, the corresponding map from `spaceTime` to `higgsVec`. -/
def toHiggsVec (φ : HiggsField) : SpaceTime → HiggsVec := φ

lemma toHiggsVec_smooth (φ : HiggsField) : Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, HiggsVec) φ.toHiggsVec := by
  intro x0
  have h1 := φ.contMDiff x0
  rw [Bundle.contMDiffAt_section] at h1
  have h2 :
    (fun x => ((trivializationAt HiggsVec (Bundle.Trivial SpaceTime HiggsVec) x0)
    { proj := x, snd := φ x }).2) = φ := by
    rfl
  simp only [h2] at h1
  exact h1

lemma toField_toHiggsVec_apply (φ : HiggsField) (x : SpaceTime) :
    (φ.toHiggsVec x).toField x = φ x := rfl

lemma higgsVecToFin2ℂ_toHiggsVec (φ : HiggsField) :
    higgsVecToFin2ℂ ∘ φ.toHiggsVec = φ := rfl

/-!

## The inner product and norm of Higgs fields

-/

/-- Given two `HiggsField`, the map `spaceTime → ℂ` obtained by taking their inner product. -/
def innerProd (φ1 φ2 : HiggsField) : SpaceTime → ℂ := fun x => ⟪φ1 x, φ2 x⟫_ℂ

/-- Notation for the inner product of two Higgs fields. -/
scoped[StandardModel.HiggsField] notation "⟪" φ1 "," φ2 "⟫_H" => innerProd φ1 φ2

@[simp]
lemma innerProd_left_zero (φ : HiggsField) : ⟪0, φ⟫_H = 0 := by
  funext x
  simp [innerProd]

@[simp]
lemma innerProd_right_zero (φ : HiggsField) : ⟪φ, 0⟫_H = 0 := by
  funext x
  simp [innerProd]

lemma innerProd_expand (φ1 φ2 : HiggsField)  :
    ⟪φ1, φ2⟫_H  = fun x => (conj (φ1 x 0) * (φ2 x 0) + conj (φ1 x 1) * (φ2 x 1) ) := by
  funext x
  simp only [innerProd, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]

/-- Given a `higgsField`, the map `spaceTime → ℝ` obtained by taking the square norm of the
 higgs vector.  -/
@[simp]
def normSq (φ : HiggsField) : SpaceTime → ℝ := fun x => ( ‖φ x‖ ^ 2)

/-- Notation for the norm squared of a Higgs field. -/
scoped[StandardModel.HiggsField] notation "‖" φ1 "‖_H ^ 2" => normSq φ1

lemma innerProd_self_eq_normSq (φ : HiggsField) (x : SpaceTime) :
    ⟪φ, φ⟫_H x  = ‖φ‖_H ^ 2 x := by
  erw [normSq, @PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  simp only [ ofReal_add, ofReal_pow, innerProd, PiLp.inner_apply,
    RCLike.inner_apply, Fin.sum_univ_two, conj_mul']

lemma normSq_eq_innerProd_self (φ : HiggsField) (x : SpaceTime) :
    ‖φ x‖ ^ 2 = (⟪φ, φ⟫_H x).re := by
  rw [innerProd_self_eq_normSq]
  rfl

lemma toHiggsVec_norm (φ : HiggsField) (x : SpaceTime) :
    ‖φ x‖  = ‖φ.toHiggsVec x‖ := rfl

lemma normSq_expand (φ : HiggsField)  :
    φ.normSq  = fun x => (conj (φ x 0) * (φ x 0) + conj (φ x 1) * (φ x 1) ).re := by
  funext x
  simp [normSq, add_re, mul_re, conj_re, conj_im, neg_mul, sub_neg_eq_add, @norm_sq_eq_inner ℂ]

lemma normSq_nonneg (φ : HiggsField) (x : SpaceTime) : 0 ≤ φ.normSq x := by
  simp [normSq, ge_iff_le, norm_nonneg, pow_nonneg]

lemma normSq_zero (φ : HiggsField) (x : SpaceTime) : φ.normSq x = 0 ↔ φ x = 0 := by
  simp [normSq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero]

/-!

## The Higgs potential

-/

/-- The Higgs potential of the form `- μ² * |φ|² + λ * |φ|⁴`. -/
@[simp]
def potential (φ : HiggsField) (μSq lambda : ℝ ) (x : SpaceTime) :  ℝ :=
  - μSq * φ.normSq x + lambda * φ.normSq x * φ.normSq x

lemma potential_apply (φ : HiggsField) (μSq lambda : ℝ) (x : SpaceTime) :
    (φ.potential μSq lambda) x = HiggsVec.potential μSq lambda (φ.toHiggsVec x) := by
  simp [HiggsVec.potential, toHiggsVec_norm]
  ring

/-!

## Smoothness

-/

lemma toVec_smooth (φ : HiggsField) : Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, Fin 2 → ℂ) φ :=
  smooth_higgsVecToFin2ℂ.comp φ.toHiggsVec_smooth

lemma apply_smooth (φ : HiggsField) :
    ∀ i, Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℂ) (fun (x : SpaceTime) => (φ x i)) :=
  (smooth_pi_space).mp (φ.toVec_smooth)

lemma apply_re_smooth (φ : HiggsField) (i : Fin 2):
    Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) (reCLM ∘ (fun (x : SpaceTime) =>  (φ x i))) :=
  (ContinuousLinearMap.smooth reCLM).comp (φ.apply_smooth i)

lemma apply_im_smooth (φ : HiggsField) (i : Fin 2):
    Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) (imCLM ∘ (fun (x : SpaceTime) =>  (φ x i))) :=
  (ContinuousLinearMap.smooth imCLM).comp (φ.apply_smooth i)

lemma normSq_smooth (φ : HiggsField) : Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) φ.normSq := by
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

lemma potential_smooth (φ : HiggsField) (μSq lambda : ℝ) :
    Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) (fun x => φ.potential μSq lambda x) := by
  simp only [potential, normSq, neg_mul]
  exact (smooth_const.smul φ.normSq_smooth).neg.add
    ((smooth_const.smul φ.normSq_smooth).smul φ.normSq_smooth)

/-!

## Constant higgs fields

-/

/-- A higgs field is constant if it is equal for all `x` `y` in `spaceTime`. -/
def IsConst (Φ : HiggsField) : Prop := ∀ x y, Φ x = Φ y

lemma isConst_of_higgsVec (φ : HiggsVec) : φ.toField.IsConst := by
  intro x _
  simp [HiggsVec.toField]

lemma isConst_iff_of_higgsVec (Φ : HiggsField) : Φ.IsConst ↔ ∃ (φ : HiggsVec), Φ = φ.toField :=
  Iff.intro (fun h ↦ ⟨Φ 0, by ext x y; rw [← h x 0]; rfl⟩) (fun ⟨φ, hφ⟩ x y ↦ by subst hφ; rfl)

lemma normSq_of_higgsVec (φ : HiggsVec) : φ.toField.normSq = fun x => (norm φ) ^ 2 := by
  funext x
  simp [normSq, HiggsVec.toField]

lemma potential_of_higgsVec (φ : HiggsVec) (μSq lambda : ℝ) :
    φ.toField.potential μSq lambda = fun _ => HiggsVec.potential μSq lambda φ := by
  simp [HiggsVec.potential]
  unfold potential
  rw [normSq_of_higgsVec]
  ring_nf

end HiggsField
end
end StandardModel
