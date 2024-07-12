/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.Polyrith
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Product
/-!

# The Higgs field

This file defines the basic properties for the Higgs field in the standard model.

## References

- We use conventions given in: [Review of Particle Physics, PDG][ParticleDataGroup:2018ovx]

-/

namespace StandardModel
noncomputable section

open Manifold
open Matrix
open Complex
open ComplexConjugate
open SpaceTime

/-!

## The definition of the Higgs vector space.

In other words, the target space of the Higgs field.
-/

/-- The complex vector space in which the Higgs field takes values. -/
abbrev HiggsVec := EuclideanSpace ℂ (Fin 2)

namespace HiggsVec

/-- The continuous linear map from the vector space `HiggsVec` to `(Fin 2 → ℂ)` achieved by
casting vectors. -/
def toFin2ℂ : HiggsVec →L[ℝ] (Fin 2 → ℂ) where
  toFun x := x
  map_add' x y := by simp
  map_smul' a x := by simp

/-- The map `toFin2ℂ` is smooth. -/
lemma smooth_toFin2ℂ : Smooth 𝓘(ℝ, HiggsVec) 𝓘(ℝ, Fin 2 → ℂ) toFin2ℂ :=
  ContinuousLinearMap.smooth toFin2ℂ

/-- An orthonormal basis of `HiggsVec`. -/
def orthonormBasis : OrthonormalBasis (Fin 2) ℂ HiggsVec :=
  EuclideanSpace.basisFun (Fin 2) ℂ

end HiggsVec

/-!

## Definition of the Higgs Field

We also define the Higgs bundle.
-/

/-! TODO: Make `HiggsBundle` an associated bundle. -/
/-- The trivial vector bundle 𝓡² × ℂ². -/
abbrev HiggsBundle := Bundle.Trivial SpaceTime HiggsVec

instance : SmoothVectorBundle HiggsVec HiggsBundle SpaceTime.asSmoothManifold :=
  Bundle.Trivial.smoothVectorBundle HiggsVec 𝓘(ℝ, SpaceTime)

/-- A Higgs field is a smooth section of the Higgs bundle. -/
abbrev HiggsField : Type := SmoothSection SpaceTime.asSmoothManifold HiggsVec HiggsBundle

instance : NormedAddCommGroup (Fin 2 → ℂ) := by
  exact Pi.normedAddCommGroup

/-- Given a vector in `HiggsVec` the constant Higgs field with value equal to that
section. -/
def HiggsVec.toField (φ : HiggsVec) : HiggsField where
  toFun := fun _ ↦ φ
  contMDiff_toFun := by
    intro x
    rw [Bundle.contMDiffAt_section]
    exact smoothAt_const

namespace HiggsField
open HiggsVec

/-!

## Relation to `HiggsVec`

-/

/-- Given a `HiggsField`, the corresponding map from `SpaceTime` to `HiggsVec`. -/
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

lemma toFin2ℂ_comp_toHiggsVec (φ : HiggsField) :
    toFin2ℂ ∘ φ.toHiggsVec = φ := rfl

/-!

## Smoothness properties of components

-/

lemma toVec_smooth (φ : HiggsField) : Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, Fin 2 → ℂ) φ :=
  smooth_toFin2ℂ.comp φ.toHiggsVec_smooth

lemma apply_smooth (φ : HiggsField) :
    ∀ i, Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℂ) (fun (x : SpaceTime) => (φ x i)) :=
  (smooth_pi_space).mp (φ.toVec_smooth)

lemma apply_re_smooth (φ : HiggsField) (i : Fin 2) :
    Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) (reCLM ∘ (fun (x : SpaceTime) => (φ x i))) :=
  (ContinuousLinearMap.smooth reCLM).comp (φ.apply_smooth i)

lemma apply_im_smooth (φ : HiggsField) (i : Fin 2) :
    Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) (imCLM ∘ (fun (x : SpaceTime) => (φ x i))) :=
  (ContinuousLinearMap.smooth imCLM).comp (φ.apply_smooth i)

/-!

## Constant Higgs fields

-/

/-- A Higgs field is constant if it is equal for all `x` `y` in `spaceTime`. -/
def IsConst (Φ : HiggsField) : Prop := ∀ x y, Φ x = Φ y

lemma isConst_of_higgsVec (φ : HiggsVec) : φ.toField.IsConst := by
  intro x _
  simp [HiggsVec.toField]

lemma isConst_iff_of_higgsVec (Φ : HiggsField) : Φ.IsConst ↔ ∃ (φ : HiggsVec), Φ = φ.toField :=
  Iff.intro (fun h ↦ ⟨Φ 0, by ext x y; rw [← h x 0]; rfl⟩) (fun ⟨φ, hφ⟩ x y ↦ by subst hφ; rfl)

end HiggsField

end
end StandardModel
