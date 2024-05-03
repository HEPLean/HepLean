/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.RepresentationTheory.Basic
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

/-- The trivial vector bundle 𝓡² × ℂ². (TODO: Make associated bundle.) -/
abbrev higgsBundle := Bundle.Trivial spaceTime (Fin 2 → ℂ)

instance : SmoothVectorBundle (Fin 2 → ℂ) higgsBundle (𝓡 4)  :=
  Bundle.Trivial.smoothVectorBundle (Fin 2 → ℂ) 𝓘(ℝ, spaceTime)

/-- A higgs field is a smooth section of the higgs bundle. -/
abbrev higgsFields : Type := SmoothSection (𝓡 4) (Fin 2 → ℂ) higgsBundle

@[simps!]
noncomputable def higgsRepMap (g : guageGroup) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun S :=  (g.2 ^ 3) • (g.1.1 *ᵥ S)
  map_add' S T := by
    simp [Matrix.mulVec_add, smul_add]
  map_smul' a S := by
    simp [Matrix.mulVec_smul]
    exact smul_comm  _ _ _


/-- The representation of the SM guage group acting on `ℂ²`. -/
noncomputable def higgsRep : Representation ℂ guageGroup (Fin 2 → ℂ) where
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



namespace higgsFields


/-- A higgs field is constant if it is equal for all `x` `y` in `spaceTime`. -/
def isConst (Φ : higgsFields) : Prop := ∀ x y, Φ x = Φ y

/-- Given a vector `ℂ²` the constant higgs field with value equal to that
section. -/
noncomputable def const (φ : Fin 2 → ℂ) : higgsFields where
  toFun := fun _ => φ
  contMDiff_toFun := by
    intro x
    rw [Bundle.contMDiffAt_section]
    exact smoothAt_const


lemma const_isConst (φ : Fin 2 → ℂ) : (const φ).isConst := by
  intro x _
  simp [const]

lemma isConst_iff_exists_const (Φ : higgsFields) : Φ.isConst ↔ ∃ φ, Φ = const φ := by
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

-- rename
def rotateMatrix (φ : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![conj φ 0 / √(normSq (φ 0) + normSq (φ 1)), conj φ 1 / √(normSq (φ 0) + normSq (φ 1))],
  ![ - φ 1/ √(normSq (φ 0) + normSq (φ 1)), φ 0 / √(normSq (φ 0) + normSq (φ 1))]]

lemma rotateMatrix_det {φ : Fin 2 → ℂ} (hφ : φ ≠ 0) :
    det (rotateMatrix φ) = 1 := by
  simp [rotateMatrix, det_fin_two]
  simp [div_mul_div_comm]
  rw [← normSq_eq_conj_mul_self, ← normSq_eq_conj_mul_self]
  rw [div_sub_div_same]
  simp
  have h1 : 0 ≤ (normSq (φ 0)) + (normSq (φ 1)) :=
    add_nonneg (normSq_nonneg _) (normSq_nonneg _)
  rw [← ofReal_mul]
  rw [Real.mul_self_sqrt h1, ofReal_add]
  refine div_self ?_

  sorry

theorem higgs_rotate (φ :  Fin 2 → ℂ) : ∃ (g : guageGroup) (v : ℝ),
    (higgsRep g) φ = ![(v : ℂ), 0] := by
  sorry


end higgsFields
end
end StandardModel
