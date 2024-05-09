/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!
# The Standard Model

This file defines the basic properties of the standard model in particle physics.

-/
universe v u
namespace StandardModel

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The space-time (TODO: Change to Minkowski.) -/
abbrev spaceTime := EuclideanSpace ℝ (Fin 4)

/-- The global gauge group of the standard model. -/
abbrev guageGroup : Type := specialUnitaryGroup (Fin 3) ℂ ×
  specialUnitaryGroup (Fin 2) ℂ × unitary ℂ

-- TODO: Move to MathLib.
lemma star_specialUnitary (g : specialUnitaryGroup (Fin 2) ℂ) :
    star g.1 ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hg := mem_specialUnitaryGroup_iff.mp g.prop
  rw [@mem_specialUnitaryGroup_iff]
  apply And.intro
  rw [@mem_unitaryGroup_iff, star_star]
  exact mem_unitaryGroup_iff'.mp hg.1
  rw [star_eq_conjTranspose, det_conjTranspose, hg.2, star_one]

-- TOMOVE
@[simps!]
noncomputable def repU1Map (g : unitary ℂ) : unitaryGroup (Fin 2) ℂ :=
  ⟨g ^ 3 • 1, by
    rw [mem_unitaryGroup_iff, smul_one_mul, show g = ⟨g.1, g.prop⟩ from rfl]
    simp only [SubmonoidClass.mk_pow, Submonoid.mk_smul, star_smul, star_pow, RCLike.star_def,
      star_one]
    rw [smul_smul, ← mul_pow]
    erw [(unitary.mem_iff.mp g.prop).2]
    simp only [one_pow, one_smul]⟩

@[simps!]
noncomputable def repU1 : unitary ℂ →* unitaryGroup (Fin 2) ℂ where
  toFun g := repU1Map g
  map_mul' g h := by
    simp only [repU1Map, Submonoid.mk_mul_mk, mul_smul_one, smul_smul, mul_comm, ← mul_pow]
  map_one' := by
    simp only [repU1Map, one_pow, one_smul, Submonoid.mk_eq_one]

@[simps!]
def fundamentalSU2 : specialUnitaryGroup (Fin 2) ℂ →* unitaryGroup (Fin 2) ℂ where
  toFun g := ⟨g.1, g.prop.1⟩
  map_mul' _ _ := Subtype.ext rfl
  map_one' := Subtype.ext rfl

lemma repU1_fundamentalSU2_commute (u1 : unitary ℂ) (g : specialUnitaryGroup (Fin 2) ℂ) :
    repU1 u1 * fundamentalSU2 g = fundamentalSU2 g * repU1 u1 := by
  apply Subtype.ext
  simp

noncomputable def higgsRepUnitary : guageGroup →* unitaryGroup (Fin 2) ℂ where
  toFun g := repU1 g.2.2 * fundamentalSU2 g.2.1
  map_mul'  := by
    intro ⟨_, a2, a3⟩ ⟨_, b2, b3⟩
    change repU1 (a3 * b3) *  fundamentalSU2 (a2 * b2) = _
    rw [repU1.map_mul, fundamentalSU2.map_mul]
    rw [mul_assoc, mul_assoc, ← mul_assoc (repU1 b3) _ _, repU1_fundamentalSU2_commute]
    repeat rw [mul_assoc]
  map_one' := by
    simp

end StandardModel
