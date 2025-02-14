/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import PhysLean.Meta.TODO.Basic
/-!
# Space time

This file introduce 4d Minkowski spacetime.

-/

noncomputable section

TODO "SpaceTime should be refactored into a structure, or similar, to prevent casting."

/-- The space-time -/
def SpaceTime : Type := Fin 4 → ℝ

/-- Give spacetime the structure of an additive commutative monoid. -/
instance : AddCommMonoid SpaceTime := Pi.addCommMonoid

/-- Give spacetime the structure of a module over the reals. -/
instance : Module ℝ SpaceTime := Pi.module _ _ _

/-- The instance of a normed group on spacetime defined via the Euclidean norm. -/
instance euclideanNormedAddCommGroup : NormedAddCommGroup SpaceTime := Pi.normedAddCommGroup

/-- The Euclidean norm-structure on space time. This is used to give it a smooth structure. -/
instance euclideanNormedSpace : NormedSpace ℝ SpaceTime := Pi.normedSpace

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The space part of spacetime. -/
@[simp]
def space (x : SpaceTime) : EuclideanSpace ℝ (Fin 3) := ![x 1, x 2, x 3]

/-- The structure of a smooth manifold on spacetime. -/
def asSmoothManifold : ModelWithCorners ℝ SpaceTime SpaceTime := 𝓘(ℝ, SpaceTime)

/-- The instance of a `ChartedSpace` on `SpaceTime`. -/
instance : ChartedSpace SpaceTime SpaceTime := chartedSpaceSelf SpaceTime

/-- The standard basis for spacetime. -/
def stdBasis : Basis (Fin 4) ℝ SpaceTime := Pi.basisFun ℝ (Fin 4)

lemma stdBasis_apply (μ ν : Fin 4) : stdBasis μ ν = if μ = ν then 1 else 0 := by
  erw [stdBasis, Pi.basisFun_apply, Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

lemma stdBasis_not_eq {μ ν : Fin 4} (h : μ ≠ ν) : stdBasis μ ν = 0 := by
  rw [stdBasis_apply]
  exact if_neg h

/-- For space-time,`stdBasis 0` is equal to `![1, 0, 0, 0] `. -/
lemma stdBasis_0 : stdBasis 0 = ![1, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [stdBasis_apply]

/-- For space-time,`stdBasis 1` is equal to `![0, 1, 0, 0] `. -/
lemma stdBasis_1 : stdBasis 1 = ![0, 1, 0, 0] := by
  funext i
  fin_cases i <;> simp [stdBasis_apply]

/-- For space-time,`stdBasis 2` is equal to `![0, 0, 1, 0] `. -/
lemma stdBasis_2 : stdBasis 2 = ![0, 0, 1, 0] := by
  funext i
  fin_cases i <;> simp [stdBasis_apply]

/-- For space-time,`stdBasis 3` is equal to `![0, 0, 0, 1] `. -/
lemma stdBasis_3 : stdBasis 3 = ![0, 0, 0, 1] := by
  funext i
  fin_cases i <;> simp [stdBasis_apply]

lemma stdBasis_mulVec (μ ν : Fin 4) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    (Λ *ᵥ stdBasis μ) ν = Λ ν μ := by
  rw [mulVec, dotProduct, Fintype.sum_eq_single μ, stdBasis_apply]
  · simp only [↓reduceIte, mul_one]
  · intro x h
    rw [stdBasis_apply, if_neg (Ne.symm h)]
    exact CommMonoidWithZero.mul_zero (Λ ν x)

/-- The explicit expansion of a point in spacetime as `![x 0, x 1, x 2, x 3]`. -/
lemma explicit (x : SpaceTime) : x = ![x 0, x 1, x 2, x 3] := by
  funext i
  fin_cases i <;> rfl

@[simp]
lemma add_apply (x y : SpaceTime) (i : Fin 4) : (x + y) i = x i + y i := rfl

@[simp]
lemma smul_apply (x : SpaceTime) (a : ℝ) (i : Fin 4) : (a • x) i = a * x i := rfl

end SpaceTime

end
