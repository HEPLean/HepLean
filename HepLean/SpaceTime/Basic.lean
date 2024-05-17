/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Space time

This file introduce 4d Minkowski spacetime.

-/

noncomputable section

/-- The space-time -/
def spaceTime : Type := Fin 4 → ℝ

/-- Give spacetime the structure of an additive commutative monoid. -/
instance : AddCommMonoid spaceTime := Pi.addCommMonoid


/-- Give spacetime the structure of a module over the reals. -/
instance : Module ℝ spaceTime := Pi.module _ _ _

instance euclideanNormedAddCommGroup : NormedAddCommGroup spaceTime := Pi.normedAddCommGroup

instance euclideanNormedSpace : NormedSpace ℝ spaceTime := Pi.normedSpace


namespace spaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The space part of spacetime. -/
@[simp]
def space (x : spaceTime) : EuclideanSpace ℝ (Fin 3) := ![x 1, x 2, x 3]

/-- The structure of a smooth manifold on spacetime. -/
def asSmoothManifold : ModelWithCorners ℝ spaceTime spaceTime := 𝓘(ℝ, spaceTime)

instance : ChartedSpace spaceTime spaceTime := chartedSpaceSelf spaceTime

/-- The standard basis for spacetime. -/
def stdBasis : Basis (Fin 4) ℝ spaceTime := Pi.basisFun ℝ (Fin 4)

lemma stdBasis_apply (μ ν : Fin 4) : stdBasis μ ν = if μ = ν then 1 else 0 := by
  erw [stdBasis, Pi.basisFun_apply, LinearMap.stdBasis_apply']

lemma stdBasis_not_eq {μ ν : Fin 4} (h : μ ≠ ν) : stdBasis μ ν = 0 := by
  rw [stdBasis_apply]
  exact if_neg h

lemma stdBasis_0 : stdBasis 0 = ![1, 0, 0, 0] := by
  funext i
  fin_cases i
    <;> simp [stdBasis_apply]

lemma stdBasis_1 : stdBasis 1 = ![0, 1, 0, 0] := by
  funext i
  fin_cases i
    <;> simp [stdBasis_apply]

lemma stdBasis_2 : stdBasis 2 = ![0, 0, 1, 0] := by
  funext i
  fin_cases i
    <;> simp [stdBasis_apply]

lemma stdBasis_3 : stdBasis 3 = ![0, 0, 0, 1] := by
  funext i
  fin_cases i
    <;> simp [stdBasis_apply]

lemma stdBasis_mulVec (μ ν : Fin 4) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    (Λ *ᵥ stdBasis μ) ν = Λ ν μ := by
  rw [mulVec, dotProduct, Fintype.sum_eq_single μ, stdBasis_apply]
  simp only [↓reduceIte, mul_one]
  intro x h
  rw [stdBasis_apply, if_neg (Ne.symm h)]
  simp

lemma explicit (x : spaceTime) : x = ![x 0, x 1, x 2, x 3] := by
  funext i
  fin_cases i <;> rfl


end spaceTime

end
