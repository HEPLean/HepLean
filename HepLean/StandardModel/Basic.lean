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
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
/-!
# The Standard Model

This file defines the basic properties of the standard model in particle physics.

## TODO

- Change the gauge group to a quotient of SU(3) x SU(2) x U(1) by a subgroup of ℤ₆.
(see e.g. pg 97 of  http://www.damtp.cam.ac.uk/user/tong/gaugetheory/gt.pdf)

-/
universe v u
namespace StandardModel

open Manifold
open Matrix
open Complex
open ComplexConjugate

noncomputable section spaceTime

/-- The space-time -/
def spaceTime : Type := Fin 4 → ℝ

/-- Give spacetime the structure of an additive commutative monoid. -/
instance : AddCommMonoid spaceTime := Pi.addCommMonoid

/-- Give spacetime the structure of a module over the reals. -/
instance : Module ℝ spaceTime := Pi.module _ _ _

instance euclideanNormedAddCommGroup : NormedAddCommGroup spaceTime := Pi.normedAddCommGroup

instance euclideanNormedSpace : NormedSpace ℝ spaceTime := Pi.normedSpace


namespace spaceTime

def asSmoothManifold : ModelWithCorners ℝ spaceTime spaceTime := 𝓘(ℝ, spaceTime)

@[simp]
def η : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1]]

lemma η_symmetric (μ ν : Fin 4) : η μ ν = η ν μ := by
  fin_cases μ <;>
    fin_cases ν <;>
    simp only [η, Fin.zero_eta, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.empty_val', Matrix.head_cons,
      Matrix.head_fin_const, Matrix.head_cons, Matrix.vecCons_const, Fin.mk_one, Fin.mk_one]

@[simps!]
def linearMapForSpaceTime (x : spaceTime) : spaceTime →ₗ[ℝ] ℝ where
  toFun y := x ⬝ᵥ (η *ᵥ y)
  map_add' y z := by
    simp only
    rw [mulVec_add, dotProduct_add]
  map_smul' c y := by
    simp only
    rw [mulVec_smul, dotProduct_smul]
    rfl

def ηLin : LinearMap.BilinForm ℝ spaceTime where
  toFun x := linearMapForSpaceTime x
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp only [linearMapForSpaceTime_apply, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    simp only [linearMapForSpaceTime_apply, RingHom.id_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [smul_dotProduct]
    rfl

def quadraticForm : QuadraticForm ℝ spaceTime := ηLin.toQuadraticForm

def lorentzGroup : Subgroup (GeneralLinearGroup (Fin 4) ℝ) where
  carrier := {Λ | ∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y}
  mul_mem' {a b} := by
    intros ha hb x y
    simp
    rw [← mulVec_mulVec, ← mulVec_mulVec, ha, hb]
  one_mem' := by
    intros x y
    simp
  inv_mem' {a} := by
    intros ha x y
    simp only [coe_units_inv, ← ha ((a.1⁻¹) *ᵥ x) ((a.1⁻¹) *ᵥ y), mulVec_mulVec]
    have hx : (a.1 * (a.1)⁻¹) = 1 := by
      simp only [@Units.mul_eq_one_iff_inv_eq, coe_units_inv]
    simp [hx]


abbrev cliffordAlgebra := CliffordAlgebra quadraticForm

end spaceTime

end spaceTime

/-- The global gauge group of the standard model. TODO: Generalize to quotient. -/
abbrev gaugeGroup : Type :=
  specialUnitaryGroup (Fin 3) ℂ × specialUnitaryGroup (Fin 2) ℂ × unitary ℂ

end StandardModel
