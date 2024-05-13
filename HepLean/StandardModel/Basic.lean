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
  simp
  intro x h
  rw [stdBasis_apply, if_neg (Ne.symm h)]
  simp



lemma explicit (x : spaceTime) : x = ![x 0, x 1, x 2, x 3] := by
  funext i
  fin_cases i <;> rfl



def η : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![1, 0, 0, 0], ![0, -1, 0, 0], ![0, 0, -1, 0], ![0, 0, 0, -1]]

lemma η_off_diagonal {μ ν : Fin 4} (h : μ ≠ ν) : η μ ν = 0 := by
  fin_cases μ <;>
    fin_cases ν <;>
      simp_all [η, Fin.zero_eta, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.empty_val', Matrix.head_cons,
      Matrix.head_fin_const, Matrix.head_cons, Matrix.vecCons_const, Fin.mk_one, Fin.mk_one,
      vecHead, vecTail, Function.comp_apply]

lemma η_symmetric (μ ν : Fin 4) : η μ ν = η ν μ := by
  by_cases h : μ = ν
  rw [h]
  rw [η_off_diagonal h]
  refine (η_off_diagonal ?_).symm
  exact fun a => h (id a.symm)

lemma η_transpose : η.transpose = η := by
  funext μ ν
  rw [transpose_apply, η_symmetric]

lemma η_sq : η * η = 1 := by
  funext μ ν
  rw [mul_apply, Fin.sum_univ_four]
  fin_cases μ <;> fin_cases ν <;>
     simp [η, Fin.zero_eta, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.empty_val', Matrix.head_cons,
      Matrix.head_fin_const, Matrix.head_cons, Matrix.vecCons_const, Fin.mk_one, Fin.mk_one,
      vecHead, vecTail, Function.comp_apply]



lemma η_mulVec (x : spaceTime) : η *ᵥ x = ![x 0, -x 1, -x 2, -x 3] := by
  rw [explicit x]
  rw [η]
  funext i
  rw [mulVec, dotProduct, Fin.sum_univ_four]
  fin_cases i <;>
    simp [η, Fin.zero_eta, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.empty_val', Matrix.head_cons,
      Matrix.head_fin_const, Matrix.head_cons, Matrix.vecCons_const, Fin.mk_one, Fin.mk_one,
      vecHead, vecTail, Function.comp_apply]

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

@[simps!]
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

lemma ηLin_expand (x y : spaceTime) : ηLin x y = x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3 := by
  rw [ηLin]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, linearMapForSpaceTime_apply, Fin.isValue]
  erw [η_mulVec]
  nth_rewrite 1 [explicit x]
  simp only [dotProduct, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Fin.sum_univ_four,
    cons_val_zero, cons_val_one, head_cons, mul_neg, cons_val_two, tail_cons, cons_val_three]
  ring

lemma ηLin_symm (x y : spaceTime) : ηLin x y = ηLin y x := by
  rw [ηLin_expand, ηLin_expand]
  ring

lemma ηLin_stdBasis_apply (μ : Fin 4) (x : spaceTime) : ηLin (stdBasis μ) x = η μ μ * x μ := by
  rw [ηLin_expand]
  fin_cases μ
   <;> simp [stdBasis_0, stdBasis_1, stdBasis_2, stdBasis_3, η]


lemma ηLin_η_stdBasis (μ ν : Fin 4) : ηLin (stdBasis μ) (stdBasis ν) = η μ ν := by
  rw [ηLin_stdBasis_apply]
  by_cases h : μ = ν
  rw [stdBasis_apply]
  subst h
  simp
  rw [stdBasis_not_eq, η_off_diagonal h]
  simp
  exact fun a => h (id a.symm)

lemma ηLin_mulVec_left (x y : spaceTime) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    ηLin (Λ *ᵥ x) y = ηLin x ((η * Λᵀ * η) *ᵥ y) := by
  simp only [ηLin_apply_apply, mulVec_mulVec]
  rw [(vecMul_transpose Λ x).symm, ← dotProduct_mulVec, mulVec_mulVec]
  rw [← mul_assoc, ← mul_assoc, η_sq, one_mul]

lemma ηLin_mulVec_right (x y : spaceTime) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    ηLin x (Λ *ᵥ y) = ηLin ((η * Λᵀ * η) *ᵥ x) y := by
  rw [ηLin_symm, ηLin_symm ((η * Λᵀ * η) *ᵥ x) _ ]
  exact ηLin_mulVec_left y x Λ

lemma ηLin_matrix_stdBasis (μ ν : Fin 4) (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    ηLin (stdBasis ν) (Λ *ᵥ stdBasis μ)  = η ν ν * Λ ν μ := by
  rw [ηLin_stdBasis_apply, stdBasis_mulVec]

lemma ηLin_matrix_eq_identity_iff (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    Λ = 1 ↔ ∀ (x y : spaceTime), ηLin x y = ηLin x (Λ *ᵥ y) := by
  apply Iff.intro
  intro h
  subst h
  simp
  intro h
  funext μ ν
  have h1 := h (stdBasis μ) (stdBasis ν)
  rw [ηLin_matrix_stdBasis, ηLin_η_stdBasis] at h1
  fin_cases μ <;> fin_cases ν <;>
    simp_all [η, Fin.zero_eta, Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_one,
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.empty_val', Matrix.head_cons,
      Matrix.head_fin_const, Matrix.head_cons, Matrix.vecCons_const, Fin.mk_one, Fin.mk_one,
      vecHead, vecTail, Function.comp_apply]


def quadraticForm : QuadraticForm ℝ spaceTime := ηLin.toQuadraticForm

def lorentzGroup : Subgroup (GeneralLinearGroup (Fin 4) ℝ) where
  carrier := {Λ | ∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y}
  mul_mem' {a b} := by
    intros ha hb x y
    simp only [Units.val_mul, mulVec_mulVec]
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


lemma mem_lorentzGroup_iff (Λ : GeneralLinearGroup (Fin 4) ℝ) :
    Λ ∈ lorentzGroup ↔ ∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y := by
  rfl

lemma mem_lorentzGroup_iff' (Λ : GeneralLinearGroup (Fin 4) ℝ) :
    Λ ∈ lorentzGroup ↔ ∀ (x y : spaceTime), ηLin (x) ((η * Λ.1ᵀ * η * Λ.1) *ᵥ y) = ηLin x y := by
  rw [mem_lorentzGroup_iff]
  apply Iff.intro
  intro h
  intro x y
  have h1 := h x y
  rw [ηLin_mulVec_left, mulVec_mulVec] at h1
  exact h1
  intro h
  intro x y
  rw [ηLin_mulVec_left, mulVec_mulVec]
  exact h x y

lemma mem_lorentzGroup_iff'' (Λ : GeneralLinearGroup (Fin 4) ℝ) :
    Λ ∈ lorentzGroup ↔ η * Λ.1ᵀ * η * Λ.1 = 1 := by
  rw [mem_lorentzGroup_iff', ηLin_matrix_eq_identity_iff (η * Λ.1ᵀ * η * Λ.1)]
  apply Iff.intro
  · simp_all only [ηLin_apply_apply, implies_true, iff_true, one_mulVec]
  · simp_all only [ηLin_apply_apply, mulVec_mulVec, implies_true]

abbrev cliffordAlgebra := CliffordAlgebra quadraticForm

end spaceTime

end spaceTime

/-- The global gauge group of the standard model. TODO: Generalize to quotient. -/
abbrev gaugeGroup : Type :=
  specialUnitaryGroup (Fin 3) ℂ × specialUnitaryGroup (Fin 2) ℂ × unitary ℂ

end StandardModel
