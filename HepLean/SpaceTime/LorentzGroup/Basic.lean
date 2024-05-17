/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Metric
import HepLean.SpaceTime.FourVelocity
import Mathlib.GroupTheory.SpecificGroups.KleinFour
/-!
# The Lorentz Group

We define the Lorentz group.

## TODO

- Show that the Lorentz is a Lie group.
- Prove that the restricted Lorentz group is equivalent to the connected component of the
identity.
- Define the continuous maps from `ℝ³` to `restrictedLorentzGroup` defining boosts.

## References

- http://home.ku.edu.tr/~amostafazadeh/phys517_518/phys517_2016f/Handouts/A_Jaffi_Lorentz_Group.pdf

-/


noncomputable section

namespace spaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- We say a matrix `Λ` preserves `ηLin` if for all `x` and `y`,
  `ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y`.  -/
def PreservesηLin (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y

namespace PreservesηLin

variable  (Λ : Matrix (Fin 4) (Fin 4) ℝ)

lemma iff_on_right : PreservesηLin Λ ↔
    ∀ (x y : spaceTime), ηLin x ((η * Λᵀ * η * Λ) *ᵥ y) = ηLin x y := by
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

lemma iff_matrix : PreservesηLin Λ ↔ η * Λᵀ * η * Λ = 1  := by
  rw [iff_on_right, ηLin_matrix_eq_identity_iff (η * Λᵀ * η * Λ)]
  apply Iff.intro
  · simp_all  [ηLin, implies_true, iff_true, one_mulVec]
  · simp_all only [ηLin, LinearMap.coe_mk, AddHom.coe_mk, linearMapForSpaceTime_apply,
    mulVec_mulVec, implies_true]

lemma iff_matrix' : PreservesηLin Λ ↔ Λ * (η * Λᵀ * η) = 1  := by
  rw [iff_matrix]
  apply Iff.intro
  intro h
  exact mul_eq_one_comm.mp h
  intro h
  exact mul_eq_one_comm.mp h

lemma iff_transpose : PreservesηLin Λ ↔ PreservesηLin Λᵀ := by
  apply Iff.intro
  intro h
  have h1 := congrArg transpose ((iff_matrix Λ).mp h)
  rw [transpose_mul, transpose_mul, transpose_mul, η_transpose,
    ← mul_assoc, transpose_one] at h1
  rw [iff_matrix' Λ.transpose, ← h1]
  repeat rw [← mul_assoc]
  intro h
  have h1 := congrArg transpose ((iff_matrix Λ.transpose).mp h)
  rw [transpose_mul, transpose_mul, transpose_mul, η_transpose,
    ← mul_assoc, transpose_one, transpose_transpose] at h1
  rw [iff_matrix', ← h1]
  repeat rw [← mul_assoc]

/-- The lift of a matrix which preserves `ηLin` to an invertible matrix. -/
def liftGL {Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : PreservesηLin Λ) : GL (Fin 4) ℝ :=
  ⟨Λ, η * Λᵀ * η , (iff_matrix' Λ).mp h , (iff_matrix Λ).mp h⟩

end PreservesηLin

/-- The Lorentz group as a subgroup of the general linear group over the reals. -/
def lorentzGroup : Subgroup (GL (Fin 4) ℝ) where
  carrier := {Λ | PreservesηLin Λ}
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

/-- The Lorentz group is a topological group with the subset topology. -/
instance : TopologicalGroup lorentzGroup :=
  Subgroup.instTopologicalGroupSubtypeMem lorentzGroup

@[simps!]
def PreservesηLin.liftLor {Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : PreservesηLin Λ) :
  lorentzGroup := ⟨liftGL h, h⟩

namespace lorentzGroup

lemma mem_iff (Λ : GL (Fin 4) ℝ): Λ ∈ lorentzGroup ↔ PreservesηLin Λ := by
  rfl

/-- The transpose of an matrix in the Lorentz group is an element of the Lorentz group. -/
def transpose (Λ : lorentzGroup) : lorentzGroup :=
  PreservesηLin.liftLor ((PreservesηLin.iff_transpose Λ.1).mp Λ.2)


def kernalMap : C(GL (Fin 4) ℝ, Matrix (Fin 4) (Fin 4) ℝ) where
  toFun Λ := η * Λ.1ᵀ * η * Λ.1
  continuous_toFun := by
    apply Continuous.mul _ Units.continuous_val
    apply Continuous.mul _ continuous_const
    exact Continuous.mul continuous_const (Continuous.matrix_transpose (Units.continuous_val))

lemma kernalMap_kernal_eq_lorentzGroup : lorentzGroup = kernalMap ⁻¹' {1} := by
  ext Λ
  erw [mem_iff Λ, PreservesηLin.iff_matrix]
  rfl

/-- The Lorentz Group is a closed subset of `GL (Fin 4) ℝ`. -/
theorem isClosed_of_GL4 : IsClosed (lorentzGroup : Set (GL (Fin 4) ℝ)) := by
  rw [kernalMap_kernal_eq_lorentzGroup]
  exact continuous_iff_isClosed.mp kernalMap.2 {1} isClosed_singleton

end lorentzGroup

end spaceTime
