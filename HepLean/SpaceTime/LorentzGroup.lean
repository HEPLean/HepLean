/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Metric
/-!
# The Lorentz Group

We define the Lorentz group, and show it is a closed subgroup General Linear Group.

## TODO

- Show that the Lorentz is a Lie group.
- Define the proper Lorentz group.
- Define the restricted Lorentz group, and prove it is connected.

-/

noncomputable section

namespace spaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The Lorentz group as a subgroup of the general linear group over the reals. -/
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

/-- The Lorentz group is a topological group with the subset topology. -/
instance : TopologicalGroup lorentzGroup :=
  Subgroup.instTopologicalGroupSubtypeMem lorentzGroup

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

lemma mem_lorentzGroup_iff'' (Λ : GL (Fin 4) ℝ) :
    Λ ∈ lorentzGroup ↔ η * Λ.1ᵀ * η * Λ.1 = 1 := by
  rw [mem_lorentzGroup_iff', ηLin_matrix_eq_identity_iff (η * Λ.1ᵀ * η * Λ.1)]
  apply Iff.intro
  · simp_all only [ηLin_apply_apply, implies_true, iff_true, one_mulVec]
  · simp_all only [ηLin_apply_apply, mulVec_mulVec, implies_true]

lemma det_lorentzGroup (Λ : lorentzGroup) : Λ.1.1.det = 1 ∨ Λ.1.1.det = -1 := by
  simpa [← sq, det_one, det_mul, det_mul, det_mul, det_transpose, det_η] using
    (congrArg det ((mem_lorentzGroup_iff'' Λ.1).mp Λ.2))

/-- A continous map from `GL (Fin 4) ℝ` to  `Matrix (Fin 4) (Fin 4) ℝ` for which the Lorentz
group is the kernal. -/
def lorentzMap (Λ : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ := η * Λ.1ᵀ * η * Λ.1

lemma lorentzMap_continuous : Continuous lorentzMap := by
  apply Continuous.mul _ Units.continuous_val
  apply Continuous.mul _ continuous_const
  exact Continuous.mul continuous_const (Continuous.matrix_transpose (Units.continuous_val))

lemma lorentzGroup_kernal : lorentzGroup = lorentzMap ⁻¹' {1} := by
  ext Λ
  erw [mem_lorentzGroup_iff'' Λ]
  rfl

theorem lorentzGroup_isClosed : IsClosed (lorentzGroup : Set (GeneralLinearGroup (Fin 4) ℝ)) := by
  rw [lorentzGroup_kernal]
  exact continuous_iff_isClosed.mp lorentzMap_continuous {1} isClosed_singleton


end spaceTime

end
