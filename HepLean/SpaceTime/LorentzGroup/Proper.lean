/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.KleinFour
/-!
# The Proper Lorentz Group

We define the give a series of lemmas related to the determinant of the lorentz group.

-/


noncomputable section

namespace spaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

namespace lorentzGroup

/-- The determinant of a member of the lorentz group is `1` or `-1`. -/
lemma det_eq_one_or_neg_one (Λ : lorentzGroup) : Λ.1.1.det = 1 ∨ Λ.1.1.det = -1 := by
  simpa [← sq, det_one, det_mul, det_mul, det_mul, det_transpose, det_η] using
    (congrArg det ((PreservesηLin.iff_matrix' Λ.1).mp ((mem_iff Λ.1).mp Λ.2)))

local notation  "ℤ₂" => Multiplicative (ZMod 2)

instance : TopologicalSpace ℤ₂ := instTopologicalSpaceFin

instance : DiscreteTopology ℤ₂ := by
  exact forall_open_iff_discrete.mp fun _ => trivial

instance : TopologicalGroup ℤ₂ := TopologicalGroup.mk

/-- A continuous function from `({-1, 1} : Set ℝ)` to `ℤ₂`. -/
@[simps!]
def coeForℤ₂ :  C(({-1, 1} : Set ℝ), ℤ₂) where
  toFun x := if x = ⟨1, by simp⟩ then (Additive.toMul 0) else (Additive.toMul (1 : ZMod 2))
  continuous_toFun := by
    haveI : DiscreteTopology ({-1, 1} : Set ℝ) := discrete_of_t1_of_finite
    exact continuous_of_discreteTopology

/-- The continuous map taking a lorentz matrix to its determinant. -/
def detContinuous :  C(lorentzGroup, ℤ₂) :=
  ContinuousMap.comp  coeForℤ₂ {
    toFun := fun Λ => ⟨Λ.1.1.det, Or.symm (lorentzGroup.det_eq_one_or_neg_one _)⟩,
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      exact Continuous.matrix_det $
        Continuous.comp' Units.continuous_val continuous_subtype_val}

lemma detContinuous_eq_iff_det_eq (Λ Λ' : lorentzGroup) :
    detContinuous Λ = detContinuous Λ' ↔ Λ.1.1.det = Λ'.1.1.det := by
  apply Iff.intro
  intro h
  simp [detContinuous] at h
  cases'  det_eq_one_or_neg_one Λ with h1 h1
    <;> cases'  det_eq_one_or_neg_one Λ' with h2 h2
    <;> simp_all [h1, h2, h]
  rw [← toMul_zero, @Equiv.apply_eq_iff_eq] at h
  change (0 : Fin 2) = (1 : Fin 2) at h
  simp only [Fin.isValue, zero_ne_one] at h
  nth_rewrite 2 [← toMul_zero] at h
  rw [@Equiv.apply_eq_iff_eq] at h
  change (1 : Fin 2) = (0 : Fin 2) at h
  simp [Fin.isValue, zero_ne_one] at h
  intro h
  simp [detContinuous, h]


/-- The representation taking a lorentz matrix to its determinant. -/
@[simps!]
def detRep : lorentzGroup →* ℤ₂ where
  toFun Λ := detContinuous Λ
  map_one' := by
    simp [detContinuous]
  map_mul' := by
    intro Λ1 Λ2
    simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul, det_mul, toMul_zero,
      mul_ite, mul_one, ite_mul, one_mul]
    cases' (det_eq_one_or_neg_one Λ1) with h1 h1
      <;> cases' (det_eq_one_or_neg_one Λ2) with h2 h2
      <;> simp [h1, h2, detContinuous]
    rfl

lemma detRep_continuous : Continuous detRep := detContinuous.2

lemma det_on_connected_component {Λ Λ'  : lorentzGroup} (h : Λ' ∈ connectedComponent Λ) :
    Λ.1.1.det = Λ'.1.1.det := by
  obtain ⟨s, hs, hΛ'⟩ := h
  let f : ContinuousMap s ℤ₂ := ContinuousMap.restrict s detContinuous
  haveI : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs.1
  simpa [f, detContinuous_eq_iff_det_eq] using
    (@IsPreconnected.subsingleton ℤ₂ _ _ _ (isPreconnected_range f.2))
    (Set.mem_range_self ⟨Λ, hs.2⟩)  (Set.mem_range_self ⟨Λ', hΛ'⟩)

lemma det_of_joined {Λ Λ' : lorentzGroup} (h : Joined Λ Λ') : Λ.1.1.det = Λ'.1.1.det :=
  det_on_connected_component $ pathComponent_subset_component _ h

/-- A Lorentz Matrix is proper if its determinant is 1. -/
@[simp]
def IsProper (Λ : lorentzGroup) : Prop := Λ.1.1.det = 1

instance : DecidablePred IsProper := by
  intro Λ
  apply Real.decidableEq

lemma IsProper_iff (Λ : lorentzGroup) : IsProper Λ ↔ detRep Λ = 1 := by
  rw [show 1 = detRep 1 by simp]
  rw [detRep_apply, detRep_apply, detContinuous_eq_iff_det_eq]
  simp only [IsProper, OneMemClass.coe_one, Units.val_one, det_one]


end lorentzGroup

end spaceTime
end
