/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup.Basic
/-!
# The Proper Lorentz Group

The proper Lorentz group is the subgroup of the Lorentz group with determinant `1`.

We define the give a series of lemmas related to the determinant of the Lorentz group.

-/

noncomputable section

open Matrix
open Complex
open ComplexConjugate

namespace LorentzGroup

open minkowskiMatrix

variable {d : ℕ}

/-- The determinant of a member of the Lorentz group is `1` or `-1`. -/
lemma det_eq_one_or_neg_one (Λ : 𝓛 d) : Λ.1.det = 1 ∨ Λ.1.det = -1 := by
  refine mul_self_eq_one_iff.mp ?_
  simpa only [det_mul, det_dual, det_one] using congrArg det ((mem_iff_self_mul_dual).mp Λ.2)

local notation "ℤ₂" => Multiplicative (ZMod 2)

instance : TopologicalSpace ℤ₂ := instTopologicalSpaceFin

instance : DiscreteTopology ℤ₂ := by
  exact forall_open_iff_discrete.mp fun _ => trivial

instance : TopologicalGroup ℤ₂ := TopologicalGroup.mk

/-- A continuous function from `({-1, 1} : Set ℝ)` to `ℤ₂`. -/
@[simps!]
def coeForℤ₂ : C(({-1, 1} : Set ℝ), ℤ₂) where
  toFun x := if x = ⟨1, Set.mem_insert_of_mem (-1) rfl⟩
    then Additive.toMul 0 else Additive.toMul (1 : ZMod 2)
  continuous_toFun := continuous_of_discreteTopology

/-- The continuous map taking a Lorentz matrix to its determinant. -/
def detContinuous : C(𝓛 d, ℤ₂) :=
  ContinuousMap.comp coeForℤ₂ {
    toFun := fun Λ => ⟨Λ.1.det, Or.symm (LorentzGroup.det_eq_one_or_neg_one _)⟩,
    continuous_toFun := by
      refine Continuous.subtype_mk ?_ _
      exact Continuous.matrix_det $
        Continuous.comp' (continuous_iff_le_induced.mpr fun U a => a) continuous_id'
      }

lemma detContinuous_eq_one (Λ : LorentzGroup d) :
    detContinuous Λ = Additive.toMul 0 ↔ Λ.1.det = 1 := by
  simp only [detContinuous, ContinuousMap.comp_apply, ContinuousMap.coe_mk, coeForℤ₂_apply,
    Subtype.mk.injEq, ite_eq_left_iff, toMul_eq_one]
  simp only [toMul_zero, ite_eq_left_iff, toMul_eq_one]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · by_contra hn
    have h' := h hn
    change (1 : Fin 2) = (0 : Fin 2) at h'
    simp only [Fin.isValue, one_ne_zero] at h'
  · intro h'
    exact False.elim (h' h)

lemma detContinuous_eq_zero (Λ : LorentzGroup d) :
    detContinuous Λ = Additive.toMul (1 : ZMod 2) ↔ Λ.1.det = - 1 := by
  simp only [detContinuous, ContinuousMap.comp_apply, ContinuousMap.coe_mk, coeForℤ₂_apply,
    Subtype.mk.injEq, Nat.reduceAdd]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · by_contra hn
    rw [if_pos] at h
    · change (0 : Fin 2) = (1 : Fin 2) at h
      simp only [Fin.isValue, zero_ne_one] at h
    · cases' det_eq_one_or_neg_one Λ with h2 h2
      · simp_all only [ite_true]
      · simp_all only [not_true_eq_false]
  · rw [if_neg]
    · rfl
    · cases' det_eq_one_or_neg_one Λ with h2 h2
      · rw [h]
        linarith
      · linarith

lemma detContinuous_eq_iff_det_eq (Λ Λ' : LorentzGroup d) :
    detContinuous Λ = detContinuous Λ' ↔ Λ.1.det = Λ'.1.det := by
  cases' det_eq_one_or_neg_one Λ with h1 h1
  · rw [h1, (detContinuous_eq_one Λ).mpr h1]
    cases' det_eq_one_or_neg_one Λ' with h2 h2
    · rw [h2, (detContinuous_eq_one Λ').mpr h2]
      simp only [toMul_zero]
    · rw [h2, (detContinuous_eq_zero Λ').mpr h2]
      erw [Additive.toMul.apply_eq_iff_eq]
      change (0 : Fin 2) = (1 : Fin 2) ↔ _
      simp only [Fin.isValue, zero_ne_one, false_iff]
      linarith
  · rw [h1, (detContinuous_eq_zero Λ).mpr h1]
    cases' det_eq_one_or_neg_one Λ' with h2 h2
    · rw [h2, (detContinuous_eq_one Λ').mpr h2]
      erw [Additive.toMul.apply_eq_iff_eq]
      change (1 : Fin 2) = (0 : Fin 2) ↔ _
      simp only [Fin.isValue, one_ne_zero, false_iff]
      linarith
    · rw [h2, (detContinuous_eq_zero Λ').mpr h2]
      simp only [Nat.reduceAdd]

/-- The representation taking a Lorentz matrix to its determinant. -/
@[simps!]
def detRep : 𝓛 d →* ℤ₂ where
  toFun Λ := detContinuous Λ
  map_one' := by
    simp only [detContinuous, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      lorentzGroupIsGroup_one_coe, det_one, coeForℤ₂_apply, ↓reduceIte]
  map_mul' Λ1 Λ2 := by
    simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul, det_mul, toMul_zero,
      mul_ite, mul_one, ite_mul, one_mul]
    cases' det_eq_one_or_neg_one Λ1 with h1 h1
    · rw [(detContinuous_eq_one Λ1).mpr h1]
      cases' det_eq_one_or_neg_one Λ2 with h2 h2
      · rw [(detContinuous_eq_one Λ2).mpr h2]
        apply (detContinuous_eq_one _).mpr
        simp only [lorentzGroupIsGroup_mul_coe, det_mul, h1, h2, mul_one]
      · rw [(detContinuous_eq_zero Λ2).mpr h2]
        apply (detContinuous_eq_zero _).mpr
        simp only [lorentzGroupIsGroup_mul_coe, det_mul, h1, h2, mul_neg, mul_one]
    · rw [(detContinuous_eq_zero Λ1).mpr h1]
      cases' det_eq_one_or_neg_one Λ2 with h2 h2
      · rw [(detContinuous_eq_one Λ2).mpr h2]
        apply (detContinuous_eq_zero _).mpr
        simp only [lorentzGroupIsGroup_mul_coe, det_mul, h1, h2, mul_one]
      · rw [(detContinuous_eq_zero Λ2).mpr h2]
        apply (detContinuous_eq_one _).mpr
        simp only [lorentzGroupIsGroup_mul_coe, det_mul, h1, h2, mul_neg, mul_one, neg_neg]

lemma detRep_continuous : Continuous (@detRep d) := detContinuous.2

lemma det_on_connected_component {Λ Λ' : LorentzGroup d} (h : Λ' ∈ connectedComponent Λ) :
    Λ.1.det = Λ'.1.det := by
  obtain ⟨s, hs, hΛ'⟩ := h
  let f : ContinuousMap s ℤ₂ := ContinuousMap.restrict s detContinuous
  haveI : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs.1
  simpa [f, detContinuous_eq_iff_det_eq] using
    (@IsPreconnected.subsingleton ℤ₂ _ _ _ (isPreconnected_range f.2))
    (Set.mem_range_self ⟨Λ, hs.2⟩) (Set.mem_range_self ⟨Λ', hΛ'⟩)

lemma detRep_on_connected_component {Λ Λ' : LorentzGroup d} (h : Λ' ∈ connectedComponent Λ) :
    detRep Λ = detRep Λ' := by
  simp only [detRep_apply, detContinuous, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    coeForℤ₂_apply, Subtype.mk.injEq]
  rw [det_on_connected_component h]

lemma det_of_joined {Λ Λ' : LorentzGroup d} (h : Joined Λ Λ') : Λ.1.det = Λ'.1.det :=
  det_on_connected_component $ pathComponent_subset_component _ h

/-- A Lorentz Matrix is proper if its determinant is 1. -/
@[simp]
def IsProper (Λ : LorentzGroup d) : Prop := Λ.1.det = 1

instance : DecidablePred (@IsProper d) := by
  intro Λ
  apply Real.decidableEq

lemma IsProper_iff (Λ : LorentzGroup d) : IsProper Λ ↔ detRep Λ = 1 := by
  rw [show 1 = detRep 1 from Eq.symm (MonoidHom.map_one detRep), detRep_apply, detRep_apply,
    detContinuous_eq_iff_det_eq]
  simp only [IsProper, lorentzGroupIsGroup_one_coe, det_one]

lemma id_IsProper : @IsProper d 1 := by
  simp [IsProper]

lemma isProper_on_connected_component {Λ Λ' : LorentzGroup d} (h : Λ' ∈ connectedComponent Λ) :
    IsProper Λ ↔ IsProper Λ' := by
  simp only [IsProper]
  rw [det_on_connected_component h]

end LorentzGroup

end
