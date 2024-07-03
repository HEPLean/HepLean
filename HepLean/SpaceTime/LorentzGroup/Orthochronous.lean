/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.NormOne
import HepLean.SpaceTime.LorentzGroup.Proper
/-!
# The Orthochronous Lorentz Group

We define the give a series of lemmas related to the orthochronous property of lorentz
matrices.

## TODO

- Prove topological properties.

-/

noncomputable section

open Matrix
open Complex
open ComplexConjugate

namespace LorentzGroup

variable {d : ℕ}
variable (Λ : LorentzGroup d)
open LorentzVector
open minkowskiMetric

/-- A Lorentz transformation is  `orthochronous` if its `0 0` element is non-negative. -/
def IsOrthochronous : Prop := 0 ≤ timeComp Λ

lemma IsOrthochronous_iff_futurePointing :
    IsOrthochronous Λ ↔ (toNormOneLorentzVector Λ) ∈ NormOneLorentzVector.FuturePointing d := by
  simp only [IsOrthochronous, timeComp_eq_toNormOneLorentzVector]
  rw [NormOneLorentzVector.FuturePointing.mem_iff_time_nonneg]

lemma IsOrthochronous_iff_transpose :
    IsOrthochronous Λ ↔ IsOrthochronous (transpose Λ) := by rfl

lemma IsOrthochronous_iff_ge_one :
    IsOrthochronous Λ ↔ 1 ≤ timeComp Λ  := by
  rw [IsOrthochronous_iff_futurePointing, NormOneLorentzVector.FuturePointing.mem_iff,
    NormOneLorentzVector.time_pos_iff]
  simp only [time, toNormOneLorentzVector, timeVec, Fin.isValue]
  erw [Pi.basisFun_apply, mulVec_stdBasis]
  rfl

lemma not_orthochronous_iff_le_neg_one :
    ¬ IsOrthochronous Λ ↔ timeComp Λ ≤ -1 := by
  rw [timeComp, IsOrthochronous_iff_futurePointing, NormOneLorentzVector.FuturePointing.not_mem_iff,
    NormOneLorentzVector.time_nonpos_iff]
  simp only [time, toNormOneLorentzVector, timeVec, Fin.isValue]
  erw [Pi.basisFun_apply, mulVec_stdBasis]

lemma not_orthochronous_iff_le_zero :
    ¬ IsOrthochronous Λ ↔ timeComp Λ ≤ 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  rw [not_orthochronous_iff_le_neg_one] at h
  linarith
  rw [IsOrthochronous_iff_ge_one]
  linarith

/-- The continuous map taking a Lorentz transformation to its `0 0` element. -/
def timeCompCont : C(LorentzGroup d, ℝ) := ⟨fun Λ => timeComp Λ  ,
   Continuous.matrix_elem (continuous_iff_le_induced.mpr fun _ a => a) (Sum.inl 0) (Sum.inl 0)⟩

/-- An auxillary function used in the definition of `orthchroMapReal`. -/
def stepFunction : ℝ → ℝ := fun t =>
  if t ≤ -1 then -1 else
    if 1 ≤  t then 1 else t

lemma stepFunction_continuous : Continuous stepFunction := by
  apply Continuous.if ?_ continuous_const (Continuous.if ?_ continuous_const continuous_id)
   <;> intro a ha
  rw [@Set.Iic_def, @frontier_Iic, @Set.mem_singleton_iff] at ha
  rw [ha]
  simp  [neg_lt_self_iff, zero_lt_one, ↓reduceIte]
  have h1 : ¬ (1 : ℝ) ≤ 0 := by simp
  exact Eq.symm (if_neg h1)
  rw [Set.Ici_def, @frontier_Ici, @Set.mem_singleton_iff] at ha
  exact id (Eq.symm ha)

/-- The continuous map from `lorentzGroup` to `ℝ` wh
taking Orthochronous elements to `1` and non-orthochronous to `-1`. -/
def orthchroMapReal : C(LorentzGroup d, ℝ) := ContinuousMap.comp
  ⟨stepFunction, stepFunction_continuous⟩ timeCompCont

lemma orthchroMapReal_on_IsOrthochronous {Λ : LorentzGroup d} (h : IsOrthochronous Λ) :
    orthchroMapReal Λ = 1 := by
  rw [IsOrthochronous_iff_ge_one, timeComp] at h
  change stepFunction (Λ.1 _ _) = 1
  rw [stepFunction, if_pos h, if_neg]
  linarith

lemma orthchroMapReal_on_not_IsOrthochronous {Λ : LorentzGroup d} (h : ¬ IsOrthochronous Λ) :
    orthchroMapReal Λ = - 1 := by
  rw [not_orthochronous_iff_le_neg_one] at h
  change stepFunction (timeComp _)= - 1
  rw [stepFunction, if_pos h]

lemma orthchroMapReal_minus_one_or_one (Λ : LorentzGroup d) :
    orthchroMapReal Λ = -1 ∨ orthchroMapReal Λ = 1 := by
  by_cases h : IsOrthochronous Λ
  apply Or.inr $ orthchroMapReal_on_IsOrthochronous h
  apply Or.inl $ orthchroMapReal_on_not_IsOrthochronous h

local notation  "ℤ₂" => Multiplicative (ZMod 2)

/-- A continuous map from `lorentzGroup` to `ℤ₂` whose kernal are the Orthochronous elements. -/
def orthchroMap : C(LorentzGroup d, ℤ₂) :=
  ContinuousMap.comp coeForℤ₂ {
    toFun := fun Λ => ⟨orthchroMapReal Λ, orthchroMapReal_minus_one_or_one Λ⟩,
    continuous_toFun :=  Continuous.subtype_mk (ContinuousMap.continuous orthchroMapReal) _}

lemma orthchroMap_IsOrthochronous {Λ : LorentzGroup d} (h : IsOrthochronous Λ) :
    orthchroMap Λ = 1 := by
  simp [orthchroMap, orthchroMapReal_on_IsOrthochronous h]

lemma orthchroMap_not_IsOrthochronous {Λ : LorentzGroup d} (h : ¬ IsOrthochronous Λ) :
    orthchroMap Λ =  Additive.toMul (1 : ZMod 2) := by
  simp [orthchroMap, orthchroMapReal_on_not_IsOrthochronous h]
  rfl

lemma mul_othchron_of_othchron_othchron {Λ Λ' : LorentzGroup d} (h : IsOrthochronous Λ)
    (h' : IsOrthochronous Λ') : IsOrthochronous (Λ * Λ') := by
  rw [IsOrthochronous_iff_transpose] at h
  rw [IsOrthochronous_iff_futurePointing] at h h'
  rw [IsOrthochronous, timeComp_mul]
  exact NormOneLorentzVector.FuturePointing.metric_reflect_mem_mem h h'

lemma mul_othchron_of_not_othchron_not_othchron {Λ Λ' : LorentzGroup d} (h : ¬ IsOrthochronous Λ)
    (h' : ¬ IsOrthochronous Λ') : IsOrthochronous (Λ * Λ') := by
  rw [IsOrthochronous_iff_transpose] at h
  rw [IsOrthochronous_iff_futurePointing] at h h'
  rw [IsOrthochronous, timeComp_mul]
  exact NormOneLorentzVector.FuturePointing.metric_reflect_not_mem_not_mem h h'

lemma mul_not_othchron_of_othchron_not_othchron {Λ Λ' : LorentzGroup d} (h :  IsOrthochronous Λ)
    (h' : ¬ IsOrthochronous Λ') : ¬ IsOrthochronous (Λ * Λ') := by
  rw [not_orthochronous_iff_le_zero, timeComp_mul]
  rw [IsOrthochronous_iff_transpose] at h
  rw [IsOrthochronous_iff_futurePointing] at h h'
  exact NormOneLorentzVector.FuturePointing.metric_reflect_mem_not_mem h h'

lemma mul_not_othchron_of_not_othchron_othchron {Λ Λ' : LorentzGroup d} (h : ¬ IsOrthochronous Λ)
    (h' : IsOrthochronous Λ') : ¬ IsOrthochronous (Λ * Λ') := by
  rw [not_orthochronous_iff_le_zero, timeComp_mul]
  rw [IsOrthochronous_iff_transpose] at h
  rw [IsOrthochronous_iff_futurePointing] at h h'
  exact NormOneLorentzVector.FuturePointing.metric_reflect_not_mem_mem h h'

/-- The homomorphism from `lorentzGroup` to `ℤ₂` whose kernel are the Orthochronous elements. -/
def orthchroRep : LorentzGroup d →* ℤ₂ where
  toFun := orthchroMap
  map_one' := orthchroMap_IsOrthochronous (by simp [IsOrthochronous])
  map_mul' Λ Λ' := by
    simp only
    by_cases h : IsOrthochronous Λ
     <;> by_cases h' : IsOrthochronous Λ'
    rw [orthchroMap_IsOrthochronous h, orthchroMap_IsOrthochronous h',
      orthchroMap_IsOrthochronous (mul_othchron_of_othchron_othchron h h')]
    rfl
    rw [orthchroMap_IsOrthochronous h, orthchroMap_not_IsOrthochronous h',
      orthchroMap_not_IsOrthochronous (mul_not_othchron_of_othchron_not_othchron h h')]
    rfl
    rw [orthchroMap_not_IsOrthochronous h, orthchroMap_IsOrthochronous h',
      orthchroMap_not_IsOrthochronous (mul_not_othchron_of_not_othchron_othchron h h')]
    rfl
    rw [orthchroMap_not_IsOrthochronous h, orthchroMap_not_IsOrthochronous h',
      orthchroMap_IsOrthochronous (mul_othchron_of_not_othchron_not_othchron h h')]
    rfl

end LorentzGroup

end
