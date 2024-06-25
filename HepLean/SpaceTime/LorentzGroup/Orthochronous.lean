/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.FourVelocity
import HepLean.SpaceTime.LorentzGroup.Proper
/-!
# The Orthochronous Lorentz Group

We define the give a series of lemmas related to the orthochronous property of lorentz
matrices.

## TODO

- Prove topological properties.

-/


noncomputable section

namespace spaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

namespace lorentzGroup
open PreFourVelocity

/-- The first column of a lorentz matrix as a `PreFourVelocity`. -/
@[simp]
def fstCol (Λ : lorentzGroup) : PreFourVelocity := ⟨Λ.1 *ᵥ stdBasis 0, by
  rw [mem_PreFourVelocity_iff, ηLin_expand]
  simp only [Fin.isValue, stdBasis_mulVec]
  have h00 := congrFun (congrFun ((PreservesηLin.iff_matrix Λ.1).mp  Λ.2) 0) 0
  simp only [Fin.isValue, mul_apply, transpose_apply, Fin.sum_univ_four, ne_eq, zero_ne_one,
    not_false_eq_true, η_off_diagonal, zero_mul, add_zero, Fin.reduceEq, one_ne_zero, mul_zero,
    zero_add, one_apply_eq] at h00
  simp only [η_explicit, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val',
    cons_val_fin_one, vecCons_const, one_mul, mul_one, cons_val_one, head_cons, mul_neg, neg_mul,
    cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, cons_val_three,
     head_fin_const] at h00
  exact h00⟩

/-- A Lorentz transformation is  `orthochronous` if its `0 0` element is non-negative. -/
def IsOrthochronous (Λ : lorentzGroup) : Prop := 0 ≤ Λ.1 0 0

lemma IsOrthochronous_iff_transpose (Λ : lorentzGroup) :
    IsOrthochronous Λ ↔ IsOrthochronous (transpose Λ) := by rfl

lemma IsOrthochronous_iff_fstCol_IsFourVelocity (Λ : lorentzGroup) :
    IsOrthochronous Λ ↔ IsFourVelocity (fstCol Λ) := by
  simp [IsOrthochronous, IsFourVelocity]
  rw [stdBasis_mulVec]

/-- The continuous map taking a Lorentz transformation to its `0 0` element. -/
def mapZeroZeroComp : C(lorentzGroup, ℝ) := ⟨fun Λ => Λ.1 0 0,
   Continuous.matrix_elem (continuous_iff_le_induced.mpr fun _ a => a) 0 0⟩

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
def orthchroMapReal : C(lorentzGroup, ℝ) := ContinuousMap.comp
  ⟨stepFunction, stepFunction_continuous⟩ mapZeroZeroComp

lemma orthchroMapReal_on_IsOrthochronous {Λ : lorentzGroup} (h : IsOrthochronous Λ) :
    orthchroMapReal Λ = 1 := by
  rw [IsOrthochronous_iff_fstCol_IsFourVelocity] at h
  simp only [IsFourVelocity] at h
  rw [zero_nonneg_iff] at h
  simp [stdBasis_mulVec] at h
  have h1 : ¬  Λ.1 0 0 ≤  (-1 : ℝ) := by linarith
  change stepFunction (Λ.1 0 0) = 1
  rw [stepFunction, if_neg h1, if_pos h]


lemma orthchroMapReal_on_not_IsOrthochronous {Λ : lorentzGroup} (h : ¬ IsOrthochronous Λ) :
    orthchroMapReal Λ = - 1 := by
  rw [IsOrthochronous_iff_fstCol_IsFourVelocity] at h
  rw [not_IsFourVelocity_iff, zero_nonpos_iff] at h
  simp only [fstCol, Fin.isValue, stdBasis_mulVec] at h
  change stepFunction (Λ.1 0 0) = - 1
  rw [stepFunction, if_pos h]

lemma orthchroMapReal_minus_one_or_one (Λ : lorentzGroup) :
    orthchroMapReal Λ = -1 ∨ orthchroMapReal Λ = 1 := by
  by_cases h : IsOrthochronous Λ
  apply Or.inr $ orthchroMapReal_on_IsOrthochronous h
  apply Or.inl $ orthchroMapReal_on_not_IsOrthochronous h

local notation  "ℤ₂" => Multiplicative (ZMod 2)

/-- A continuous map from `lorentzGroup` to `ℤ₂` whose kernal are the Orthochronous elements. -/
def orthchroMap : C(lorentzGroup, ℤ₂) :=
  ContinuousMap.comp coeForℤ₂ {
    toFun := fun Λ => ⟨orthchroMapReal Λ, orthchroMapReal_minus_one_or_one Λ⟩,
    continuous_toFun :=  Continuous.subtype_mk (ContinuousMap.continuous orthchroMapReal) _}

lemma orthchroMap_IsOrthochronous {Λ : lorentzGroup} (h : IsOrthochronous Λ) :
    orthchroMap Λ = 1 := by
  simp [orthchroMap, orthchroMapReal_on_IsOrthochronous h]

lemma orthchroMap_not_IsOrthochronous {Λ : lorentzGroup} (h : ¬ IsOrthochronous Λ) :
    orthchroMap Λ =  Additive.toMul (1 : ZMod 2) := by
  simp [orthchroMap, orthchroMapReal_on_not_IsOrthochronous h]
  rfl

lemma zero_zero_mul (Λ Λ' : lorentzGroup) :
    (Λ * Λ').1 0 0 =  (fstCol (transpose Λ)).1 0 * (fstCol Λ').1 0 +
    ⟪(fstCol (transpose Λ)).1.space, (fstCol Λ').1.space⟫_ℝ := by
  simp only [Fin.isValue, lorentzGroupIsGroup_mul_coe, mul_apply, Fin.sum_univ_four, fstCol,
    transpose, stdBasis_mulVec, transpose_apply, space, PiLp.inner_apply, Nat.succ_eq_add_one,
    Nat.reduceAdd, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three, cons_val_zero,
    cons_val_one, head_cons, cons_val_two, tail_cons]
  ring

lemma mul_othchron_of_othchron_othchron {Λ Λ' : lorentzGroup} (h : IsOrthochronous Λ)
    (h' : IsOrthochronous Λ') : IsOrthochronous (Λ * Λ') := by
  rw [IsOrthochronous_iff_transpose] at h
  rw [IsOrthochronous_iff_fstCol_IsFourVelocity] at h h'
  rw [IsOrthochronous, zero_zero_mul]
  exact euclid_norm_IsFourVelocity_IsFourVelocity h h'

lemma mul_othchron_of_not_othchron_not_othchron {Λ Λ' : lorentzGroup} (h : ¬  IsOrthochronous Λ)
    (h' : ¬ IsOrthochronous Λ') : IsOrthochronous (Λ * Λ') := by
  rw [IsOrthochronous_iff_transpose] at h
  rw [IsOrthochronous_iff_fstCol_IsFourVelocity] at h h'
  rw [IsOrthochronous, zero_zero_mul]
  exact euclid_norm_not_IsFourVelocity_not_IsFourVelocity h h'

lemma mul_not_othchron_of_othchron_not_othchron {Λ Λ' : lorentzGroup} (h :  IsOrthochronous Λ)
    (h' : ¬ IsOrthochronous Λ') : ¬ IsOrthochronous (Λ * Λ') := by
  rw [IsOrthochronous_iff_transpose] at h
  rw [IsOrthochronous_iff_fstCol_IsFourVelocity] at h h'
  rw [IsOrthochronous_iff_fstCol_IsFourVelocity, not_IsFourVelocity_iff]
  simp [stdBasis_mulVec]
  change (Λ * Λ').1 0 0  ≤ _
  rw [zero_zero_mul]
  exact euclid_norm_IsFourVelocity_not_IsFourVelocity h h'

lemma mul_not_othchron_of_not_othchron_othchron {Λ Λ' : lorentzGroup} (h : ¬ IsOrthochronous Λ)
    (h' : IsOrthochronous Λ') : ¬ IsOrthochronous (Λ * Λ') := by
  rw [IsOrthochronous_iff_transpose] at h
  rw [IsOrthochronous_iff_fstCol_IsFourVelocity] at h h'
  rw [IsOrthochronous_iff_fstCol_IsFourVelocity, not_IsFourVelocity_iff]
  simp [stdBasis_mulVec]
  change (Λ * Λ').1 0 0  ≤ _
  rw [zero_zero_mul]
  exact euclid_norm_not_IsFourVelocity_IsFourVelocity h h'

/-- The homomorphism from `lorentzGroup` to `ℤ₂` whose kernel are the Orthochronous elements. -/
def orthchroRep : lorentzGroup →* ℤ₂ where
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

end lorentzGroup

end spaceTime
end
