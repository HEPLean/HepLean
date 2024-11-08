/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup.Proper
import Mathlib.Topology.Constructions
import HepLean.SpaceTime.LorentzVector.Real.NormOne
/-!
# Boosts

This file defines those Lorentz which are boosts.

We first define generalised boosts, which are restricted lorentz transformations taking
a four velocity `u` to a four velocity `v`.

A boost is the special case of a generalised boost when `u = stdBasis 0`.

## References

- The main argument follows: Guillem Cobos, The Lorentz Group, 2015:
  https://diposit.ub.edu/dspace/bitstream/2445/68763/2/memoria.pdf

-/
/-! TODO: Show that generalised boosts are in the restricted Lorentz group. -/
noncomputable section

namespace LorentzGroup

open Lorentz.Contr.NormOne
open Lorentz
open TensorProduct

variable {d : ℕ}

/-- An auxillary linear map used in the definition of a generalised boost. -/
def genBoostAux₁ (u v : FuturePointing d) : ContrMod d →ₗ[ℝ] ContrMod d where
  toFun x := (2 * toField d ⟪x, u.val.val⟫ₘ) • v.1.1
  map_add' x y := by
    simp [map_add, LinearMap.add_apply, tmul_add, add_tmul, mul_add, add_smul]
  map_smul' c x := by
    simp only [toField, Action.instMonoidalCategory_tensorObj_V,
      Action.instMonoidalCategory_tensorUnit_V, CategoryTheory.Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      smul_tmul, tmul_smul, map_smul, smul_eq_mul, RingHom.id_apply]
    erw [LinearMap.id_apply]
    rw [← mul_assoc, mul_comm 2 c, mul_assoc, mul_smul]
    rfl

/-- An auxillary linear map used in the definition of a genearlised boost. -/
def genBoostAux₂ (u v : FuturePointing d) : ContrMod d →ₗ[ℝ] ContrMod d where
  toFun x := - (toField d ⟪x, u.1.1 + v.1.1⟫ₘ / (1 + toField d ⟪u.1.1, v.1.1⟫ₘ)) • (u.1.1 + v.1.1)
  map_add' x y := by
    simp only
    rw [← add_smul]
    apply congrFun (congrArg _ _)
    field_simp [add_tmul]
    apply congrFun (congrArg _ _)
    ring
  map_smul' c x := by
    simp only [smul_tmul, tmul_smul]
    rw [map_smul]
    conv =>
      lhs; lhs; rhs; lhs
      change (c * toField d (contrContrContract.hom (x ⊗ₜ[ℝ] (u.val.val + v.val.val))))
    rw [mul_div_assoc, neg_mul_eq_mul_neg, smul_smul]
    rfl

lemma genBoostAux₂_self (u : FuturePointing d) : genBoostAux₂ u u = - genBoostAux₁ u u := by
  ext1 x
  simp only [genBoostAux₂, LinearMap.coe_mk, AddHom.coe_mk, genBoostAux₁, LinearMap.neg_apply]
  rw [neg_smul]
  apply congrArg
  conv => lhs; rhs; rw [← (two_smul ℝ u.val.val)]
  rw [smul_smul]
  congr 1
  rw [u.1.2]
  simp [toField]
  conv => lhs; lhs; rhs; rhs; change 1
  rw [show 1 + (1 : ℝ) = (2 : ℝ ) by ring]
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel]
  rw [← (two_smul ℝ u.val.val)]
  simp only [tmul_smul, map_smul, smul_eq_mul]
  rfl


/-- An generalised boost. This is a Lorentz transformation which takes the four velocity `u`
to `v`. -/
def genBoost (u v : FuturePointing d) : ContrMod d →ₗ[ℝ] ContrMod d :=
  LinearMap.id + genBoostAux₁ u v + genBoostAux₂ u v

namespace genBoost

/--
  This lemma states that for a given four-velocity `u`, the general boost
  transformation `genBoost u u` is equal to the identity linear map `LinearMap.id`.
-/
lemma self (u : FuturePointing d) : genBoost u u = LinearMap.id := by
  ext x
  simp only [genBoost, LinearMap.add_apply, LinearMap.id_coe, id_eq]
  rw [genBoostAux₂_self]
  simp only [LinearMap.neg_apply, add_neg_cancel_right]

/-- A generalised boost as a matrix. -/
def toMatrix (u v : FuturePointing d) : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  LinearMap.toMatrix ContrMod.stdBasis ContrMod.stdBasis (genBoost u v)

lemma toMatrix_mulVec (u v : FuturePointing d) (x : Contr d) :
    (toMatrix u v) *ᵥ x = genBoost u v x :=
  ContrMod.ext (LinearMap.toMatrix_mulVec_repr ContrMod.stdBasis ContrMod.stdBasis (genBoost u v) x)

open minkowskiMatrix LorentzVector in
@[simp]
lemma toMatrix_apply (u v : FuturePointing d) (μ ν : Fin 1 ⊕ Fin d) :
    (toMatrix u v) μ ν = η μ μ * (toField d ⟪ContrMod.stdBasis μ, ContrMod.stdBasis ν⟫ₘ + 2 *
     toField d ⟪ContrMod.stdBasis ν, u.val.val⟫ₘ * toField d  ⟪ContrMod.stdBasis μ, v.val.val⟫ₘ
    - toField d  ⟪ContrMod.stdBasis μ, u.val.val + v.val.val⟫ₘ *
    toField d  ⟪ContrMod.stdBasis ν, u.val.val + v.val.val⟫ₘ /
    (1 + toField d  ⟪u.val.val, v.val.val⟫ₘ)) := by
  sorry
  rw [matrix_apply_stdBasis (toMatrix u v) μ ν, toMatrix_mulVec]
  simp only [genBoost, genBoostAux₁, genBoostAux₂, map_add, smul_add, neg_smul, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk, basis_left, map_smul, smul_eq_mul, map_neg,
    mul_eq_mul_left_iff]
  ring_nf
  exact (true_or (η μ μ = 0)).mpr trivial

open minkowskiMatrix LorentzVector in
lemma toMatrix_continuous (u : FuturePointing d) : Continuous (toMatrix u) := by
  refine continuous_matrix ?_
  intro i j
  simp only [toMatrix_apply]
  refine (continuous_mul_left (η i i)).comp' ?_
  refine Continuous.sub ?_ ?_
  · refine .comp' (continuous_add_left (minkowskiMetric (e i) (e j))) ?_
    refine .comp' (continuous_mul_left (2 * ⟪e j, u⟫ₘ)) ?_
    exact FuturePointing.metric_continuous _
  refine .mul ?_ ?_
  · refine .mul ?_ ?_
    · simp only [(minkowskiMetric _).map_add]
      refine .comp' ?_ ?_
      · exact continuous_add_left ((minkowskiMetric (stdBasis i)) ↑u)
      · exact FuturePointing.metric_continuous _
    · simp only [(minkowskiMetric _).map_add]
      refine .comp' ?_ ?_
      · exact continuous_add_left _
      · exact FuturePointing.metric_continuous _
  · refine .inv₀ ?_ ?_
    · refine .comp' (continuous_add_left 1) (FuturePointing.metric_continuous _)
    exact fun x => FuturePointing.one_add_metric_non_zero u x

lemma toMatrix_in_lorentzGroup (u v : FuturePointing d) : (toMatrix u v) ∈ LorentzGroup d:= by
  intro x y
  rw [toMatrix_mulVec, toMatrix_mulVec, genBoost, genBoostAux₁, genBoostAux₂]
  have h1 : (1 + (minkowskiMetric ↑u) ↑v.1.1) ≠ 0 := FuturePointing.one_add_metric_non_zero u v
  simp only [map_add, smul_add, neg_smul, LinearMap.add_apply, LinearMap.id_coe,
    id_eq, LinearMap.coe_mk, AddHom.coe_mk, LinearMapClass.map_smul, map_neg, LinearMap.smul_apply,
    smul_eq_mul, LinearMap.neg_apply]
  field_simp
  rw [u.1.2, v.1.2, minkowskiMetric.symm v.1.1 u, minkowskiMetric.symm u y,
      minkowskiMetric.symm v y]
  ring

/-- A generalised boost as an element of the Lorentz Group. -/
def toLorentz (u v : FuturePointing d) : LorentzGroup d :=
  ⟨toMatrix u v, toMatrix_in_lorentzGroup u v⟩

lemma toLorentz_continuous (u : FuturePointing d) : Continuous (toLorentz u) := by
  refine Continuous.subtype_mk ?_ (fun x => toMatrix_in_lorentzGroup u x)
  exact toMatrix_continuous u

lemma toLorentz_joined_to_1 (u v : FuturePointing d) : Joined 1 (toLorentz u v) := by
  obtain ⟨f, _⟩ := FuturePointing.isPathConnected.joinedIn u trivial v trivial
  use ContinuousMap.comp ⟨toLorentz u, toLorentz_continuous u⟩ f
  · simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    Path.source, ContinuousMap.coe_mk]
    rw [@Subtype.ext_iff, toLorentz]
    simp [toMatrix, self u]
  · simp

lemma toLorentz_in_connected_component_1 (u v : FuturePointing d) :
    toLorentz u v ∈ connectedComponent 1 :=
  pathComponent_subset_component _ (toLorentz_joined_to_1 u v)

lemma isProper (u v : FuturePointing d) : IsProper (toLorentz u v) :=
  (isProper_on_connected_component (toLorentz_in_connected_component_1 u v)).mp id_IsProper

end genBoost

end LorentzGroup

end
