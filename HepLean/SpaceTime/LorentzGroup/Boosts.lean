/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup.Proper
import Mathlib.Topology.Constructions
import HepLean.SpaceTime.LorentzVector.NormOne
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

open NormOneLorentzVector
open minkowskiMetric

variable {d : ℕ}

/-- An auxillary linear map used in the definition of a generalised boost. -/
def genBoostAux₁ (u v : FuturePointing d) : LorentzVector d →ₗ[ℝ] LorentzVector d where
  toFun x := (2 * ⟪x, u⟫ₘ) • v.1.1
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply]
    rw [mul_add, add_smul]
  map_smul' c x := by
    simp only [LinearMapClass.map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [← mul_assoc, mul_comm 2 c, mul_assoc, mul_smul]

/-- An auxillary linear map used in the definition of a genearlised boost. -/
def genBoostAux₂ (u v : FuturePointing d) : LorentzVector d →ₗ[ℝ] LorentzVector d where
  toFun x := - (⟪x, u.1.1 + v⟫ₘ / (1 + ⟪u.1.1, v⟫ₘ)) • (u.1.1 + v)
  map_add' x y := by
    simp only
    rw [← add_smul]
    apply congrFun
    apply congrArg
    field_simp
    apply congrFun
    apply congrArg
    ring
  map_smul' c x := by
    simp only
    rw [map_smul]
    rw [show (c • minkowskiMetric x) (↑u + ↑v) = c * minkowskiMetric x (u+v) from rfl]
    rw [mul_div_assoc, neg_mul_eq_mul_neg, smul_smul]
    rfl

/-- An generalised boost. This is a Lorentz transformation which takes the four velocity `u`
to `v`. -/
def genBoost (u v : FuturePointing d) : LorentzVector d →ₗ[ℝ] LorentzVector d :=
  LinearMap.id + genBoostAux₁ u v + genBoostAux₂ u v

namespace genBoost

/--
  This lemma states that for a given four-velocity `u`, the general boost
  transformation `genBoost u u` is equal to the identity linear map `LinearMap.id`.
-/
lemma self (u : FuturePointing d) : genBoost u u = LinearMap.id := by
  ext x
  simp [genBoost]
  rw [add_assoc]
  rw [@add_right_eq_self]
  rw [@add_eq_zero_iff_eq_neg]
  rw [genBoostAux₁, genBoostAux₂]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, smul_add, neg_smul, neg_add_rev, neg_neg]
  rw [← add_smul]
  apply congr
  apply congrArg
  repeat rw [u.1.2]
  field_simp
  ring
  rfl

/-- A generalised boost as a matrix. -/
def toMatrix (u v : FuturePointing d) : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ :=
  LinearMap.toMatrix LorentzVector.stdBasis LorentzVector.stdBasis (genBoost u v)

lemma toMatrix_mulVec (u v : FuturePointing d) (x : LorentzVector d) :
    (toMatrix u v).mulVec x = genBoost u v x :=
  LinearMap.toMatrix_mulVec_repr LorentzVector.stdBasis LorentzVector.stdBasis (genBoost u v) x

open minkowskiMatrix LorentzVector in
@[simp]
lemma toMatrix_apply (u v : FuturePointing d) (μ ν : Fin 1 ⊕ Fin d) :
    (toMatrix u v) μ ν = η μ μ * (⟪e μ, e ν⟫ₘ + 2 * ⟪e ν, u⟫ₘ * ⟪e μ, v⟫ₘ
    - ⟪e μ, u + v⟫ₘ * ⟪e ν, u + v⟫ₘ / (1 + ⟪u, v.1.1⟫ₘ)) := by
  rw [matrix_apply_stdBasis (toMatrix u v) μ ν, toMatrix_mulVec]
  simp only [genBoost, genBoostAux₁, genBoostAux₂, map_add, smul_add, neg_smul, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk, basis_left, map_smul, smul_eq_mul, map_neg,
    mul_eq_mul_left_iff]
  have h1 := FuturePointing.one_add_metric_non_zero u v
  field_simp
  ring_nf
  simp

open minkowskiMatrix LorentzVector in
lemma toMatrix_continuous (u : FuturePointing d) : Continuous (toMatrix u) := by
  refine continuous_matrix ?_
  intro i j
  simp only [toMatrix_apply]
  refine Continuous.comp' (continuous_mul_left (η i i)) ?hf
  refine Continuous.sub ?_ ?_
  refine Continuous.comp' (continuous_add_left ⟪e i, e j⟫ₘ) ?_
  refine Continuous.comp' (continuous_mul_left (2 * ⟪e j, u⟫ₘ)) ?_
  exact FuturePointing.metric_continuous _
  refine Continuous.mul ?_ ?_
  refine Continuous.mul ?_ ?_
  simp only [(minkowskiMetric _).map_add]
  refine Continuous.comp' ?_ ?_
  exact continuous_add_left ((minkowskiMetric (stdBasis i)) ↑u)
  exact FuturePointing.metric_continuous _
  simp only [(minkowskiMetric _).map_add]
  refine Continuous.comp' ?_ ?_
  exact continuous_add_left _
  exact FuturePointing.metric_continuous _
  refine Continuous.inv₀ ?_ ?_
  refine Continuous.comp' (continuous_add_left 1) ?_
  exact FuturePointing.metric_continuous _
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
