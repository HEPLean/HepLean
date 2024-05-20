/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzGroup.Orthochronous
import HepLean.SpaceTime.LorentzGroup.Proper
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Topology.Constructions
/-!
# Boosts

This file defines those Lorentz which are boosts.

We first define generalised boosts, which are restricted lorentz transforamations taking
a four velocity `u` to a four velcoity `v`.

A boost is the speical case of a generalised boost when `u = stdBasis 0`.

## TODO

- Show that generalised boosts are in the restircted Lorentz group.
- Define boosts.

## References

- The main argument follows: Guillem Cobos, The Lorentz Group, 2015:
  https://diposit.ub.edu/dspace/bitstream/2445/68763/2/memoria.pdf

-/
noncomputable section
namespace spaceTime

namespace lorentzGroup

open FourVelocity

/-- An auxillary linear map used in the definition of a genearlised boost. -/
def genBoostAux₁ (u v : FourVelocity) : spaceTime →ₗ[ℝ] spaceTime where
  toFun x := (2 * ηLin x u) • v.1.1
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply]
    rw [mul_add, add_smul]
  map_smul' c x := by
    simp only [LinearMapClass.map_smul, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [← mul_assoc, mul_comm 2 c, mul_assoc, mul_smul]

/-- An auxillary linear map used in the definition of a genearlised boost. -/
def genBoostAux₂ (u v : FourVelocity) : spaceTime →ₗ[ℝ] spaceTime where
  toFun x := - (ηLin x (u + v) / (1 + ηLin u v)) • (u + v)
  map_add' x y := by
    simp only
    rw [ηLin.map_add, div_eq_mul_one_div]
    rw [show (ηLin x + ηLin y) (↑u + ↑v) = ηLin x (u+v) + ηLin y (u+v) from rfl]
    rw [add_mul, neg_add, add_smul, ← div_eq_mul_one_div, ← div_eq_mul_one_div]
  map_smul' c x := by
    simp only
    rw [ηLin.map_smul]
    rw [show (c • ηLin x) (↑u + ↑v) = c * ηLin x (u+v) from rfl]
    rw [mul_div_assoc, neg_mul_eq_mul_neg, smul_smul]
    rfl

/-- An genearlised boost. This is a Lorentz transformation which takes the four velocity `u`
to `v`. -/
def genBoost (u v : FourVelocity) : spaceTime →ₗ[ℝ] spaceTime :=
  LinearMap.id + genBoostAux₁ u v + genBoostAux₂ u v

namespace genBoost

lemma self (u : FourVelocity) : genBoost u u = LinearMap.id := by
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
def toMatrix (u v : FourVelocity) : Matrix (Fin 4) (Fin 4) ℝ :=
  LinearMap.toMatrix stdBasis stdBasis (genBoost u v)

lemma toMatrix_mulVec (u v : FourVelocity) (x : spaceTime) :
    (toMatrix u v).mulVec x = genBoost u v x :=
  LinearMap.toMatrix_mulVec_repr stdBasis stdBasis (genBoost u v) x

lemma toMatrix_apply (u v : FourVelocity) (i j : Fin 4) :
    (toMatrix u v) i j =
     η i i * (ηLin (stdBasis i) (stdBasis j) + 2 * ηLin (stdBasis j) u * ηLin (stdBasis i) v -
    ηLin (stdBasis i) (u + v) * ηLin (stdBasis j) (u + v) / (1 + ηLin u v)) := by
  rw [ηLin_matrix_stdBasis' j i (toMatrix u v), toMatrix_mulVec]
  simp only [genBoost, genBoostAux₁, genBoostAux₂, map_add, smul_add, neg_smul, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMapClass.map_smul, smul_eq_mul,
    map_neg, mul_eq_mul_left_iff]
  apply Or.inl
  ring

lemma toMatrix_continuous (u : FourVelocity) : Continuous (toMatrix u) := by
  refine continuous_matrix ?_
  intro i j
  simp only [toMatrix_apply]
  refine Continuous.comp' (continuous_mul_left (η i i)) ?hf
  refine Continuous.sub ?_ ?_
  refine Continuous.comp' (continuous_add_left ((ηLin (stdBasis i)) (stdBasis j))) ?_
  refine Continuous.comp' (continuous_mul_left (2 * (ηLin (stdBasis j)) ↑u)) ?_
  exact η_continuous _
  refine Continuous.mul ?_ ?_
  refine Continuous.mul ?_ ?_
  simp only [(ηLin _).map_add]
  refine Continuous.comp' ?_ ?_
  exact continuous_add_left ((ηLin (stdBasis i)) ↑u)
  exact η_continuous _
  simp only [(ηLin _).map_add]
  refine Continuous.comp' ?_ ?_
  exact continuous_add_left _
  exact η_continuous _
  refine Continuous.inv₀ ?_ ?_
  refine Continuous.comp' (continuous_add_left 1) ?_
  exact η_continuous _
  exact fun x => one_plus_ne_zero u x


lemma toMatrix_PreservesηLin (u v : FourVelocity) : PreservesηLin (toMatrix u v) := by
  intro x y
  rw [toMatrix_mulVec, toMatrix_mulVec, genBoost, genBoostAux₁, genBoostAux₂]
  have h1 : (1 + (ηLin ↑u) ↑v) ≠ 0 := one_plus_ne_zero u v
  simp only [map_add, smul_add, neg_smul, LinearMap.add_apply, LinearMap.id_coe,
    id_eq, LinearMap.coe_mk, AddHom.coe_mk, LinearMapClass.map_smul, map_neg, LinearMap.smul_apply,
    smul_eq_mul, LinearMap.neg_apply]
  field_simp
  rw [u.1.2, v.1.2, ηLin_symm v u, ηLin_symm u y, ηLin_symm v y]
  ring

/-- A generalised boost as an element of the Lorentz Group. -/
def toLorentz (u v : FourVelocity) : lorentzGroup :=
  PreservesηLin.liftLor (toMatrix_PreservesηLin u v)

lemma toLorentz_continuous (u : FourVelocity) : Continuous (toLorentz u) := by
  refine Continuous.subtype_mk ?_ fun x => (PreservesηLin.liftLor (toMatrix_PreservesηLin u x)).2
  refine Units.continuous_iff.mpr (And.intro ?_ ?_)
  exact toMatrix_continuous u
  change Continuous fun x => (η * (toMatrix u x).transpose * η)
  refine Continuous.matrix_mul ?_ continuous_const
  refine Continuous.matrix_mul continuous_const ?_
  exact Continuous.matrix_transpose (toMatrix_continuous u)


lemma toLorentz_joined_to_1 (u v : FourVelocity) : Joined 1 (toLorentz u v) := by
  obtain ⟨f, _⟩ := isPathConnected_FourVelocity.joinedIn u trivial v trivial
  use ContinuousMap.comp ⟨toLorentz u, toLorentz_continuous u⟩ f
  · simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    Path.source, ContinuousMap.coe_mk]
    rw [@Subtype.ext_iff, toLorentz, PreservesηLin.liftLor]
    refine Units.val_eq_one.mp ?_
    simp [PreservesηLin.liftGL, toMatrix, self u]
  · simp


end genBoost


end lorentzGroup


end spaceTime
end
