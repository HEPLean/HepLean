/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.Group.Proper
import HepLean.Lorentz.RealVector.NormOne
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
noncomputable section

namespace LorentzGroup

open Lorentz.Contr.NormOne
open Lorentz
open TensorProduct

variable {d : ℕ}

/-- An auxillary linear map used in the definition of a generalised boost. -/
def genBoostAux₁ (u v : FuturePointing d) : ContrMod d →ₗ[ℝ] ContrMod d where
  toFun x := (2 * ⟪x, u.val.val⟫ₘ) • v.1.1
  map_add' x y := by
    simp [map_add, LinearMap.add_apply, tmul_add, add_tmul, mul_add, add_smul]
  map_smul' c x := by
    simp only [Action.instMonoidalCategory_tensorObj_V,
      Action.instMonoidalCategory_tensorUnit_V, CategoryTheory.Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      smul_tmul, tmul_smul, map_smul, smul_eq_mul, RingHom.id_apply]
    rw [← mul_assoc, mul_comm 2 c, mul_assoc, mul_smul]

/-- An auxillary linear map used in the definition of a genearlised boost. -/
def genBoostAux₂ (u v : FuturePointing d) : ContrMod d →ₗ[ℝ] ContrMod d where
  toFun x := - (⟪x, u.1.1 + v.1.1⟫ₘ / (1 + ⟪u.1.1, v.1.1⟫ₘ)) • (u.1.1 + v.1.1)
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
      change (c * (contrContrContractField (x ⊗ₜ[ℝ] (u.val.val + v.val.val))))
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
  conv => lhs; lhs; rhs; rhs; change 1
  rw [show 1 + (1 : ℝ) = (2 : ℝ) by ring]
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel]
  rw [← (two_smul ℝ u.val.val)]
  simp only [tmul_smul, map_smul, smul_eq_mul]

/-- An generalised boost. This is a Lorentz transformation which takes the four velocity `u`
to `v`. -/
def genBoost (u v : FuturePointing d) : ContrMod d →ₗ[ℝ] ContrMod d :=
  LinearMap.id + genBoostAux₁ u v + genBoostAux₂ u v

lemma genBoost_mul_one_plus_contr (u v : FuturePointing d) (x : Contr d) :
    (1 + ⟪u.1.1, v.1.1⟫ₘ) • genBoost u v x =
    (1 + ⟪u.1.1, v.1.1⟫ₘ) • x +
    (2 * ⟪x, u.val.val⟫ₘ * (1 + ⟪u.1.1, v.1.1⟫ₘ)) • v.1.1
    - (⟪x, u.1.1 + v.1.1⟫ₘ) • (u.1.1 + v.1.1) := by
  simp only [genBoost, LinearMap.add_apply, LinearMap.id_apply, id_eq]
  rw [smul_add, smul_add]
  trans (1 + ⟪u.1.1, v.1.1⟫ₘ) • x +
    (2 * ⟪x, u.val.val⟫ₘ * (1 + ⟪u.1.1, v.1.1⟫ₘ)) • v.1.1
    + (- ⟪x, u.1.1 + v.1.1⟫ₘ) • (u.1.1 + v.1.1)
  · congr 1
    · congr 1
      rw [genBoostAux₁]
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [smul_smul]
      congr 1
      ring
    · rw [genBoostAux₂]
      simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
        CategoryTheory.Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
        Action.FunctorCategoryEquivalence.functor_obj_obj, neg_smul, LinearMap.coe_mk,
        AddHom.coe_mk, smul_neg]
      rw [smul_smul]
      congr
      have h1 := FuturePointing.one_add_metric_non_zero u v
      field_simp
  · rw [neg_smul]
    rfl

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

open minkowskiMatrix in
@[simp]
lemma toMatrix_apply (u v : FuturePointing d) (μ ν : Fin 1 ⊕ Fin d) :
    (toMatrix u v) μ ν = η μ μ * (⟪ContrMod.stdBasis μ, ContrMod.stdBasis ν⟫ₘ + 2 *
    ⟪ContrMod.stdBasis ν, u.val.val⟫ₘ * ⟪ContrMod.stdBasis μ, v.val.val⟫ₘ
    - ⟪ContrMod.stdBasis μ, u.val.val + v.val.val⟫ₘ *
    ⟪ContrMod.stdBasis ν, u.val.val + v.val.val⟫ₘ /
    (1 + ⟪u.val.val, v.val.val⟫ₘ)) := by
  rw [contrContrContractField.matrix_apply_stdBasis (Λ := toMatrix u v) μ ν, toMatrix_mulVec]
  simp only [genBoost, genBoostAux₁, genBoostAux₂, smul_add, neg_smul, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk, contrContrContractField.basis_left,
    map_add, map_smul, map_neg, mul_eq_mul_left_iff]
  ring_nf
  simp only [Pi.add_apply, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_tensorUnit_V, CategoryTheory.Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.neg_apply]
  left
  ring

open minkowskiMatrix in
lemma toMatrix_continuous (u : FuturePointing d) : Continuous (toMatrix u) := by
  refine continuous_matrix ?_
  intro i j
  simp only [toMatrix_apply]
  refine (continuous_mul_left (η i i)).comp' ?_
  refine Continuous.sub ?_ ?_
  · refine .comp' (continuous_add_left _) ?_
    refine .comp' (continuous_mul_left _) ?_
    exact FuturePointing.metric_continuous _
  refine .mul ?_ ?_
  · refine .mul ?_ ?_
    · simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      CategoryTheory.Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, tmul_add, map_add]
      refine .comp' ?_ ?_
      · exact continuous_add_left _
      · exact FuturePointing.metric_continuous _
    · simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      CategoryTheory.Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, tmul_add, map_add]
      refine .comp' ?_ ?_
      · exact continuous_add_left _
      · exact FuturePointing.metric_continuous _
  · refine .inv₀ ?_ ?_
    · refine .comp' (continuous_add_left 1) (FuturePointing.metric_continuous _)
    exact fun x => FuturePointing.one_add_metric_non_zero u x

lemma toMatrix_in_lorentzGroup (u v : FuturePointing d) : (toMatrix u v) ∈ LorentzGroup d := by
  rw [LorentzGroup.mem_iff_invariant]
  intro x y
  rw [toMatrix_mulVec, toMatrix_mulVec]
  have h1 : (((1 + ⟪u.1.1, v.1.1⟫ₘ)) * (1 + ⟪u.1.1, v.1.1⟫ₘ)) •
      (contrContrContractField ((genBoost u v) y ⊗ₜ[ℝ] (genBoost u v) x))
      = (((1 + ⟪u.1.1, v.1.1⟫ₘ)) * (1 + ⟪u.1.1, v.1.1⟫ₘ)) • ⟪y, x⟫ₘ := by
    conv_lhs =>
      erw [← map_smul]
      rw [← smul_smul]
      rw [← tmul_smul, ← smul_tmul, ← tmul_smul, genBoost_mul_one_plus_contr,
        genBoost_mul_one_plus_contr]
      simp only [add_smul, one_smul, tmul_add, map_add, smul_add, tmul_sub, sub_tmul, add_tmul,
        smul_tmul, tmul_smul, map_sub, map_smul, smul_eq_mul, contr_self, mul_one]
      rw [contrContrContractField.symm v.1.1 u, contrContrContractField.symm v.1.1 x,
        contrContrContractField.symm u.1.1 x]
    simp only [smul_eq_mul]
    ring
  have hn (a : ℝ) {b c : ℝ} (h : a ≠ 0) (hab : a * b = a * c) : b = c := by
    simp_all only [smul_eq_mul, ne_eq, mul_eq_mul_left_iff, or_false]
  refine hn _ ?_ h1
  simpa using (FuturePointing.one_add_metric_non_zero u v)

TODO "Make `toLorentz` the definition of a generalised boost. This will involve
  refactoring this file."
/-- A generalised boost as an element of the Lorentz Group. -/
def toLorentz (u v : FuturePointing d) : LorentzGroup d :=
  ⟨toMatrix u v, toMatrix_in_lorentzGroup u v⟩

TODO "Show that generalised boosts are in the restricted Lorentz group."

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
