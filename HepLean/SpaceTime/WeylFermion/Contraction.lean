/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.WeylFermion.Basic
/-!

# Contraction of Weyl fermions

-/

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct


/-!

## Contraction of Weyl fermions.

-/
open CategoryTheory.MonoidalCategory

/-- The bi-linear map corresponding to contraction of a left-handed Weyl fermion with a
  alt-left-handed Weyl fermion. -/
def leftAltBi : leftHanded →ₗ[ℂ] altLeftHanded →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r ψ := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The bi-linear map corresponding to contraction of a alt-left-handed Weyl fermion with a
  left-handed Weyl fermion. -/
def altLeftBi : altLeftHanded →ₗ[ℂ] leftHanded →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, add_dotProduct, vec2_dotProduct, Fin.isValue, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
  map_smul' ψ ψ' := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [_root_.map_smul, smul_dotProduct, vec2_dotProduct, Fin.isValue, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]


/-- The bi-linear map corresponding to contraction of a right-handed Weyl fermion with a
  alt-right-handed Weyl fermion. -/
def rightAltBi : rightHanded →ₗ[ℂ] altRightHanded →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r ψ := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The bi-linear map corresponding to contraction of a alt-right-handed Weyl fermion with a
  right-handed Weyl fermion. -/
def altRightBi : altRightHanded →ₗ[ℂ] rightHanded →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ,
    map_add' := by
      intro φ φ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r φ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' ψ ψ':= by
    refine LinearMap.ext (fun φ => ?_)
    simp only [map_add, add_dotProduct, vec2_dotProduct, Fin.isValue, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
  map_smul' ψ ψ' := by
    refine LinearMap.ext (fun φ => ?_)
    simp only [_root_.map_smul, smul_dotProduct, vec2_dotProduct, Fin.isValue, smul_eq_mul,
      LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]

/-- The linear map from leftHandedWeyl ⊗ altLeftHandedWeyl to ℂ given by
    summing over components of leftHandedWeyl and altLeftHandedWeyl in the
    standard basis (i.e. the dot product).
    Physically, the contraction of a left-handed Weyl fermion with a alt-left-handed Weyl fermion.
    In index notation this is ψ_a φ^a. -/
def leftAltContraction : leftHanded ⊗ altLeftHanded ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := TensorProduct.lift leftAltBi
  comm M := by
    apply TensorProduct.ext'
    intro ψ φ
    change (M.1 *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
    simp

lemma leftAltContraction_hom_tmul (ψ : leftHanded) (φ : altLeftHanded) :
    leftAltContraction.hom (ψ ⊗ₜ φ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ := by
  rw [leftAltContraction]
  erw [TensorProduct.lift.tmul]
  rfl

/-- The linear map from altLeftHandedWeyl ⊗ leftHandedWeyl to ℂ given by
    summing over components of altLeftHandedWeyl and leftHandedWeyl in the
    standard basis (i.e. the dot product).
    Physically, the contraction of a alt-left-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ^a ψ_a. -/
def altLeftContraction : altLeftHanded ⊗ leftHanded ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := TensorProduct.lift altLeftBi
  comm M := by
    apply TensorProduct.ext'
    intro φ ψ
    change (M.1⁻¹ᵀ *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1 *ᵥ ψ.toFin2ℂ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    simp

lemma altLeftContraction_hom_tmul (φ : altLeftHanded) (ψ : leftHanded) :
    altLeftContraction.hom (φ ⊗ₜ ψ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ := by
  rw [altLeftContraction]
  erw [TensorProduct.lift.tmul]
  rfl

/--
The linear map from rightHandedWeyl ⊗ altRightHandedWeyl to ℂ given by
  summing over components of rightHandedWeyl and altRightHandedWeyl in the
  standard basis (i.e. the dot product).
  The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is ψ_{dot a} φ^{dot a}.
-/
def rightAltContraction : rightHanded ⊗ altRightHanded ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := TensorProduct.lift rightAltBi
  comm M := by
    apply TensorProduct.ext'
    intro ψ φ
    change (M.1.map star *ᵥ ψ.toFin2ℂ) ⬝ᵥ (M.1⁻¹.conjTranspose *ᵥ φ.toFin2ℂ) = ψ.toFin2ℂ ⬝ᵥ φ.toFin2ℂ
    have h1 : (M.1)⁻¹ᴴ = ((M.1)⁻¹.map star)ᵀ := by
      rw [conjTranspose]
      exact rfl
    rw [dotProduct_mulVec, h1, vecMul_transpose, mulVec_mulVec]
    have h2 : ((M.1)⁻¹.map star * (M.1).map star) = 1 := by
      refine transpose_inj.mp ?_
      rw [transpose_mul]
      change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
      rw [← @conjTranspose_mul]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
    rw [h2]
    simp only [one_mulVec, vec2_dotProduct, Fin.isValue, RightHandedModule.toFin2ℂEquiv_apply,
      AltRightHandedModule.toFin2ℂEquiv_apply]

informal_definition altRightWeylContraction where
  math :≈ "The linear map from altRightHandedWeyl ⊗ rightHandedWeyl to ℂ given by
    summing over components of altRightHandedWeyl and rightHandedWeyl in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ^{dot a} ψ_{dot a}."
  deps :≈ [``rightHanded, ``altRightHanded]

def altRightContraction : altRightHanded ⊗ rightHanded ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := TensorProduct.lift altRightBi
  comm M := by
    apply TensorProduct.ext'
    intro φ ψ
    change (M.1⁻¹.conjTranspose *ᵥ φ.toFin2ℂ) ⬝ᵥ (M.1.map star *ᵥ ψ.toFin2ℂ) = φ.toFin2ℂ ⬝ᵥ ψ.toFin2ℂ
    have h1 : (M.1)⁻¹ᴴ = ((M.1)⁻¹.map star)ᵀ := by
      rw [conjTranspose]
      exact rfl
    rw [dotProduct_mulVec, h1, mulVec_transpose, vecMul_vecMul]
    have h2 : ((M.1)⁻¹.map star * (M.1).map star) = 1 := by
      refine transpose_inj.mp ?_
      rw [transpose_mul]
      change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
      rw [← @conjTranspose_mul]
      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
    rw [h2]
    simp only [vecMul_one, vec2_dotProduct, Fin.isValue, AltRightHandedModule.toFin2ℂEquiv_apply,
      RightHandedModule.toFin2ℂEquiv_apply]

lemma leftAltContraction_apply_symm (ψ : leftHanded) (φ : altLeftHanded) :
    leftAltContraction.hom (ψ ⊗ₜ φ) = altLeftContraction.hom (φ ⊗ₜ ψ) := by
  rw [altLeftContraction_hom_tmul, leftAltContraction_hom_tmul]
  exact dotProduct_comm ψ.toFin2ℂ φ.toFin2ℂ

/-- A manifestation of the statement that `ψ ψ' = - ψ' ψ` where `ψ` and `ψ'`
  are `leftHandedWeyl`. -/
lemma leftAltContraction_apply_leftHandedAltEquiv (ψ ψ' : leftHanded) :
    leftAltContraction.hom (ψ ⊗ₜ leftHandedAltEquiv.hom.hom ψ') =
    - leftAltContraction.hom (ψ' ⊗ₜ leftHandedAltEquiv.hom.hom ψ) := by
  rw [leftAltContraction_hom_tmul, leftAltContraction_hom_tmul,
    leftHandedAltEquiv_hom_hom_apply, leftHandedAltEquiv_hom_hom_apply]
  simp only [CategoryTheory.Monoidal.transportStruct_tensorUnit,
    CategoryTheory.Equivalence.symm_functor, Action.functorCategoryEquivalence_inverse,
    Action.FunctorCategoryEquivalence.inverse_obj_V, CategoryTheory.Monoidal.tensorUnit_obj,
    cons_mulVec, cons_dotProduct, zero_mul, one_mul, dotProduct_empty, add_zero, zero_add, neg_mul,
    empty_mulVec, LinearEquiv.apply_symm_apply, dotProduct_cons, mul_neg, neg_add_rev, neg_neg]
  ring

/-- A manifestation of the statement that `φ φ' = - φ' φ` where `φ` and `φ'` are
  `altLeftHandedWeyl`. -/
lemma leftAltContraction_apply_leftHandedAltEquiv_inv (φ φ' : altLeftHanded) :
    leftAltContraction.hom (leftHandedAltEquiv.inv.hom φ ⊗ₜ φ') =
    - leftAltContraction.hom (leftHandedAltEquiv.inv.hom φ' ⊗ₜ φ) := by
  rw [leftAltContraction_hom_tmul, leftAltContraction_hom_tmul,
    leftHandedAltEquiv_inv_hom_apply, leftHandedAltEquiv_inv_hom_apply]
  simp only [CategoryTheory.Monoidal.transportStruct_tensorUnit,
    CategoryTheory.Equivalence.symm_functor, Action.functorCategoryEquivalence_inverse,
    Action.FunctorCategoryEquivalence.inverse_obj_V, CategoryTheory.Monoidal.tensorUnit_obj,
    cons_mulVec, cons_dotProduct, zero_mul, neg_mul, one_mul, dotProduct_empty, add_zero, zero_add,
    empty_mulVec, LinearEquiv.apply_symm_apply, neg_add_rev, neg_neg]
  ring

informal_lemma leftAltWeylContraction_symm_altLeftWeylContraction where
  math :≈ "The linear map altLeftWeylContraction is leftAltWeylContraction composed
    with the braiding of the tensor product."
  deps :≈ [``leftAltContraction, ``altLeftContraction]

informal_lemma altLeftWeylContraction_invariant where
  math :≈ "The contraction altLeftWeylContraction is invariant with respect to
    the action of SL(2,C) on leftHandedWeyl and altLeftHandedWeyl."
  deps :≈ [``altLeftContraction]


informal_lemma rightAltWeylContraction_invariant where
  math :≈ "The contraction rightAltWeylContraction is invariant with respect to
    the action of SL(2,C) on rightHandedWeyl and altRightHandedWeyl."
  deps :≈ [``rightAltContraction]

informal_lemma rightAltWeylContraction_symm_altRightWeylContraction where
  math :≈ "The linear map altRightWeylContraction is rightAltWeylContraction composed
    with the braiding of the tensor product."
  deps :≈ [``rightAltContraction, ``altRightWeylContraction]

informal_lemma altRightWeylContraction_invariant where
  math :≈ "The contraction altRightWeylContraction is invariant with respect to
    the action of SL(2,C) on rightHandedWeyl and altRightHandedWeyl."
  deps :≈ [``altRightWeylContraction]


end
end Fermion
