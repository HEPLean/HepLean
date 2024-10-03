/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Informal
import HepLean.SpaceTime.SL2C.Basic
import Mathlib.RepresentationTheory.Rep
import HepLean.Tensors.Basic
import HepLean.SpaceTime.WeylFermion.Modules
import Mathlib.Logic.Equiv.TransferInstance
/-!

# Weyl fermions

A good reference for the material in this file is:
https://particle.physics.ucdavis.edu/modernsusy/slides/slideimages/spinorfeynrules.pdf

-/

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

/-- The vector space ℂ^2 carrying the fundamental representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ_a. -/
def leftHanded : Rep ℂ SL(2,ℂ) := Rep.of {
  toFun := fun M => {
    toFun := fun (ψ : LeftHandedModule) =>
      LeftHandedModule.toFin2ℂEquiv.symm (M.1 *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    simp only [SpecialLinearGroup.coe_mul]
    ext1 x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply, LinearEquiv.apply_symm_apply,
      mulVec_mulVec]}

/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)ᵀ. In index notation corresponds to a Weyl fermion with indices ψ^a. -/
def altLeftHanded : Rep ℂ SL(2,ℂ) := Rep.of {
  toFun := fun M => {
    toFun := fun (ψ : AltLeftHandedModule) =>
      AltLeftHandedModule.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    rw [Matrix.mul_inv_rev]
    exact transpose_mul _ _}

/-- The vector space ℂ^2 carrying the conjugate representation of SL(2,C).
  In index notation corresponds to a Weyl fermion with indices ψ_{dot a}. -/
def rightHanded : Rep ℂ SL(2,ℂ) := Rep.of {
  toFun := fun M => {
    toFun := fun (ψ : RightHandedModule) =>
      RightHandedModule.toFin2ℂEquiv.symm (M.1.map star *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, RCLike.star_def, Matrix.map_mul, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.mul_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec]}

/-- The vector space ℂ^2 carrying the representation of SL(2,C) given by
    M → (M⁻¹)^†.
    In index notation this corresponds to a Weyl fermion with index `ψ^{dot a}`. -/
def altRightHanded : Rep ℂ SL(2,ℂ) := Rep.of {
  toFun := fun M => {
    toFun := fun (ψ : AltRightHandedModule) =>
      AltRightHandedModule.toFin2ℂEquiv.symm ((M.1⁻¹).conjTranspose *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp [mulVec_add]
    map_smul' := by
      intro r ψ
      simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' := fun M N => by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    rw [Matrix.mul_inv_rev]
    exact conjTranspose_mul _ _}

/-!

## Equivalences between Weyl fermion vector spaces.

-/

/-- The morphism between the representation `leftHanded` and the representation
  `altLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def leftHandedToAlt : leftHanded ⟶ altLeftHanded where
  hom := {
    toFun := fun ψ => AltLeftHandedModule.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp only [mulVec_add, LinearEquiv.map_add]
    map_smul' := by
      intro a ψ
      simp only [mulVec_smul, LinearEquiv.map_smul]
      rfl}
  comm := by
    intro M
    refine LinearMap.ext (fun ψ => ?_)
    change AltLeftHandedModule.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ M.1 *ᵥ ψ.val) =
      AltLeftHandedModule.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ !![0, 1; -1, 0] *ᵥ ψ.val)
    apply congrArg
    rw [mulVec_mulVec, mulVec_mulVec, SpaceTime.SL2C.inverse_coe, eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp

lemma leftHandedToAlt_hom_apply (ψ : leftHanded) :
    leftHandedToAlt.hom ψ =
    AltLeftHandedModule.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The morphism from `altLeftHanded` to
  `leftHanded` defined by multiplying an element of
  altLeftHandedWeyl by the matrix `εₐ₁ₐ₂ = !![0, -1; 1, 0]`. -/
def leftHandedAltTo : altLeftHanded ⟶ leftHanded where
  hom := {
    toFun := fun ψ =>
      LeftHandedModule.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ),
    map_add' := by
      intro ψ ψ'
      simp only [map_add]
      rw [mulVec_add, LinearEquiv.map_add]
    map_smul' := by
      intro a ψ
      simp only [LinearEquiv.map_smul]
      rw [mulVec_smul, LinearEquiv.map_smul]
      rfl}
  comm := by
    intro M
    refine LinearMap.ext (fun ψ => ?_)
    change LeftHandedModule.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ (M.1⁻¹)ᵀ *ᵥ ψ.val) =
      LeftHandedModule.toFin2ℂEquiv.symm (M.1 *ᵥ !![0, -1; 1, 0] *ᵥ ψ.val)
    rw [EquivLike.apply_eq_iff_eq, mulVec_mulVec, mulVec_mulVec, SpaceTime.SL2C.inverse_coe,
      eta_fin_two M.1]
    refine congrFun (congrArg _ ?_) _
    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
    simp

lemma leftHandedAltTo_hom_apply (ψ : altLeftHanded) :
    leftHandedAltTo.hom ψ =
    LeftHandedModule.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl

/-- The equivalence between the representation `leftHanded` and the representation
  `altLeftHanded` defined by multiplying an element of
  `leftHanded` by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`. -/
def leftHandedAltEquiv : leftHanded ≅ altLeftHanded where
  hom := leftHandedToAlt
  inv := leftHandedAltTo
  hom_inv_id := by
    ext ψ
    simp only [Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply, Action.id_hom,
      ModuleCat.id_apply]
    rw [leftHandedAltTo_hom_apply, leftHandedToAlt_hom_apply]
    rw [AltLeftHandedModule.toFin2ℂ, LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, -1; (1 : ℂ), 0] * !![0, 1; -1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl
  inv_hom_id := by
    ext ψ
    simp only [Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply, Action.id_hom,
      ModuleCat.id_apply]
    rw [leftHandedAltTo_hom_apply, leftHandedToAlt_hom_apply, LeftHandedModule.toFin2ℂ,
      LinearEquiv.apply_symm_apply, mulVec_mulVec]
    rw [show (!![0, (1 : ℂ); -1, 0] * !![0, -1; 1, 0]) = 1 by simpa using Eq.symm one_fin_two]
    rw [one_mulVec]
    rfl

lemma leftHandedAltEquiv_hom_hom_apply (ψ : leftHanded) :
    leftHandedAltEquiv.hom.hom ψ =
    AltLeftHandedModule.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ ψ.toFin2ℂ) := rfl

lemma leftHandedAltEquiv_inv_hom_apply (ψ : altLeftHanded) :
    leftHandedAltEquiv.inv.hom ψ =
    LeftHandedModule.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ ψ.toFin2ℂ) := rfl

informal_definition rightHandedWeylAltEquiv where
  math :≈ "The linear equiv between rightHandedWeyl and altRightHandedWeyl given
    by multiplying an element of rightHandedWeyl by the matrix `εᵃ⁰ᵃ¹ = !![0, 1; -1, 0]]`"
  deps :≈ [``rightHanded, ``altRightHanded]

informal_lemma rightHandedWeylAltEquiv_equivariant where
  math :≈ "The linear equiv rightHandedWeylAltEquiv is equivariant with respect to the
    action of SL(2,C) on rightHandedWeyl and altRightHandedWeyl."
  deps :≈ [``rightHandedWeylAltEquiv]

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

informal_definition rightAltWeylContraction where
  math :≈ "The linear map from rightHandedWeyl ⊗ altRightHandedWeyl to ℂ given by
    summing over components of rightHandedWeyl and altRightHandedWeyl in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is ψ_{dot a} φ^{dot a}."
  deps :≈ [``rightHanded, ``altRightHanded]

informal_lemma rightAltWeylContraction_invariant where
  math :≈ "The contraction rightAltWeylContraction is invariant with respect to
    the action of SL(2,C) on rightHandedWeyl and altRightHandedWeyl."
  deps :≈ [``rightAltWeylContraction]

informal_definition altRightWeylContraction where
  math :≈ "The linear map from altRightHandedWeyl ⊗ rightHandedWeyl to ℂ given by
    summing over components of altRightHandedWeyl and rightHandedWeyl in the
    standard basis (i.e. the dot product)."
  physics :≈ "The contraction of a right-handed Weyl fermion with a left-handed Weyl fermion.
    In index notation this is φ^{dot a} ψ_{dot a}."
  deps :≈ [``rightHanded, ``altRightHanded]

informal_lemma rightAltWeylContraction_symm_altRightWeylContraction where
  math :≈ "The linear map altRightWeylContraction is rightAltWeylContraction composed
    with the braiding of the tensor product."
  deps :≈ [``rightAltWeylContraction, ``altRightWeylContraction]

informal_lemma altRightWeylContraction_invariant where
  math :≈ "The contraction altRightWeylContraction is invariant with respect to
    the action of SL(2,C) on rightHandedWeyl and altRightHandedWeyl."
  deps :≈ [``altRightWeylContraction]

end

end Fermion
