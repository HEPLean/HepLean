/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Complex.Basic
/-!

# Contraction of Lorentz vectors

-/

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open SpaceTime
open CategoryTheory.MonoidalCategory
namespace Lorentz

/-- The bi-linear map corresponding to contraction of a contravariant Lorentz vector with a
  covariant Lorentz vector. -/
def contrCoContrBi : complexContr →ₗ[ℂ] complexCo →ₗ[ℂ] ℂ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin13ℂ ⬝ᵥ φ.toFin13ℂ,
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

/-- The bi-linear map corresponding to contraction of a covariant Lorentz vector with a
  contravariant Lorentz vector. -/
def contrContrCoBi : complexCo →ₗ[ℂ] complexContr →ₗ[ℂ] ℂ where
  toFun φ := {
    toFun := fun ψ => φ.toFin13ℂ ⬝ᵥ ψ.toFin13ℂ,
    map_add' := by
      intro ψ ψ'
      simp only [map_add]
      rw [dotProduct_add]
    map_smul' := by
      intro r ψ
      simp only [LinearEquiv.map_smul]
      rw [dotProduct_smul]
      rfl}
  map_add' φ φ' := by
    refine LinearMap.ext (fun ψ => ?_)
    simp only [map_add, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [add_dotProduct]
  map_smul' r φ := by
    refine LinearMap.ext (fun ψ => ?_)
    simp only [LinearEquiv.map_smul, LinearMap.coe_mk, AddHom.coe_mk]
    rw [smul_dotProduct]
    rfl

/-- The linear map from complexContr ⊗ complexCo to ℂ given by
    summing over components of contravariant Lorentz vector and
    covariant Lorentz vector in the
    standard basis (i.e. the dot product).
    In terms of index notation this is the contraction is ψⁱ φᵢ. -/
def contrCoContraction : complexContr ⊗ complexCo ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := TensorProduct.lift contrCoContrBi
  comm M := TensorProduct.ext' fun ψ φ => by
    change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) *ᵥ ψ.toFin13ℂ) ⬝ᵥ
      ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ φ.toFin13ℂ) = ψ.toFin13ℂ ⬝ᵥ φ.toFin13ℂ
    rw [dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
    rw [inv_mul_of_invertible (LorentzGroup.toComplex (SL2C.toLorentzGroup M))]
    simp

lemma contrCoContraction_hom_tmul (ψ : complexContr) (φ : complexCo) :
    contrCoContraction.hom (ψ ⊗ₜ φ) = ψ.toFin13ℂ ⬝ᵥ φ.toFin13ℂ := by
  rfl

lemma contrCoContraction_basis (i j : Fin 4) :
    contrCoContraction.hom (complexContrBasisFin4 i ⊗ₜ complexCoBasisFin4 j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [contrCoContraction_hom_tmul]
  simp only [Action.instMonoidalCategory_tensorUnit_V, complexContrBasisFin4, Basis.coe_reindex,
    Function.comp_apply, complexContrBasis_toFin13ℂ, complexCoBasisFin4, complexCoBasis_toFin13ℂ,
    dotProduct_single, mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  simp only [EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, eq_iff_iff, eq_comm]

lemma contrCoContraction_basis' (i j : Fin 1 ⊕ Fin 3) :
    contrCoContraction.hom (complexContrBasis i ⊗ₜ complexCoBasis j) =
    if i = j then (1 : ℂ) else 0 := by
  rw [contrCoContraction_hom_tmul]
  simp only [Action.instMonoidalCategory_tensorUnit_V, complexContrBasisFin4, Basis.coe_reindex,
    Function.comp_apply, complexContrBasis_toFin13ℂ, complexCoBasisFin4, complexCoBasis_toFin13ℂ,
    dotProduct_single, mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

/-- The linear map from complexCo ⊗ complexContr to ℂ given by
    summing over components of covariant Lorentz vector and
    contravariant Lorentz vector in the
    standard basis (i.e. the dot product).
    In terms of index notation this is the contraction is φᵢ ψⁱ. -/
def coContrContraction : complexCo ⊗ complexContr ⟶ 𝟙_ (Rep ℂ SL(2,ℂ)) where
  hom := TensorProduct.lift contrContrCoBi
  comm M := TensorProduct.ext' fun φ ψ => by
    change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ φ.toFin13ℂ) ⬝ᵥ
      ((LorentzGroup.toComplex (SL2C.toLorentzGroup M)) *ᵥ ψ.toFin13ℂ) = φ.toFin13ℂ ⬝ᵥ ψ.toFin13ℂ
    rw [dotProduct_mulVec, mulVec_transpose, vecMul_vecMul]
    rw [inv_mul_of_invertible (LorentzGroup.toComplex (SL2C.toLorentzGroup M))]
    simp

lemma coContrContraction_hom_tmul (φ : complexCo) (ψ : complexContr) :
    coContrContraction.hom (φ ⊗ₜ ψ) = φ.toFin13ℂ ⬝ᵥ ψ.toFin13ℂ := by
  rfl

lemma coContrContraction_basis (i j : Fin 4) :
    coContrContraction.hom (complexCoBasisFin4 i ⊗ₜ complexContrBasisFin4 j) =
    if i.1 = j.1 then (1 : ℂ) else 0 := by
  rw [coContrContraction_hom_tmul]
  simp only [Action.instMonoidalCategory_tensorUnit_V, complexCoBasisFin4, Basis.coe_reindex,
    Function.comp_apply, complexCoBasis_toFin13ℂ, complexContrBasisFin4, complexContrBasis_toFin13ℂ,
    dotProduct_single, mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  simp only [EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, eq_iff_iff, eq_comm]

lemma coContrContraction_basis' (i j : Fin 1 ⊕ Fin 3) :
    coContrContraction.hom (complexCoBasis i ⊗ₜ complexContrBasis j) =
    if i = j then (1 : ℂ) else 0 := by
  rw [coContrContraction_hom_tmul]
  simp only [Action.instMonoidalCategory_tensorUnit_V, complexCoBasisFin4, Basis.coe_reindex,
    Function.comp_apply, complexCoBasis_toFin13ℂ, complexContrBasisFin4, complexContrBasis_toFin13ℂ,
    dotProduct_single, mul_one]
  rw [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  simp only [EmbeddingLike.apply_eq_iff_eq, Fin.ext_iff, eq_iff_iff, eq_comm]

/-!

## Symmetry

-/

lemma contrCoContraction_tmul_symm (φ : complexContr) (ψ : complexCo) :
    contrCoContraction.hom (φ ⊗ₜ ψ) = coContrContraction.hom (ψ ⊗ₜ φ) := by
  rw [contrCoContraction_hom_tmul, coContrContraction_hom_tmul, dotProduct_comm]

lemma coContrContraction_tmul_symm (φ : complexCo) (ψ : complexContr) :
    coContrContraction.hom (φ ⊗ₜ ψ) = contrCoContraction.hom (ψ ⊗ₜ φ) := by
  rw [contrCoContraction_hom_tmul, coContrContraction_hom_tmul, dotProduct_comm]

end Lorentz
end
