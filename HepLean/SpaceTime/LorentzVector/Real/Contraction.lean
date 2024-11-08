/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Real.Basic
/-!

# Contraction of Real Lorentz vectors

-/

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open SpaceTime
open CategoryTheory.MonoidalCategory
namespace Lorentz

variable {d : ℕ}

/-- The bi-linear map corresponding to contraction of a contravariant Lorentz vector with a
  covariant Lorentz vector. -/
def contrModCoModBi (d : ℕ) : ContrMod d →ₗ[ℝ] CoMod d →ₗ[ℝ] ℝ where
  toFun ψ := {
    toFun := fun φ => ψ.toFin1dℝ ⬝ᵥ φ.toFin1dℝ,
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
def coModContrModBi (d : ℕ) : CoMod d →ₗ[ℝ] ContrMod d →ₗ[ℝ] ℝ where
  toFun φ := {
    toFun := fun ψ => φ.toFin1dℝ ⬝ᵥ ψ.toFin1dℝ,
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

/-- The linear map from Contr d ⊗ Co d to ℝ given by
    summing over components of contravariant Lorentz vector and
    covariant Lorentz vector in the
    standard basis (i.e. the dot product).
    In terms of index notation this is the contraction is ψⁱ φᵢ. -/
def contrCoContract : Contr d ⊗ Co d ⟶ 𝟙_ (Rep ℝ (LorentzGroup d)) where
  hom := TensorProduct.lift (contrModCoModBi d)
  comm M := TensorProduct.ext' fun ψ φ => by
    change (M.1 *ᵥ ψ.toFin1dℝ)  ⬝ᵥ ((LorentzGroup.transpose M⁻¹).1 *ᵥ φ.toFin1dℝ) = _
    rw [dotProduct_mulVec, LorentzGroup.transpose_val,
      vecMul_transpose, mulVec_mulVec, LorentzGroup.coe_inv, inv_mul_of_invertible M.1]
    simp only [one_mulVec, CategoryTheory.Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.comp_id, lift.tmul]
    rfl

scoped[Lorentz] notation "⟪" ψ "," φ "⟫ₘ" => contrCoContract.hom (ψ ⊗ₜ φ)

lemma contrCoContract_hom_tmul (ψ : Contr d) (φ : Co d) : ⟪ψ, φ⟫ₘ = ψ.toFin1dℝ ⬝ᵥ φ.toFin1dℝ := by
  rfl

/-- The linear map from Co d ⊗ Contr d to ℝ given by
    summing over components of contravariant Lorentz vector and
    covariant Lorentz vector in the
    standard basis (i.e. the dot product).
    In terms of index notation this is the contraction is ψⁱ φᵢ. -/
def coContrContract : Co d ⊗ Contr d ⟶ 𝟙_ (Rep ℝ (LorentzGroup d)) where
  hom := TensorProduct.lift (coModContrModBi d)
  comm M := TensorProduct.ext' fun ψ φ => by
    change ((LorentzGroup.transpose M⁻¹).1 *ᵥ ψ.toFin1dℝ) ⬝ᵥ (M.1 *ᵥ φ.toFin1dℝ)  = _
    rw [dotProduct_mulVec, LorentzGroup.transpose_val, mulVec_transpose, vecMul_vecMul,
      LorentzGroup.coe_inv, inv_mul_of_invertible M.1]
    simp only [vecMul_one, CategoryTheory.Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.comp_id, lift.tmul]
    rfl

scoped[Lorentz] notation "⟪" φ "," ψ "⟫ₘ" => coContrContract.hom (φ ⊗ₜ ψ)

lemma coContrContract_hom_tmul (φ : Co d) (ψ : Contr d) : ⟪φ, ψ⟫ₘ = φ.toFin1dℝ ⬝ᵥ ψ.toFin1dℝ := by
  rfl

/-!

## Symmetry relations

-/

lemma contrCoContract_tmul_symm (φ : Contr d) (ψ : Co d) : ⟪φ, ψ⟫ₘ = ⟪ψ, φ⟫ₘ := by
  rw [contrCoContract_hom_tmul, coContrContract_hom_tmul, dotProduct_comm]

lemma coContrContract_tmul_symm (φ : Co d) (ψ : Contr d) : ⟪φ, ψ⟫ₘ = ⟪ψ, φ⟫ₘ := by
  rw [contrCoContract_tmul_symm]

/-!

## Contracting contr vectors with contr vectors etc.

-/
open CategoryTheory.MonoidalCategory
open CategoryTheory

/-- The linear map from Contr d ⊗ Contr d to ℝ induced by the homomorphism
  `Contr.toCo` and the contraction `contrCoContract`. -/
def contrContrContract : Contr d ⊗ Contr d ⟶ 𝟙_ (Rep ℝ (LorentzGroup d)) :=
  (Contr d ◁ Contr.toCo d) ≫ contrCoContract

scoped[Lorentz] notation "⟪" ψ "," φ "⟫ₘ" => contrContrContract.hom (ψ ⊗ₜ φ)

/-- The linear map from Co d ⊗ Co d to ℝ induced by the homomorphism
  `Co.toContr` and the contraction `coContrContract`. -/
def coCoContract : Co d ⊗ Co d ⟶ 𝟙_ (Rep ℝ (LorentzGroup d)) :=
  (Co d ◁ Co.toContr d) ≫ coContrContract

scoped[Lorentz] notation "⟪" ψ "," φ "⟫ₘ" => coCoContract.hom (ψ ⊗ₜ φ)

end Lorentz
end
