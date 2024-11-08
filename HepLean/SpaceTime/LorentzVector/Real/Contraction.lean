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
open CategoryTheory.MonoidalCategory
open minkowskiMatrix
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

/-- Notation for `contrCoContract` acting on a tmul. -/
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

/-- Notation for `coContrContract` acting on a tmul. -/
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

/-- Notation for `contrContrContract` acting on a tmul. -/
scoped[Lorentz] notation "⟪" ψ "," φ "⟫ₘ" => contrContrContract.hom (ψ ⊗ₜ φ)

lemma contrContrContract_hom_tmul (φ : Contr d) (ψ : Contr d) :
    ⟪φ, ψ⟫ₘ = φ.toFin1dℝ ⬝ᵥ η *ᵥ ψ.toFin1dℝ:= by
  simp only [Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
    contrContrContract, Action.comp_hom, Action.instMonoidalCategory_whiskerLeft_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  erw [contrCoContract_hom_tmul]
  rfl

/-- The linear map from Co d ⊗ Co d to ℝ induced by the homomorphism
  `Co.toContr` and the contraction `coContrContract`. -/
def coCoContract : Co d ⊗ Co d ⟶ 𝟙_ (Rep ℝ (LorentzGroup d)) :=
  (Co d ◁ Co.toContr d) ≫ coContrContract

/-- Notation for `coCoContract` acting on a tmul. -/
scoped[Lorentz] notation "⟪" ψ "," φ "⟫ₘ" => coCoContract.hom (ψ ⊗ₜ φ)

lemma coCoContract_hom_tmul (φ : Co d) (ψ : Co d) :
    ⟪φ, ψ⟫ₘ = φ.toFin1dℝ ⬝ᵥ η *ᵥ ψ.toFin1dℝ:= by
  simp only [Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
    contrContrContract, Action.comp_hom, Action.instMonoidalCategory_whiskerLeft_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]
  erw [coContrContract_hom_tmul]
  rfl

/-!

## Lemmas related to contraction.

We derive the lemmas in main for `contrContrContract`.

-/
namespace contrContrContract

variable (x y : Contr d)

lemma as_sum : ⟪x, y⟫ₘ = x.val (Sum.inl 0) * y.val (Sum.inl 0) -
      ∑ i, x.val (Sum.inr i) * y.val (Sum.inr i)  := by
  rw [contrContrContract_hom_tmul]
  simp only [dotProduct, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mulVec_diagonal,
    Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Sum.elim_inl,
    one_mul, Finset.sum_singleton, Sum.elim_inr, neg_mul, mul_neg, Finset.sum_neg_distrib]
  rfl

lemma symm : ⟪x, y⟫ₘ = ⟪y, x⟫ₘ := by
  rw [as_sum, as_sum]
  congr 1
  rw [mul_comm]
  congr
  funext i
  rw [mul_comm]

lemma dual_mulVec_right : ⟪x, dual Λ *ᵥ y⟫ₘ = ⟪Λ *ᵥ x, y⟫ₘ := by
  rw [contrContrContract_hom_tmul, contrContrContract_hom_tmul]
  simp only [Action.instMonoidalCategory_tensorUnit_V, ContrMod.mulVec_toFin1dℝ, mulVec_mulVec]
  simp only [dual, ← mul_assoc, minkowskiMatrix.sq, one_mul]
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

lemma dual_mulVec_left : ⟪dual Λ *ᵥ x, y⟫ₘ = ⟪x, Λ *ᵥ y⟫ₘ := by
  rw [symm, dual_mulVec_right, symm]

lemma right_parity : ⟪x, (Contr d).ρ LorentzGroup.parity y⟫ₘ =  ∑ i, x.val i * y.val i := by
  rw [as_sum]
  simp only [Action.instMonoidalCategory_tensorUnit_V, Fin.isValue, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  trans x.val (Sum.inl 0) * (((Contr d).ρ LorentzGroup.parity) y).val (Sum.inl 0) +
    ∑ i : Fin d, - (x.val (Sum.inr i) * (((Contr d).ρ LorentzGroup.parity) y).val (Sum.inr i))
  · simp only [Fin.isValue, Finset.sum_neg_distrib]
    rfl
  congr 1
  · change x.val (Sum.inl 0) * (η *ᵥ y.toFin1dℝ) (Sum.inl 0) = _
    simp only [Fin.isValue, mulVec_inl_0, mul_eq_mul_left_iff]
    exact mul_eq_mul_left_iff.mp rfl
  · congr
    funext i
    change - (x.val (Sum.inr i) * ((η *ᵥ y.toFin1dℝ) (Sum.inr i)))  = _
    simp only [mulVec_inr_i, mul_neg, neg_neg, mul_eq_mul_left_iff]
    exact mul_eq_mul_left_iff.mp rfl

lemma self_parity_eq_zero_iff : ⟪y, (Contr d).ρ LorentzGroup.parity y⟫ₘ = 0 ↔ y = 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [right_parity] at h
    have hn := Fintype.sum_eq_zero_iff_of_nonneg (f := fun i => y.val i * y.val i) (fun i => by
      simpa using mul_self_nonneg (y.val i))
    rw [h] at hn
    simp at hn
    apply ContrMod.ext
    funext i
    simpa using congrFun hn i
  · rw [h]
    simp only [Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
      Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, map_zero, tmul_zero]

/-- The metric tensor is non-degenerate. -/
lemma nondegenerate : (∀ (x : Contr d), ⟪x, y⟫ₘ = 0) ↔ y = 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · exact (self_parity_eq_zero_iff _).mp ((symm _ _).trans $ h _)
  · simp [h]

lemma matrix_apply_eq_iff_sub : ⟪x, Λ *ᵥ y⟫ₘ = ⟪x, Λ' *ᵥ y⟫ₘ ↔ ⟪x, (Λ - Λ') *ᵥ y⟫ₘ = 0 := by
  rw [← sub_eq_zero, ← LinearMap.map_sub, ← tmul_sub, ← ContrMod.sub_mulVec Λ Λ' y]

lemma matrix_eq_iff_eq_forall' : (∀ (v : Contr d), (Λ *ᵥ v) = Λ' *ᵥ v) ↔
    ∀ (w v : Contr d), ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, Λ' *ᵥ w⟫ₘ := by
  refine Iff.intro (fun h ↦ fun w v ↦ ?_) (fun h ↦ fun v ↦ ?_)
  · rw [h w]
  · simp only [matrix_apply_eq_iff_sub] at h
    refine sub_eq_zero.1 ?_
    have h1 := h v
    rw [nondegenerate] at h1
    simp only [ContrMod.sub_mulVec] at h1
    exact h1

lemma matrix_eq_iff_eq_forall : Λ = Λ' ↔ ∀ (w v : Contr d), ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, Λ' *ᵥ w⟫ₘ := by
  rw [← matrix_eq_iff_eq_forall']
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · subst h
    exact fun v => rfl
  · rw [← (LinearMap.toMatrix ContrMod.stdBasis ContrMod.stdBasis).toEquiv.symm.apply_eq_iff_eq]
    ext1 v
    exact h v

lemma matrix_eq_id_iff : Λ = 1 ↔ ∀ (w v : Contr d), ⟪v, Λ *ᵥ w⟫ₘ = ⟪v, w⟫ₘ := by
  rw [matrix_eq_iff_eq_forall]
  simp only [Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ContrMod.one_mulVec]

lemma _root_.LorentzGroup.mem_iff_invariant : Λ ∈ LorentzGroup d ↔
    ∀ (w v : Contr d), ⟪Λ *ᵥ v, Λ *ᵥ w⟫ₘ = ⟪v, w⟫ₘ := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · intro x y
    rw [← dual_mulVec_right, ContrMod.mulVec_mulVec]
    have h1 := LorentzGroup.mem_iff_dual_mul_self.mp h
    rw [h1]
    simp only [Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
      Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
      Action.FunctorCategoryEquivalence.functor_obj_obj, ContrMod.one_mulVec]
  · conv at h =>
      intro x y
      rw [← dual_mulVec_right, ContrMod.mulVec_mulVec]
    rw [← matrix_eq_id_iff] at h
    exact LorentzGroup.mem_iff_dual_mul_self.mpr h

lemma _root_.LorentzGroup.mem_iff_norm : Λ ∈ LorentzGroup d ↔
    ∀ (w : Contr d), ⟪Λ *ᵥ w, Λ *ᵥ w⟫ₘ = ⟪w, w⟫ₘ := by
  rw [LorentzGroup.mem_iff_invariant]
  refine Iff.intro (fun h x => h x x) (fun h x y => ?_)
  have hp := h (x + y)
  have hn := h (x - y)
  rw [ContrMod.mulVec_add, tmul_add, add_tmul, add_tmul, tmul_add, add_tmul, add_tmul] at hp
  rw [ContrMod.mulVec_sub, tmul_sub, sub_tmul, sub_tmul, tmul_sub, sub_tmul, sub_tmul] at hn
  simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply] at hp hn
  rw [symm (Λ *ᵥ y) (Λ *ᵥ x), symm y x] at hp hn
  let e :  𝟙_ (Rep ℝ ↑(LorentzGroup d)) ≃ₗ[ℝ] ℝ :=
    LinearEquiv.refl ℝ (CoeSort.coe (𝟙_ (Rep ℝ ↑(LorentzGroup d))))
  apply e.injective
  have hp' := e.injective.eq_iff.mpr hp
  have hn' := e.injective.eq_iff.mpr hn
  simp only [Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, map_add, map_sub] at hp' hn'
  linear_combination  (norm := ring_nf) (1 / 4) * hp' + (-1/ 4) * hn'
  rw [symm (Λ *ᵥ y) (Λ *ᵥ x), symm y x]
  simp only [Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, add_sub_cancel, neg_add_cancel, e]

end contrContrContract

end Lorentz
end
