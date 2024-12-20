/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.Group.Restricted
/-!
# The group SL(2, ℂ) and it's relation to the Lorentz group

The aim of this file is to give the relationship between `SL(2, ℂ)` and the Lorentz group.

-/
namespace Lorentz

open Matrix
open MatrixGroups
open Complex

namespace SL2C

noncomputable section

/-!

## Some basic properties about SL(2, ℂ)

Possibly to be moved to mathlib at some point.
-/

lemma inverse_coe (M : SL(2, ℂ)) : M.1⁻¹ = (M⁻¹).1 := by
  apply Matrix.inv_inj
  simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true,
    nonsing_inv_nonsing_inv, SpecialLinearGroup.coe_inv]
  have h1 : IsUnit M.1.det := by
    simp
  rw [Matrix.inv_adjugate M.1 h1]
  · simp
  · simp

lemma transpose_coe (M : SL(2, ℂ)) : M.1ᵀ = (M.transpose).1 := rfl
/-!

## Representation of SL(2, ℂ) on spacetime

Through the correspondence between spacetime and self-adjoint matrices,
we can define a representation a representation of `SL(2, ℂ)` on spacetime.

-/

/-- Given an element `M ∈ SL(2, ℂ)` the linear map from `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` to
  itself defined by `A ↦ M * A * Mᴴ`. -/
@[simps!]
def toSelfAdjointMap (M : SL(2, ℂ)) :
    selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun A := ⟨M.1 * A.1 * Matrix.conjTranspose M,
    by
      noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
        conjTranspose_mul, conjTranspose_conjTranspose,
        (star_eq_conjTranspose A.1).symm.trans $ selfAdjoint.mem_iff.mp A.2]⟩
  map_add' A B := by
    simp only [AddSubgroup.coe_add, AddMemClass.mk_add_mk, Subtype.mk.injEq]
    noncomm_ring [AddSubmonoid.coe_add, AddSubgroup.coe_toAddSubmonoid, AddSubmonoid.mk_add_mk,
      Subtype.mk.injEq]
  map_smul' r A := by
    noncomm_ring [selfAdjoint.val_smul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      RingHom.id_apply]

lemma toSelfAdjointMap_apply_det (M : SL(2, ℂ)) (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    det ((toSelfAdjointMap M) A).1 = det A.1 := by
  simp only [LinearMap.coe_mk, AddHom.coe_mk, toSelfAdjointMap, det_mul,
    selfAdjoint.mem_iff, det_conjTranspose, det_mul, det_one, RingHom.id_apply]
  simp only [SpecialLinearGroup.det_coe, one_mul, star_one, mul_one]

lemma toSelfAdjointMap_apply_σSAL_inl (M : SL(2, ℂ)) :
    toSelfAdjointMap M (PauliMatrix.σSAL (Sum.inl 0)) =
    ((‖M.1 0 0‖ ^ 2 + ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2) •
      PauliMatrix.σSAL (Sum.inl 0) +
    (- ((M.1 0 1).re * (M.1 1 1).re + (M.1 0 1).im * (M.1 1 1).im +
      (M.1 0 0).im * (M.1 1 0).im + (M.1 0 0).re * (M.1 1 0).re)) • PauliMatrix.σSAL (Sum.inr 0)
    + ((- (M.1 0 0).re * (M.1 1 0).im + ↑(M.1 1 0).re * (M.1 0 0).im
      - (M.1 0 1).re * (M.1 1 1).im + (M.1 0 1).im * (M.1 1 1).re)) • PauliMatrix.σSAL (Sum.inr 1)
    + ((- ‖M.1 0 0‖ ^ 2 - ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2) •
      PauliMatrix.σSAL (Sum.inr 2) := by
  simp only [toSelfAdjointMap, PauliMatrix.σSAL, Fin.isValue, Basis.coe_mk, PauliMatrix.σSAL',
    PauliMatrix.σ0, LinearMap.coe_mk, AddHom.coe_mk, norm_eq_abs, neg_add_rev, PauliMatrix.σ1,
    neg_of, neg_cons, neg_zero, neg_empty, neg_mul, PauliMatrix.σ2, neg_neg, PauliMatrix.σ3]
  ext1
  simp only [Fin.isValue, AddSubgroup.coe_add, selfAdjoint.val_smul, smul_of, smul_cons, real_smul,
    ofReal_div, ofReal_add, ofReal_pow, ofReal_ofNat, mul_one, smul_zero, smul_empty, smul_neg,
    ofReal_neg, ofReal_mul, neg_add_rev, neg_neg, of_add_of, add_cons, head_cons, add_zero,
    tail_cons, zero_add, empty_add_empty, ofReal_sub]
  conv => lhs; erw [← eta_fin_two 1, mul_one]
  conv => lhs; lhs; rw [eta_fin_two M.1]
  conv => lhs; rhs; rw [eta_fin_two M.1ᴴ]
  simp only [Fin.isValue, conjTranspose_apply, RCLike.star_def, cons_mul, Nat.succ_eq_add_one,
    Nat.reduceAdd, vecMul_cons, head_cons, smul_cons, smul_eq_mul, smul_empty, tail_cons,
    empty_vecMul, add_zero, add_cons, empty_add_empty, empty_mul, Equiv.symm_apply_apply,
    EmbeddingLike.apply_eq_iff_eq]
  rw [mul_conj', mul_conj', mul_conj', mul_conj']
  ext x y
  match x, y with
  | 0, 0 =>
    simp only [Fin.isValue, norm_eq_abs, cons_val', cons_val_zero, empty_val', cons_val_fin_one]
    ring_nf
  | 0, 1 =>
    simp only [Fin.isValue, norm_eq_abs, cons_val', cons_val_one, head_cons, empty_val',
      cons_val_fin_one, cons_val_zero]
    ring_nf
    rw [← re_add_im (M.1 0 0), ← re_add_im (M.1 0 1), ← re_add_im (M.1 1 0), ← re_add_im (M.1 1 1)]
    simp only [Fin.isValue, map_add, conj_ofReal, _root_.map_mul, conj_I, mul_neg, add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im,
      mul_im, zero_add]
    ring_nf
    simp only [Fin.isValue, I_sq, mul_neg, mul_one, neg_mul, neg_neg, one_mul, sub_neg_eq_add]
    ring
  | 1, 0 =>
    simp only [Fin.isValue, norm_eq_abs, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
      cons_val_one, head_fin_const]
    ring_nf
    rw [← re_add_im (M.1 0 0), ← re_add_im (M.1 0 1), ← re_add_im (M.1 1 0), ← re_add_im (M.1 1 1)]
    simp only [Fin.isValue, map_add, conj_ofReal, _root_.map_mul, conj_I, mul_neg, add_re,
      ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im,
      mul_im, zero_add]
    ring_nf
    simp only [Fin.isValue, I_sq, mul_neg, mul_one, neg_mul, neg_neg, one_mul, sub_neg_eq_add]
    ring
  | 1, 1 =>
    simp only [Fin.isValue, norm_eq_abs, cons_val', cons_val_one, head_cons, empty_val',
      cons_val_fin_one, head_fin_const]
    ring_nf

/-- The monoid homomorphisms from `SL(2, ℂ)` to matrices indexed by `Fin 1 ⊕ Fin 3`
  formed by the action `M A Mᴴ`. -/
def toMatrix : SL(2, ℂ) →* Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ where
  toFun M := LinearMap.toMatrix PauliMatrix.σSAL PauliMatrix.σSAL (toSelfAdjointMap M)
  map_one' := by
    simp only [toSelfAdjointMap, SpecialLinearGroup.coe_one, one_mul, conjTranspose_one,
      mul_one, Subtype.coe_eta]
    erw [LinearMap.toMatrix_one]
  map_mul' M N := by
    simp only
    rw [← LinearMap.toMatrix_mul]
    apply congrArg
    ext1 x
    simp only [toSelfAdjointMap, SpecialLinearGroup.coe_mul, conjTranspose_mul,
      LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply, Subtype.mk.injEq]
    noncomm_ring

open Lorentz in
lemma toMatrix_apply_contrMod (M : SL(2, ℂ)) (v : ContrMod 3) :
    (toMatrix M) *ᵥ v = ContrMod.toSelfAdjoint.symm
    ((toSelfAdjointMap M) (ContrMod.toSelfAdjoint v)) := by
  simp only [ContrMod.mulVec, toMatrix, MonoidHom.coe_mk, OneHom.coe_mk]
  obtain ⟨a, ha⟩ := ContrMod.toSelfAdjoint.symm.surjective v
  subst ha
  rw [LinearEquiv.apply_symm_apply]
  simp only [ContrMod.toSelfAdjoint, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply]
  change ContrMod.toFin1dℝEquiv.symm
    ((((LinearMap.toMatrix PauliMatrix.σSAL PauliMatrix.σSAL) (toSelfAdjointMap M)))
    *ᵥ (((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 1 ⊕ Fin 3)) (PauliMatrix.σSAL.repr a)))) = _
  apply congrArg
  erw [LinearMap.toMatrix_mulVec_repr]
  rfl

lemma toMatrix_mem_lorentzGroup (M : SL(2, ℂ)) : toMatrix M ∈ LorentzGroup 3 := by
  rw [LorentzGroup.mem_iff_norm]
  intro x
  apply ofReal_injective
  rw [Lorentz.contrContrContractField.same_eq_det_toSelfAdjoint]
  rw [toMatrix_apply_contrMod]
  rw [LinearEquiv.apply_symm_apply]
  rw [toSelfAdjointMap_apply_det]
  rw [Lorentz.contrContrContractField.same_eq_det_toSelfAdjoint]

/-- The group homomorphism from `SL(2, ℂ)` to the Lorentz group `𝓛`. -/
@[simps!]
def toLorentzGroup : SL(2, ℂ) →* LorentzGroup 3 where
  toFun M := ⟨toMatrix M, toMatrix_mem_lorentzGroup M⟩
  map_one' := by
    simp only [_root_.map_one]
    rfl
  map_mul' M N := by
    ext1
    simp only [_root_.map_mul, lorentzGroupIsGroup_mul_coe]

lemma toLorentzGroup_eq_σSAL (M : SL(2, ℂ)) :
    toLorentzGroup M = LinearMap.toMatrix
    PauliMatrix.σSAL PauliMatrix.σSAL (toSelfAdjointMap M) := by
  rfl

lemma toSelfAdjointMap_basis (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjointMap M (PauliMatrix.σSAL i) =
    ∑ j, (toLorentzGroup M).1 j i • PauliMatrix.σSAL j := by
  rw [toLorentzGroup_eq_σSAL]
  simp only [LinearMap.toMatrix_apply, Finset.univ_unique,
    Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
  nth_rewrite 1 [← (Basis.sum_repr PauliMatrix.σSAL
    ((toSelfAdjointMap M) (PauliMatrix.σSAL i)))]
  rfl

lemma toSelfAdjointMap_σSA (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjointMap M (PauliMatrix.σSA i) =
    ∑ j, (toLorentzGroup M⁻¹).1 i j • PauliMatrix.σSA j := by
  have h1 : (toLorentzGroup M⁻¹).1 = minkowskiMatrix.dual (toLorentzGroup M).1 := by
    simp
  simp only [h1]
  rw [PauliMatrix.σSA_minkowskiMetric_σSAL, _root_.map_smul]
  rw [toSelfAdjointMap_basis]
  rw [Finset.smul_sum]
  apply congrArg
  funext j
  rw [smul_smul, PauliMatrix.σSA_minkowskiMetric_σSAL, smul_smul]
  apply congrFun
  apply congrArg
  exact Eq.symm (minkowskiMatrix.dual_apply_minkowskiMatrix ((toLorentzGroup M).1) i j)

/-- The first column of the Lorentz matrix formed from an element of `SL(2, ℂ)`. -/
lemma toLorentzGroup_fst_col (M : SL(2, ℂ)) :
    (fun μ => (toLorentzGroup M).1 μ (Sum.inl 0)) = fun μ =>
      match μ with
      | Sum.inl 0 => ((‖M.1 0 0‖ ^ 2 + ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2)
      | Sum.inr 0 => (- ((M.1 0 1).re * (M.1 1 1).re + (M.1 0 1).im * (M.1 1 1).im +
        (M.1 0 0).im * (M.1 1 0).im + (M.1 0 0).re * (M.1 1 0).re))
      | Sum.inr 1 => ((- (M.1 0 0).re * (M.1 1 0).im + ↑(M.1 1 0).re * (M.1 0 0).im
        - (M.1 0 1).re * (M.1 1 1).im + (M.1 0 1).im * (M.1 1 1).re))
      | Sum.inr 2 => ((- ‖M.1 0 0‖ ^ 2 - ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2) := by
  let k : Fin 1 ⊕ Fin 3 → ℝ := fun μ =>
    match μ with
    | Sum.inl 0 => ((‖M.1 0 0‖ ^ 2 + ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2)
    | Sum.inr 0 => (- ((M.1 0 1).re * (M.1 1 1).re + (M.1 0 1).im * (M.1 1 1).im +
      (M.1 0 0).im * (M.1 1 0).im + (M.1 0 0).re * (M.1 1 0).re))
    | Sum.inr 1 => ((- (M.1 0 0).re * (M.1 1 0).im + ↑(M.1 1 0).re * (M.1 0 0).im
      - (M.1 0 1).re * (M.1 1 1).im + (M.1 0 1).im * (M.1 1 1).re))
    | Sum.inr 2 => ((- ‖M.1 0 0‖ ^ 2 - ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2)
  change (fun μ => (toLorentzGroup M).1 μ (Sum.inl 0)) = k
  have h1 : toSelfAdjointMap M (PauliMatrix.σSAL (Sum.inl 0)) = ∑ μ, k μ • PauliMatrix.σSAL μ := by
    simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton, Fin.sum_univ_three]
    rw [toSelfAdjointMap_apply_σSAL_inl]
    abel
  rw [toSelfAdjointMap_basis] at h1
  have h1x := sub_eq_zero_of_eq h1
  rw [← Finset.sum_sub_distrib] at h1x
  funext μ
  refine sub_eq_zero.mp ?_
  refine Fintype.linearIndependent_iff.mp PauliMatrix.σSAL.linearIndependent
    (fun x => ((toLorentzGroup M).1 x (Sum.inl 0) - k x)) ?_ μ
  rw [← h1x]
  congr
  funext x
  exact sub_smul ((toLorentzGroup M).1 x (Sum.inl 0)) (k x) (PauliMatrix.σSAL x)

/-- The first element of the image of `SL(2, ℂ)` in the Lorentz group. -/
lemma toLorentzGroup_inl_inl (M : SL(2, ℂ)) :
    (toLorentzGroup M).1 (Sum.inl 0) (Sum.inl 0) =
    ((‖M.1 0 0‖ ^ 2 + ‖M.1 0 1‖ ^ 2 + ‖M.1 1 0‖ ^ 2 + ‖M.1 1 1‖ ^ 2) / 2) := by
  change (fun μ => (toLorentzGroup M).1 μ (Sum.inl 0)) (Sum.inl 0) = _
  rw [toLorentzGroup_fst_col]

/-- The image of `SL(2, ℂ)` in the Lorentz group is orthochronous. -/
lemma toLorentzGroup_isOrthochronous (M : SL(2, ℂ)) :
    LorentzGroup.IsOrthochronous (toLorentzGroup M) := by
  rw [LorentzGroup.IsOrthochronous]
  rw [toLorentzGroup_inl_inl]
  apply div_nonneg
  · apply add_nonneg
    · apply add_nonneg
      · apply add_nonneg
        · exact sq_nonneg _
        · exact sq_nonneg _
      · exact sq_nonneg _
    · exact sq_nonneg _
  · exact zero_le_two

/-!

## Homomorphism to the restricted Lorentz group

The homomorphism `toLorentzGroup` restricts to a homomorphism to the restricted Lorentz group.
In this section we will define this homomorphism.

-/

informal_lemma toLorentzGroup_det_one where
  math :≈ "The determinant of the image of `SL(2, ℂ)` in the Lorentz group is one."
  deps :≈ [``toLorentzGroup]

informal_lemma toRestrictedLorentzGroup where
  math :≈ "The homomorphism from `SL(2, ℂ)` to the restricted Lorentz group."
  deps :≈ [``toLorentzGroup, ``toLorentzGroup_det_one, ``toLorentzGroup_isOrthochronous,
    ``LorentzGroup.Restricted]

/-! TODO: Define homomorphism from `SL(2, ℂ)` to the restricted Lorentz group. -/
end
end SL2C

end Lorentz
