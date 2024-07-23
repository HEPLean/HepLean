/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Real.LorentzAction
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
/-!

# Tensor products of real Lorentz Tensors

-/
noncomputable section

namespace RealLorentzTensor
open TensorProduct
open Set LinearMap Submodule

variable {d : ℕ} {X Y Y' X'  : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype X'] [DecidableEq X']
  (cX : X → Colors) (cY : Y → Colors)


/-!

## The tensorator and properties thereof

-/

/-- An equivalence between `ColorFiber d (Sum.elim cX cY)` and
  `ColorFiber d cX ⊗[ℝ] ColorFiber d cY`. This is related to the `tensorator` of
  the monoidal functor defined by `ColorFiber`, hence the terminology.  -/
def tensorator {cX : X → Colors} {cY : Y → Colors} :
    ColorFiber d (Sum.elim cX cY) ≃ₗ[ℝ] ColorFiber d cX ⊗[ℝ] ColorFiber d cY :=
  (basisColorFiber (Sum.elim cX cY)).equiv (basisProd cX cY) indexValueSumEquiv

lemma tensorator_symm_apply {cX : X → Colors} {cY : Y → Colors}
    (X : ColorFiber d cX ⊗[ℝ] ColorFiber d cY) (i : IndexValue d (Sum.elim cX cY)) :
    (tensorator.symm X) i = (basisProd cX cY).repr X (indexValueSumEquiv i) := by
  rfl

/-! TODO : Move -/
lemma tensorator_mapIso_cond {cX : X → Colors} {cY : Y → Colors} {cX' : X' → Colors}
    {cY' : Y' → Colors} {eX : X ≃ X'} {eY : Y ≃ Y'} (hX : cX = cX' ∘ eX) (hY : cY = cY' ∘ eY) :
    Sum.elim cX cY = Sum.elim cX' cY' ∘ ⇑(eX.sumCongr eY) := by
  subst hX hY
  ext1 x
  simp_all only [Function.comp_apply, Equiv.sumCongr_apply]
  cases x with
  | inl val => simp_all only [Sum.elim_inl, Function.comp_apply, Sum.map_inl]
  | inr val_1 => simp_all only [Sum.elim_inr, Function.comp_apply, Sum.map_inr]

/-- The naturality condition for the `tensorator`. -/
lemma tensorator_mapIso {cX : X → Colors} {cY : Y → Colors} {cX' : X' → Colors}
    {cY' : Y' → Colors} (eX : X ≃ X') (eY : Y ≃ Y') (hX : cX = cX' ∘ eX) (hY : cY = cY' ∘ eY) :
    (mapIsoFiber d (Equiv.sumCongr eX eY) (tensorator_mapIso_cond hX hY)).trans tensorator  =
    tensorator.trans (TensorProduct.congr (mapIsoFiber d eX hX) (mapIsoFiber d eY hY)) := by
  apply (basisColorFiber (Sum.elim cX cY)).ext'
  intro i
  simp
  nth_rewrite 2 [tensorator]
  simp
  rw [Basis.tensorProduct_apply, TensorProduct.congr_tmul, mapIsoFiber_basis]
  rw [tensorator]
  simp
  rw [Basis.tensorProduct_apply, mapIsoFiber_basis, mapIsoFiber_basis]
  congr
  sorry
  sorry

lemma tensorator_lorentzAction  (Λ : LorentzGroup d)  :
    (tensorator).toLinearMap ∘ₗ lorentzActionFiber Λ
    = (TensorProduct.map (lorentzActionFiber Λ) (lorentzActionFiber Λ) ) ∘ₗ
    ((@tensorator d X Y _ _ _ _ cX cY).toLinearMap) := by
  apply (basisColorFiber (Sum.elim cX cY)).ext
  intro i
  nth_rewrite 2 [tensorator]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Basis.equiv_apply]
  rw [basisProd, Basis.tensorProduct_apply, TensorProduct.map_tmul, lorentzActionFiber_basis,
    lorentzActionFiber_basis, lorentzActionFiber_basis, map_sum, tmul_sum]
  simp only [sum_tmul]
  rw [← Equiv.sum_comp (indexValueSumEquiv).symm, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => (Finset.sum_congr rfl (fun k _ => ?_)))
  rw [tmul_smul, smul_tmul, tmul_smul, smul_smul, map_smul]
  congr 1
  · rw [toTensorRepMat_of_indexValueSumEquiv, Equiv.apply_symm_apply, mul_comm]
  · simp [tensorator]

lemma tensorator_lorentzAction_apply  (Λ : LorentzGroup d) (T : ColorFiber d (Sum.elim cX cY)) :
    tensorator (lorentzActionFiber Λ T) =
    TensorProduct.map (lorentzActionFiber Λ) (lorentzActionFiber Λ) (tensorator T) := by
  erw [← LinearMap.comp_apply, tensorator_lorentzAction]
  rfl

/-!

## Decomposing tensors based on embeddings

-/

def decompEmbedSet (f : Y ↪ X) :
    X ≃ {x // x ∈ (Finset.image f Finset.univ)ᶜ} ⊕ Y :=
  (Equiv.Set.sumCompl (Set.range ⇑f)).symm.trans <|
  (Equiv.sumComm _ _).trans <|
  Equiv.sumCongr ((Equiv.subtypeEquivRight (by simp))) <|
  (Function.Embedding.toEquivRange f).symm

def decompEmbedColorLeft (f : Y ↪ X) : {x // x ∈ (Finset.image f Finset.univ)ᶜ} → Colors :=
  (cX ∘ (decompEmbedSet f).symm) ∘ Sum.inl

def decompEmbedColorRight (f : Y ↪ X) : Y → Colors :=
  (cX ∘ (decompEmbedSet f).symm) ∘ Sum.inr

/-- Decomposes a tensor into a tensor product based on an embedding. -/
def decompEmbed (f : Y ↪ X) :
    ColorFiber d cX ≃ₗ[ℝ] ColorFiber d (decompEmbedColorLeft cX f) ⊗[ℝ] ColorFiber d (cX ∘ f) :=
  (@mapIsoFiber _ _ d (decompEmbedSet f) cX (Sum.elim (decompEmbedColorLeft cX f)
    (decompEmbedColorRight cX f)) (by
      simpa [decompEmbedColorLeft, decompEmbedColorRight] using (Equiv.comp_symm_eq _ _ _).mp rfl)).trans
  tensorator

lemma decompEmbed_lorentzAction_apply {f : Y ↪ X} (Λ : LorentzGroup d) (T : ColorFiber d cX) :
    decompEmbed cX f (lorentzActionFiber Λ T) =
    TensorProduct.map (lorentzActionFiber Λ) (lorentzActionFiber Λ) (decompEmbed cX f T) := by
  rw [decompEmbed]
  simp
  rw [lorentzActionFiber_mapIsoFiber]
  exact tensorator_lorentzAction_apply (decompEmbedColorLeft cX f) (decompEmbedColorRight cX f) Λ
      ((mapIsoFiber d (decompEmbedSet f) (decompEmbed.proof_2 cX f)) T)

def decompEmbedProd (f : X' ↪ X) (g : Y' ↪ Y) :
    ColorFiber d cX ⊗[ℝ] ColorFiber d cY ≃ₗ[ℝ]
    ColorFiber d (Sum.elim (decompEmbedColorLeft cX f) (decompEmbedColorLeft cY g))
    ⊗[ℝ] (ColorFiber d (cX ∘ f) ⊗[ℝ] ColorFiber d (cY ∘ g)) :=
  (TensorProduct.congr (decompEmbed cX f) (decompEmbed cY g)).trans <|
  (TensorProduct.assoc ℝ _ _ _).trans <|
  (TensorProduct.congr (LinearEquiv.refl ℝ _)
    ((TensorProduct.assoc ℝ _ _ _).symm.trans <|
     (TensorProduct.congr (TensorProduct.comm _ _ _) (LinearEquiv.refl ℝ _)).trans <|
     (TensorProduct.assoc ℝ _ _ _))).trans <|
  (TensorProduct.assoc ℝ _ _ _).symm.trans <|
  (TensorProduct.congr tensorator.symm (LinearEquiv.refl ℝ _))



/-- The contraction of all indices of two tensors with dual index-colors.
  This is a bilinear map to ℝ. -/
@[simps!]
def contrAll {f1 : X → Colors} {f2 : Y → Colors} (e : X ≃ Y) (hc : f1 = τ ∘ f2 ∘ e) :
    ColorFiber d f1 →ₗ[ℝ] ColorFiber d f2 →ₗ[ℝ] ℝ where
  toFun T := {
    toFun := fun S => ∑ i, T i * S (indexValueDualIso d e hc i),
    map_add' := fun S F => by
      trans  ∑ i, (T i * S (indexValueDualIso d e hc i) + T i * F (indexValueDualIso d e hc i))
      exact Finset.sum_congr rfl (fun i _ => mul_add _ _ _ )
      exact Finset.sum_add_distrib,
    map_smul' := fun r S => by
      trans ∑ i , r * (T i * S (indexValueDualIso d e hc i))
      refine Finset.sum_congr rfl (fun x _ => ?_)
      ring_nf
      rw [mul_assoc]
      rfl
      rw [← Finset.mul_sum]
      rfl}
  map_add' := fun T S => by
    ext F
    trans ∑ i , (T i * F (indexValueDualIso d e hc i) + S i * F (indexValueDualIso d e hc i))
    exact Finset.sum_congr rfl (fun x _ => add_mul _ _ _)
    exact Finset.sum_add_distrib
  map_smul' := fun r T => by
    ext S
    trans ∑ i , r * (T i * S (indexValueDualIso d e hc i))
    refine Finset.sum_congr rfl (fun x _ => mul_assoc _ _ _)
    rw [← Finset.mul_sum]
    rfl

lemma contrAll_symm {f1 : X → Colors} {f2 : Y → Colors} (e : X ≃ Y)
    (h : f1 = τ ∘ f2 ∘ e) (T : ColorFiber d f1) (S : ColorFiber d f2) :
    contrAll e h T S = contrAll e.symm (indexValueDualIso_cond_symm h) S T := by
  rw [contrAll_apply_apply, contrAll_apply_apply, ← Equiv.sum_comp (indexValueDualIso d e h)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm, ← Equiv.trans_apply]
  simp

lemma contrAll_mapIsoFiber_right {f1 : X → Colors} {f2 : Y → Colors}
    {g2 : Y' → Colors} (e : X ≃ Y) (eY : Y ≃ Y')
    (h : f1 = τ ∘ f2 ∘ e) (hY : f2 = g2 ∘ eY) (T : ColorFiber d f1) (S : ColorFiber d f2) :
    contrAll e h T S = contrAll (e.trans eY) (indexValueDualIso_cond_trans_indexValueIso h hY)
      T (mapIsoFiber d eY hY S) := by
  rw [contrAll_apply_apply, contrAll_apply_apply]
  refine Finset.sum_congr rfl (fun i _ => Mathlib.Tactic.Ring.mul_congr rfl ?_ rfl)
  rw [mapIsoFiber_apply, ← Equiv.trans_apply]
  simp only [indexValueDualIso_trans_indexValueIso]
  congr
  ext1 x
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

lemma contrAll_mapIsoFiber_left {f1 : X → Colors} {f2 : Y → Colors}
    {g1 : X' → Colors} (e : X ≃ Y) (eX : X ≃ X')
    (h : f1 = τ ∘ f2 ∘ e) (hX : f1 = g1 ∘ eX) (T : ColorFiber d f1) (S : ColorFiber d f2) :
    contrAll e h T S = contrAll (eX.symm.trans e)
    (indexValueIso_trans_indexValueDualIso_cond ((Equiv.eq_comp_symm eX g1 f1).mpr hX.symm) h)
    (mapIsoFiber d eX hX T) S := by
  rw [contrAll_symm, contrAll_mapIsoFiber_right _ eX _ hX, contrAll_symm]
  rfl

lemma contrAll_lorentzAction {f1 : X → Colors} {f2 : Y → Colors} (e : X ≃ Y)
    (hc : f1 = τ ∘ f2 ∘ e) (T : ColorFiber d f1) (S : ColorFiber d f2) (Λ : LorentzGroup d) :
    contrAll e hc (lorentzActionFiber Λ T) (lorentzActionFiber Λ S) = contrAll e hc T S := by
  change ∑ i, (∑ j, toTensorRepMat Λ i j * T j) *
    (∑ k, toTensorRepMat Λ (indexValueDualIso d e hc i) k * S k) = _
  trans ∑ i, ∑ j, ∑ k, (toTensorRepMat Λ (indexValueDualIso d e hc i) k * toTensorRepMat Λ i j)
      * T j * S k
  · apply Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl (fun j _ => ?_)
    apply Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [Finset.sum_comm]
  trans ∑ j, ∑ k, ∑ i, (toTensorRepMat Λ (indexValueDualIso d e hc i) k
    * toTensorRepMat Λ i j) * T j * S k
  · apply Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
  trans ∑ j, ∑ k, (toTensorRepMat 1 (indexValueDualIso d e.symm (indexValueDualIso_cond_symm hc) k) j) * T j * S k
  · apply Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    erw [toTensorRepMat_indexValueDualIso_sum]
  rw [Finset.sum_comm]
  trans ∑ k, T (indexValueDualIso d e.symm (indexValueDualIso_cond_symm hc) k) * S k
  · apply Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_mul, ← toTensorRepMat_one_coord_sum' T]
  rw [← Equiv.sum_comp (indexValueDualIso d e hc), ← indexValueDualIso_symm e hc]
  simp only [Equiv.symm_apply_apply, contrAll_apply_apply]


end RealLorentzTensor
end
