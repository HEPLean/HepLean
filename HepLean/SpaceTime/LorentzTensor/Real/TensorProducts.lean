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
  (cX : X → Color) (cY : Y → Color)


/-!

## The tensorator and properties thereof

-/

/-- An equivalence between `ColorFiber d (Sum.elim cX cY)` and
  `ColorFiber d cX ⊗[ℝ] ColorFiber d cY`. This is related to the `tensorator` of
  the monoidal functor defined by `ColorFiber`, hence the terminology.  -/
def tensorator {cX : X → Color} {cY : Y → Color} :
    RealLorentzTensor d (Sum.elim cX cY) ≃ₗ[ℝ] RealLorentzTensor d cX ⊗[ℝ] RealLorentzTensor d cY :=
  (basis (Sum.elim cX cY)).equiv (basisProd cX cY) indexValueTensorator

lemma tensorator_symm_apply {cX : X → Color} {cY : Y → Color}
    (X : RealLorentzTensor d cX ⊗[ℝ] RealLorentzTensor d cY) (i : IndexValue d (Sum.elim cX cY)) :
    (tensorator.symm X) i = (basisProd cX cY).repr X (indexValueTensorator i) := by
  rfl



/-- The naturality condition for the `tensorator`. -/
lemma tensorator_mapIso {cX : X → Color} {cY : Y → Color} {cX' : X' → Color}
    {cY' : Y' → Color} (eX : X ≃ X') (eY : Y ≃ Y') (hX : cX = cX' ∘ eX) (hY : cY = cY' ∘ eY) :
    (@mapIso _ _ d (Equiv.sumCongr eX eY) _ _ (tensorator_mapIso_cond hX hY)).trans tensorator  =
    tensorator.trans (TensorProduct.congr (mapIso eX hX) (mapIso eY hY)) := by
  apply (basis (Sum.elim cX cY)).ext'
  intro i
  simp
  nth_rewrite 2 [tensorator]
  simp
  rw [Basis.tensorProduct_apply, TensorProduct.congr_tmul, mapIsoFiber_basis]
  rw [tensorator]
  simp only [basisProd, Basis.equiv_apply]
  rw [Basis.tensorProduct_apply, mapIsoFiber_basis, mapIsoFiber_basis]
  congr
  rw [← Equiv.trans_apply, indexValueTensorator_indexValueMapIso]
  rfl
  exact hY
  rw [← Equiv.trans_apply, indexValueTensorator_indexValueMapIso]
  rfl
  exact hX

lemma tensorator_lorentzAction  (Λ : LorentzGroup d)  :
    (tensorator).toLinearMap ∘ₗ lorentzAction Λ
    = (TensorProduct.map (lorentzAction Λ) (lorentzAction Λ) ) ∘ₗ
    ((@tensorator d X Y _ _ _ _ cX cY).toLinearMap) := by
  apply (basis (Sum.elim cX cY)).ext
  intro i
  nth_rewrite 2 [tensorator]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Basis.equiv_apply]
  rw [basisProd, Basis.tensorProduct_apply, TensorProduct.map_tmul, lorentzAction_basis,
    lorentzAction_basis, lorentzAction_basis, map_sum, tmul_sum]
  simp only [sum_tmul]
  rw [← Equiv.sum_comp (indexValueTensorator).symm, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => (Finset.sum_congr rfl (fun k _ => ?_)))
  rw [tmul_smul, smul_tmul, tmul_smul, smul_smul, map_smul]
  congr 1
  · rw [toTensorRepMat_of_indexValueSumEquiv, Equiv.apply_symm_apply, mul_comm]
  · simp [tensorator]

lemma tensorator_lorentzAction_apply  (Λ : LorentzGroup d) (T : RealLorentzTensor d (Sum.elim cX cY)) :
    tensorator (Λ • T) =
    TensorProduct.map (lorentzAction Λ) (lorentzAction Λ) (tensorator T) := by
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

def decompEmbedColorLeft (f : Y ↪ X) : {x // x ∈ (Finset.image f Finset.univ)ᶜ} → Color :=
  (cX ∘ (decompEmbedSet f).symm) ∘ Sum.inl

def decompEmbedColorRight (f : Y ↪ X) : Y → Color :=
  (cX ∘ (decompEmbedSet f).symm) ∘ Sum.inr

/-- Decomposes a tensor into a tensor product based on an embedding. -/
def decompEmbed (f : Y ↪ X) :
    RealLorentzTensor d cX ≃ₗ[ℝ] RealLorentzTensor d (decompEmbedColorLeft cX f) ⊗[ℝ] RealLorentzTensor d (cX ∘ f) :=
  (@mapIso _ _ d (decompEmbedSet f) cX (Sum.elim (decompEmbedColorLeft cX f)
    (decompEmbedColorRight cX f)) (by
      simpa [decompEmbedColorLeft, decompEmbedColorRight] using (Equiv.comp_symm_eq _ _ _).mp rfl)).trans
  tensorator

lemma decompEmbed_lorentzAction_apply {f : Y ↪ X} (Λ : LorentzGroup d) (T : RealLorentzTensor d cX) :
    decompEmbed cX f (Λ • T) =
    TensorProduct.map (lorentzAction Λ) (lorentzAction Λ) (decompEmbed cX f T) := by
  rw [decompEmbed]
  simp
  rw [lorentzAction_mapIso]
  exact tensorator_lorentzAction_apply (decompEmbedColorLeft cX f) (decompEmbedColorRight cX f) Λ
      ((mapIso (decompEmbedSet f) (decompEmbed.proof_2 cX f)) T)

def decompEmbedProd (f : X' ↪ X) (g : Y' ↪ Y) :
    RealLorentzTensor d cX ⊗[ℝ] RealLorentzTensor d cY ≃ₗ[ℝ]
    RealLorentzTensor d (Sum.elim (decompEmbedColorLeft cX f) (decompEmbedColorLeft cY g))
    ⊗[ℝ] (RealLorentzTensor d (cX ∘ f) ⊗[ℝ] RealLorentzTensor d (cY ∘ g)) :=
  (TensorProduct.congr (decompEmbed cX f) (decompEmbed cY g)).trans <|
  (TensorProduct.assoc ℝ _ _ _).trans <|
  (TensorProduct.congr (LinearEquiv.refl ℝ _)
    ((TensorProduct.assoc ℝ _ _ _).symm.trans <|
     (TensorProduct.congr (TensorProduct.comm _ _ _) (LinearEquiv.refl ℝ _)).trans <|
     (TensorProduct.assoc ℝ _ _ _))).trans <|
  (TensorProduct.assoc ℝ _ _ _).symm.trans <|
  (TensorProduct.congr tensorator.symm (LinearEquiv.refl ℝ _))



end RealLorentzTensor
end
