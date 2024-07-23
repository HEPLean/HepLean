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

variable {d : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  (cX : X → Colors) (cY : Y → Colors)

def basisColorFiber : Basis (IndexValue d cX) ℝ (ColorFiber d cX) := Pi.basisFun _ _

def colorFiberElim {cX : X → Colors} {cY : Y → Colors} : ColorFiber d (Sum.elim cX cY) ≃ₗ[ℝ] ColorFiber d cX ⊗[ℝ] ColorFiber d cY :=
  (basisColorFiber (Sum.elim cX cY)).equiv
  (Basis.tensorProduct (basisColorFiber cX) (basisColorFiber cY)) indexValueSumEquiv

def splitOnEmbeddingSet (f : Y ↪ X) :
    X ≃ {x // x ∈ (Finset.image f Finset.univ)ᶜ} ⊕ Y :=
  (Equiv.Set.sumCompl (Set.range ⇑f)).symm.trans <|
  (Equiv.sumComm _ _).trans <|
  Equiv.sumCongr ((Equiv.subtypeEquivRight (by simp))) <|
  (Function.Embedding.toEquivRange f).symm

def embedLeftColor (f : Y ↪ X) : {x // x ∈ (Finset.image f Finset.univ)ᶜ}  → Colors :=
  (cX ∘ (splitOnEmbeddingSet f).symm) ∘ Sum.inl

def embedRightColor (f : Y ↪ X) : Y → Colors :=
  (cX ∘ (splitOnEmbeddingSet f).symm) ∘ Sum.inr

def embedTensorProd (f : Y ↪ X) : ColorFiber d cX ≃ₗ[ℝ] ColorFiber d (embedLeftColor cX f) ⊗[ℝ]
    ColorFiber d (embedRightColor cX f) :=
  (@mapIsoFiber _ _ d (splitOnEmbeddingSet f) cX (Sum.elim (embedLeftColor cX f)
    (embedRightColor cX f)) (by
      simpa [embedLeftColor, embedRightColor] using (Equiv.comp_symm_eq _ _ _).mp rfl)).trans
  colorFiberElim

/-- The contraction of all indices of two tensors with dual index-colors.
  This is a bilinear map to ℝ. -/
@[simps!]
def contrAll {f1 f2 : X → Colors} (hc : f1 = τ ∘ f2) :
    ColorFiber d f1 →ₗ[ℝ] ColorFiber d f2 →ₗ[ℝ] ℝ where
  toFun T := {
    toFun := fun S => ∑ i, T i * S (indexValueDualIso d hc i),
    map_add' := fun S F => by
      trans  ∑ i, (T i * S (indexValueDualIso d hc i) + T i * F (indexValueDualIso d hc i))
      exact Finset.sum_congr rfl (fun i _ => mul_add _ _ _ )
      exact Finset.sum_add_distrib,
    map_smul' := fun r S => by
      trans ∑ i , r * (T i * S (indexValueDualIso d hc i))
      refine Finset.sum_congr rfl (fun x _ => ?_)
      ring_nf
      rw [mul_assoc]
      rfl
      rw [← Finset.mul_sum]
      rfl}
  map_add' := fun T S => by
    ext F
    trans ∑ i , (T i * F (indexValueDualIso d hc i) + S i * F (indexValueDualIso d hc i))
    exact Finset.sum_congr rfl (fun x _ => add_mul _ _ _)
    exact Finset.sum_add_distrib
  map_smul' := fun r T => by
    ext S
    trans ∑ i , r * (T i * S (indexValueDualIso d hc i))
    refine Finset.sum_congr rfl (fun x _ => mul_assoc _ _ _)
    rw [← Finset.mul_sum]
    rfl

lemma contrAll_mapIsoFiber {f1 f2 : X → Colors} (hc : f1 = τ ∘ f2)
      (e : X ≃ Y) {g1 g2 : Y → Colors} (h1 : f1 = g1 ∘ e) (h2 : f2 = g2 ∘ e) (T : ColorFiber d f1)
      (S : ColorFiber d f2) : contrAll hc T S = contrAll (by
        rw [h1, h2, ← Function.comp.assoc, ← Equiv.comp_symm_eq] at hc
        simpa [Function.comp.assoc] using hc) (mapIsoFiber d e h1 T) (mapIsoFiber d e h2 S) := by
  rw [contrAll_apply_apply, contrAll_apply_apply]
  rw [← Equiv.sum_comp (indexValueIso d e h1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mapIsoFiber_apply, Equiv.symm_apply_apply]
  rw [mapIsoFiber_apply]
  congr 2
  rw [← indexValueDualIso_symm]





lemma contrAll_symm {f1 f2 : X → Colors} (hc : f1 = τ ∘ f2) (T : ColorFiber d f1)
    (S : ColorFiber d f2) : contrAll hc T S = contrAll (color_comp_τ_symm hc) S T := by
  rw [contrAll_apply_apply, contrAll_apply_apply, ← Equiv.sum_comp (indexValueDualIso d hc)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  congr
  rw [← indexValueDualIso_symm]
  exact (Equiv.apply_eq_iff_eq_symm_apply (indexValueDualIso d hc)).mp rfl

lemma contrAll_lorentzAction {f1 f2 : X → Colors} (hc : f1 = τ ∘ f2) (T : ColorFiber d f1)
    (S : ColorFiber d f2) (Λ : LorentzGroup d) :
    contrAll hc (lorentzActionFiber Λ T) (lorentzActionFiber Λ S) = contrAll hc T S := by
  change ∑ i, (∑ j, toTensorRepMat Λ i j * T j) *
    (∑ k, toTensorRepMat Λ (indexValueDualIso d hc i) k * S k) = _
  trans ∑ i, ∑ j, ∑ k, (toTensorRepMat Λ (indexValueDualIso d hc i) k * toTensorRepMat Λ i j)
      * T j * S k
  · apply Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl (fun j _ => ?_)
    apply Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [Finset.sum_comm]
  trans ∑ j, ∑ k, ∑ i, (toTensorRepMat Λ (indexValueDualIso d hc i) k
    * toTensorRepMat Λ i j) * T j * S k
  · apply Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
  trans ∑ j, ∑ k, (toTensorRepMat 1 (indexValueDualIso d (color_comp_τ_symm hc) k) j) * T j * S k
  · apply Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    erw [toTensorRepMat_indexValueDualIso]
  rw [Finset.sum_comm]
  trans ∑ k, T (indexValueDualIso d (color_comp_τ_symm hc) k) * S k
  · apply Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Finset.sum_mul, ← toTensorRepMat_one_coord_sum' T]
  rw [← Equiv.sum_comp (indexValueDualIso d hc), ← indexValueDualIso_symm d hc]
  simp only [Equiv.symm_apply_apply, contrAll_apply_apply]


end RealLorentzTensor
end
