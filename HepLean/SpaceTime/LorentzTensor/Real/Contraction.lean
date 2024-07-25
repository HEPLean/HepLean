/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Real.Basic
import HepLean.SpaceTime.LorentzTensor.Real.TensorProducts
/-!

# Multiplication of Real Lorentz Tensors along an index

We define the multiplication of two singularly marked Lorentz tensors along the
marked index. This is equivalent to contracting two Lorentz tensors.

We prove various results about this multiplication.

-/
/-! TODO: Set up a good notation for the multiplication. -/

namespace RealLorentzTensor
open TensorProduct
open Set LinearMap Submodule

variable {d : ℕ} {X Y Y' X'  : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype X'] [DecidableEq X']
  (cX : X → Color) (cY : Y → Color)



/-- The contraction of all indices of two tensors with dual index-colors.
  This is a bilinear map to ℝ. -/
@[simps!]
def contrAll {f1 : X → Color} {f2 : Y → Color} (e : X ≃ Y) (hc : f1 = τ ∘ f2 ∘ e) :
    RealLorentzTensor d f1 →ₗ[ℝ] RealLorentzTensor d f2 →ₗ[ℝ] ℝ where
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

lemma contrAll_symm {f1 : X → Color} {f2 : Y → Color} (e : X ≃ Y)
    (h : f1 = τ ∘ f2 ∘ e) (T : RealLorentzTensor d f1) (S : RealLorentzTensor d f2) :
    contrAll e h T S = contrAll e.symm (indexValueDualIso_cond_symm h) S T := by
  rw [contrAll_apply_apply, contrAll_apply_apply, ← Equiv.sum_comp (indexValueDualIso d e h)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm, ← Equiv.trans_apply]
  simp

lemma contrAll_mapIsoFiber_right {f1 : X → Color} {f2 : Y → Color}
    {g2 : Y' → Color} (e : X ≃ Y) (eY : Y ≃ Y')
    (h : f1 = τ ∘ f2 ∘ e) (hY : f2 = g2 ∘ eY) (T : RealLorentzTensor d f1) (S : RealLorentzTensor d f2) :
    contrAll e h T S = contrAll (e.trans eY) (indexValueDualIso_cond_trans_indexValueIso h hY)
      T (mapIso eY hY S) := by
  rw [contrAll_apply_apply, contrAll_apply_apply]
  refine Finset.sum_congr rfl (fun i _ => Mathlib.Tactic.Ring.mul_congr rfl ?_ rfl)
  rw [mapIso_apply, ← Equiv.trans_apply]
  simp only [indexValueDualIso_trans_indexValueIso]
  congr
  ext1 x
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]

lemma contrAll_mapIsoFiber_left {f1 : X → Color} {f2 : Y → Color}
    {g1 : X' → Color} (e : X ≃ Y) (eX : X ≃ X')
    (h : f1 = τ ∘ f2 ∘ e) (hX : f1 = g1 ∘ eX) (T : RealLorentzTensor d f1) (S : RealLorentzTensor d f2) :
    contrAll e h T S = contrAll (eX.symm.trans e)
    (indexValueIso_trans_indexValueDualIso_cond ((Equiv.eq_comp_symm eX g1 f1).mpr hX.symm) h)
    (mapIso eX hX T) S := by
  rw [contrAll_symm, contrAll_mapIsoFiber_right _ eX _ hX, contrAll_symm]
  rfl

lemma contrAll_lorentzAction {f1 : X → Color} {f2 : Y → Color} (e : X ≃ Y)
    (hc : f1 = τ ∘ f2 ∘ e) (T : RealLorentzTensor d f1) (S : RealLorentzTensor d f2) (Λ : LorentzGroup d) :
    contrAll e hc (Λ • T) (Λ • S) = contrAll e hc T S := by
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
