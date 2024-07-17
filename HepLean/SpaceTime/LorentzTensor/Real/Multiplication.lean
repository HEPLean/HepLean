/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Real.Basic
import HepLean.SpaceTime.LorentzTensor.Real.LorentzAction
/-!

# Multiplication of Real Lorentz Tensors along an index

We define the multiplication of two singularly marked Lorentz tensors along the
marked index. This is equivalent to contracting two Lorentz tensors.

We prove various results about this multiplication.

-/
/-! TODO: Add unit to the multiplication. -/
/-! TODO: Generalize to contracting any marked index of a marked tensor. -/
/-! TODO: Set up a good notation for the multiplication. -/

namespace RealLorentzTensor

variable {d : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  (T : RealLorentzTensor d X) (c : X → Colors) (Λ Λ' : LorentzGroup d) {μ : Colors}

open Marked

/-- The contraction of the marked indices of two tensors each with one marked index, which
is dual to the others. The contraction is done via
`φ^μ ψ_μ = φ^0 ψ_0 + φ^1 ψ_1 + ...`. -/
@[simps!]
def mul {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    RealLorentzTensor d (X ⊕ Y) where
  color := Sum.elim T.unmarkedColor S.unmarkedColor
  coord := fun i => ∑ x,
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1, oneMarkedIndexValue x)) *
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2,
      oneMarkedIndexValue $ colorsIndexDualCast h x))

/-- Multiplication is well behaved with regard to swapping tensors. -/
lemma mul_symm {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    mapIso d (Equiv.sumComm X Y) (mul T S h) = mul S T (color_eq_dual_symm h) := by
  refine ext ?_ ?_
  · funext a
    cases a with
    | inl _ => rfl
    | inr _ => rfl
  · funext i
    rw [mapIso_apply_coord, mul_coord, mul_coord]
    erw [← Equiv.sum_comp (colorsIndexDualCast h).symm]
    refine Fintype.sum_congr _ _ (fun x => ?_)
    rw [mul_comm]
    congr
    · exact Equiv.apply_symm_apply (colorsIndexDualCast h) x
    · exact colorsIndexDualCast_symm h

lemma mul_mapIso {X Y Z : Type} (T : Marked d X 1) (S : Marked d Y 1) (f : X ≃ W)
    (g : Y ≃ Z) (h : T.markedColor 0 = τ (S.markedColor 0)) :
    mapIso d (Equiv.sumCongr f g) (mul T S h) = mul (mapIso d (Equiv.sumCongr f (Equiv.refl _)) T)
    (mapIso d (Equiv.sumCongr g (Equiv.refl _)) S) h := by
  refine ext ?_ ?_
  · funext a
    cases a with
    | inl _ => rfl
    | inr _ => rfl
  · funext i
    rw [mapIso_apply_coord, mul_coord, mul_coord]
    refine Fintype.sum_congr _ _ (fun x => ?_)
    rw [mapIso_apply_coord, mapIso_apply_coord]
    refine Mathlib.Tactic.Ring.mul_congr ?_ ?_ rfl
    · apply congrArg
      ext1 r
      cases r with
      | inl val => rfl
      | inr val_1 => rfl
    · apply congrArg
      ext1 r
      cases r with
      | inl val => rfl
      | inr val_1 => rfl

/-!

## Lorentz action and multiplication.

-/

/-- The marked Lorentz Action leaves multiplication invariant. -/
lemma mul_markedLorentzAction (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 1)) :
    mul (Λ •ₘ T) (Λ •ₘ S) h = mul T S h := by
  refine ext rfl ?_
  funext i
  change ∑ x, (∑ j, toTensorRepMat Λ (oneMarkedIndexValue x) j *
      T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1, j))) *
      (∑ k, toTensorRepMat Λ (oneMarkedIndexValue $ colorsIndexDualCast h x) k *
      S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, k))) = _
  trans ∑ x, ∑ j, ∑ k, (toTensorRepMat Λ (oneMarkedIndexValue $ colorsIndexDualCast h x) k
    * toTensorRepMat Λ (oneMarkedIndexValue x) j) *
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1, j))
    * S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, k))
  apply Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul_sum ]
  apply Finset.sum_congr rfl (fun j _ => ?_)
  apply Finset.sum_congr rfl (fun k _ => ?_)
  ring
  rw [Finset.sum_comm]
  trans ∑ j, ∑ k, ∑ x, (toTensorRepMat Λ (oneMarkedIndexValue $ colorsIndexDualCast h x) k
    * toTensorRepMat Λ (oneMarkedIndexValue x) j) *
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1, j))
    * S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, k))
  apply Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  trans ∑ j, ∑ k, (toTensorRepMat 1
    (oneMarkedIndexValue $ (colorsIndexDualCast h).symm $ oneMarkedIndexValue.symm k) j) *
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1, j))
    * S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, k))
  apply Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  erw [toTensorRepMap_sum_dual]
  rfl
  rw [Finset.sum_comm]
  trans ∑ k,
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1,
    (oneMarkedIndexValue $ (colorsIndexDualCast h).symm $ oneMarkedIndexValue.symm k)))*
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, k))
  apply Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_mul, ← toTensorRepMat_one_coord_sum T]
  rw [← Equiv.sum_comp (oneMarkedIndexValue)]
  erw [← Equiv.sum_comp (colorsIndexDualCast h)]
  simp
  rfl

/-- The unmarked Lorentz Action commutes with multiplication. -/
lemma mul_unmarkedLorentzAction (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 1)) :
    mul (Λ •ᵤₘ T) (Λ •ᵤₘ S) h = Λ • mul T S h := by
  refine ext rfl ?_
  funext i
  change ∑ x, (∑ j, toTensorRepMat Λ (indexValueSumEquiv i).1 j *
      T.coord (splitIndexValue.symm (j, oneMarkedIndexValue x)))*
      ∑ k, toTensorRepMat Λ (indexValueSumEquiv i).2 k *
      S.coord (splitIndexValue.symm (k, oneMarkedIndexValue $ colorsIndexDualCast h x)) = _
  trans ∑ x, ∑ j, ∑ k, (toTensorRepMat Λ (indexValueSumEquiv i).1 j *
      T.coord (splitIndexValue.symm (j, oneMarkedIndexValue x)))*
       toTensorRepMat Λ (indexValueSumEquiv i).2 k *
      S.coord (splitIndexValue.symm (k, oneMarkedIndexValue $ colorsIndexDualCast h x))
  apply Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul_sum ]
  apply Finset.sum_congr rfl (fun j _ => ?_)
  apply Finset.sum_congr rfl (fun k _ => ?_)
  ring
  rw [Finset.sum_comm]
  trans ∑ j, ∑ k, ∑ x, (toTensorRepMat Λ (indexValueSumEquiv i).1 j *
      T.coord (splitIndexValue.symm (j, oneMarkedIndexValue x)))*
       toTensorRepMat Λ (indexValueSumEquiv i).2 k *
      S.coord (splitIndexValue.symm (k, oneMarkedIndexValue $ colorsIndexDualCast h x))
  apply Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_comm]
  trans ∑ j, ∑ k,
    ((toTensorRepMat Λ (indexValueSumEquiv i).1 j) * toTensorRepMat Λ (indexValueSumEquiv i).2 k)
    * ∑ x, (T.coord (splitIndexValue.symm (j, oneMarkedIndexValue x)))
    * S.coord (splitIndexValue.symm (k, oneMarkedIndexValue $ colorsIndexDualCast h x))
  apply Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun x _ => ?_)
  ring
  trans ∑ j, ∑ k, toTensorRepMat Λ i (indexValueSumEquiv.symm (j, k)) *
    ∑ x, (T.coord (splitIndexValue.symm (j, oneMarkedIndexValue x)))
      * S.coord (splitIndexValue.symm (k, oneMarkedIndexValue $ colorsIndexDualCast h x))
  apply Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [toTensorRepMat_of_indexValueSumEquiv']
  congr
  simp only [IndexValue, Finset.mem_univ, Prod.mk.eta, Equiv.symm_apply_apply, mul_color]
  trans ∑ p, toTensorRepMat Λ i p *
    ∑ x, (T.coord (splitIndexValue.symm ((indexValueSumEquiv p).1, oneMarkedIndexValue x)))
    * S.coord (splitIndexValue.symm ((indexValueSumEquiv p).2,
      oneMarkedIndexValue $ colorsIndexDualCast h x))
  erw [← Equiv.sum_comp indexValueSumEquiv.symm]
  rw [Fintype.sum_prod_type]
  rfl
  rfl

/-- The Lorentz action commutes with multiplication. -/
lemma mul_lorentzAction (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 1)) :
    mul (Λ • T) (Λ • S) h = Λ • mul T S h := by
  simp only [← marked_unmarked_action_eq_action]
  rw [mul_markedLorentzAction, mul_unmarkedLorentzAction]

end RealLorentzTensor
