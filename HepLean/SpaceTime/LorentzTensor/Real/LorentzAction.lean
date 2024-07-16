/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Real.Basic
import HepLean.SpaceTime.LorentzGroup.Basic
/-!

# Lorentz group action on Real Lorentz Tensors

We define the action of the Lorentz group on Real Lorentz Tensors.

The Lorentz action is currently only defined for finite and decidable types `X`.

-/

namespace RealLorentzTensor

variable {d : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
variable (T : RealLorentzTensor d X) (c : X → Colors)
variable (Λ Λ' : LorentzGroup d)
open LorentzGroup
open BigOperators


variable {μ : Colors}

/-- Monoid homomorphism from the Lorentz group to matrices indexed by `ColorsIndex d μ` for a
  color `μ`.

  This can be thought of as the representation of the Lorentz group for that color index. -/
def colorMatrix (μ : Colors) : LorentzGroup d →* Matrix (ColorsIndex d μ) (ColorsIndex d μ) ℝ where
  toFun Λ := match μ with
    | .up => fun i j => Λ.1 i j
    | .down => fun i j => (LorentzGroup.transpose Λ⁻¹).1 i j
  map_one' := by
    match μ with
    | .up =>
        simp only [lorentzGroupIsGroup_one_coe]
        ext i j
        simp only [OfNat.ofNat, One.one, ColorsIndex]
        congr
    | .down =>
        simp only [transpose, inv_one, lorentzGroupIsGroup_one_coe, Matrix.transpose_one]
        ext i j
        simp only [OfNat.ofNat, One.one, ColorsIndex]
        congr
  map_mul' Λ Λ' := by
    match μ with
    | .up =>
        ext i j
        simp only [lorentzGroupIsGroup_mul_coe]
    | .down =>
        ext i j
        simp only [transpose, mul_inv_rev, lorentzGroupIsGroup_inv, lorentzGroupIsGroup_mul_coe,
          Matrix.transpose_mul, Matrix.transpose_apply]
        rfl

lemma colorMatrix_cast {μ ν : Colors} (h : μ = ν) (Λ : LorentzGroup d) :
    colorMatrix μ Λ =
    Matrix.reindex (castColorsIndex h).symm (castColorsIndex h).symm (colorMatrix ν Λ) := by
  subst h
  rfl

/-- A real number occuring in the action of the Lorentz group on Lorentz tensors. -/
@[simps!]
def toTensorRepMat {c : X → Colors} :
    LorentzGroup d →* Matrix (IndexValue d c) (IndexValue d c) ℝ where
  toFun Λ := fun i j => ∏ x, colorMatrix (c x) Λ (i x) (j x)
  map_one' := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [map_one, Matrix.one_apply_eq, Finset.prod_const_one]
    · obtain ⟨x, hijx⟩ := Function.ne_iff.mp hij
      simp only [map_one]
      rw [@Finset.prod_eq_zero _ _ _ _ _ x]
      exact Eq.symm (Matrix.one_apply_ne' fun a => hij (id (Eq.symm a)))
      exact Finset.mem_univ x
      exact Matrix.one_apply_ne' (id (Ne.symm hijx))
  map_mul' Λ Λ' := by
    ext i j
    rw [Matrix.mul_apply]
    trans ∑ (k : IndexValue d c), ∏ x,
        (colorMatrix (c x) Λ (i x) (k x)) * (colorMatrix (c x) Λ' (k x) (j x))
    have h1 : ∑ (k : IndexValue d c), ∏ x,
        (colorMatrix (c x) Λ (i x) (k x)) * (colorMatrix (c x) Λ' (k x) (j x)) =
        ∏ x, ∑ y, (colorMatrix (c x) Λ (i x) y) * (colorMatrix (c x) Λ' y (j x)) := by
      rw [Finset.prod_sum]
      simp only [Finset.prod_attach_univ, Finset.sum_univ_pi]
      apply Finset.sum_congr
      simp only [IndexValue, Fintype.piFinset_univ]
      intro x _
      rfl
    rw [h1]
    simp only [map_mul]
    exact Finset.prod_congr rfl (fun x _ => rfl)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.prod_mul_distrib]

lemma toTensorRepMat_mul' (i j : IndexValue d c) :
    toTensorRepMat (Λ * Λ') i j = ∑ (k : IndexValue d c),
    ∏ x, colorMatrix (c x) Λ (i x) (k x) * colorMatrix (c x) Λ' (k x) (j x) := by
  simp [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.prod_mul_distrib]
  rfl

@[simp]
lemma toTensorRepMat_on_sum {cX : X → Colors} {cY : Y → Colors}
    (i j : IndexValue d (sumElimIndexColor cX cY)) :
    toTensorRepMat Λ i j = toTensorRepMat Λ (inlIndexValue i) (inlIndexValue j) *
    toTensorRepMat Λ (inrIndexValue i) (inrIndexValue j)  := by
  simp only [toTensorRepMat_apply]
  rw [Fintype.prod_sum_type]
  rfl

open Marked

lemma toTensorRepMap_on_splitIndexValue (T : Marked d X n)
    (i : T.UnmarkedIndexValue) (k : T.MarkedIndexValue) (j : IndexValue d T.color) :
    toTensorRepMat Λ (splitIndexValue.symm (i, k)) j =
    toTensorRepMat Λ i (toUnmarkedIndexValue j) *
    toTensorRepMat Λ k (toMarkedIndexValue j) := by
  simp only [toTensorRepMat_apply]
  rw [Fintype.prod_sum_type]
  rfl

/-!

## Definition of the Lorentz group action on Real Lorentz Tensors.

-/

/-- Action of the Lorentz group on `X`-indexed Real Lorentz Tensors. -/
@[simps!]
instance lorentzAction : MulAction (LorentzGroup d) (RealLorentzTensor d X) where
  smul Λ T := {color := T.color,
                coord := fun i => ∑ j, toTensorRepMat Λ i j * T.coord j}
  one_smul T := by
    refine ext' rfl ?_
    funext i
    simp only [HSMul.hSMul, map_one]
    erw [Finset.sum_eq_single_of_mem i]
    simp only [Matrix.one_apply_eq, one_mul, IndexValue]
    rfl
    exact Finset.mem_univ i
    exact fun j _ hij =>  mul_eq_zero.mpr (Or.inl (Matrix.one_apply_ne' hij))
  mul_smul Λ Λ' T := by
    refine ext' rfl ?_
    simp only [HSMul.hSMul]
    funext i
    have h1 : ∑ j : IndexValue d T.color, toTensorRepMat (Λ * Λ') i j
        * T.coord j = ∑ j : IndexValue d T.color, ∑ (k : IndexValue d T.color),
        (∏ x, ((colorMatrix (T.color x) Λ (i x) (k x)) *
        (colorMatrix (T.color x) Λ' (k x) (j x)))) * T.coord j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [toTensorRepMat_mul', Finset.sum_mul]
    rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [toTensorRepMat, IndexValue]
    rw [← mul_assoc]
    congr
    rw [Finset.prod_mul_distrib]
    rfl

/-!

## The Lorentz action on marked tensors.

-/

@[simps!]
instance  : MulAction (LorentzGroup d) (Marked d X n) := lorentzAction

lemma lorentzAction_on_splitIndexValue' (T : Marked d X n)
    (i : T.UnmarkedIndexValue) (k : T.MarkedIndexValue) :
    (Λ • T).coord (splitIndexValue.symm (i, k)) =
    ∑ (x : T.UnmarkedIndexValue), ∑ (y : T.MarkedIndexValue),
    (toTensorRepMat Λ i x * toTensorRepMat Λ k y) * T.coord (splitIndexValue.symm (x, y)) := by
  erw [lorentzAction_smul_coord]
  erw [← Equiv.sum_comp splitIndexValue.symm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  erw [toTensorRepMap_on_splitIndexValue]
  rfl

@[simp]
lemma lorentzAction_on_splitIndexValue (T : Marked d X n)
    (i : T.UnmarkedIndexValue) (k : T.MarkedIndexValue) :
    (Λ • T).coord (splitIndexValue.symm (i, k)) =
    ∑ (x : T.UnmarkedIndexValue), toTensorRepMat Λ i x *
    ∑ (y : T.MarkedIndexValue), toTensorRepMat Λ k y *
    T.coord (splitIndexValue.symm (x, y)) := by
  rw [lorentzAction_on_splitIndexValue']
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [NonUnitalRing.mul_assoc]


/-!

## Properties of the Lorentz action.

-/


/-- The action on an empty Lorentz tensor is trivial. -/
lemma lorentzAction_on_isEmpty [IsEmpty X] (Λ : LorentzGroup d) (T : RealLorentzTensor d X) :
    Λ • T = T := by
  refine ext' rfl ?_
  funext i
  erw [lorentzAction_smul_coord]
  simp only [Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
    Finset.sum_singleton, toTensorRepMat_apply]
  erw [toTensorRepMat_apply]
  simp only [IndexValue, toTensorRepMat, Unique.eq_default]
  rw [@mul_left_eq_self₀]
  exact Or.inl rfl

/-- The Lorentz action commutes with `congrSet`. -/
lemma lorentzAction_comm_congrSet (f : X ≃ Y) (Λ : LorentzGroup d) (T : RealLorentzTensor d X) :
    congrSet f (Λ • T) = Λ • (congrSet f T) := by
  refine ext' rfl ?_
  funext i
  erw [lorentzAction_smul_coord, lorentzAction_smul_coord]
  erw [← Equiv.sum_comp (congrSetIndexValue d f T.color)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [toTensorRepMat]
  erw [← Equiv.prod_comp f]
  apply Or.inl
  congr
  funext x
  have h1 : (T.color (f.symm (f x))) = T.color x := by
    simp only [Equiv.symm_apply_apply]
  rw [colorMatrix_cast h1]
  simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply]
  erw [castColorsIndex_comp_congrSetIndexValue]
  apply congrFun
  apply congrArg
  symm
  refine cast_eq_iff_heq.mpr ?_
  simp only [congrSetIndexValue, Equiv.piCongrLeft'_symm_apply, heq_eqRec_iff_heq, heq_eq_eq]
  rfl

open Marked

lemma lorentzAction_comm_mul  (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 1)) :
    mul (Λ • T) (Λ • S) h = Λ • mul T S h  := by
  refine ext' rfl ?_
  funext i
  trans ∑ j, toTensorRepMat Λ (inlIndexValue i) (inlIndexValue j) *
    toTensorRepMat Λ (inrIndexValue i) (inrIndexValue j)
    * (mul T S h).coord j
  swap
  refine Finset.sum_congr rfl (fun j _ => ?_)
  erw [toTensorRepMat_on_sum]
  rfl
  change ∑ x, (∑ j, toTensorRepMat Λ (splitIndexValue.symm
    (inlIndexValue i, T.oneMarkedIndexValue x)) j * T.coord j) *
    (∑ k, toTensorRepMat Λ _ k * S.coord k) = _
  trans ∑ x, (∑ j,
    toTensorRepMat  Λ (inlIndexValue i) (toUnmarkedIndexValue j)
    * toTensorRepMat  Λ (T.oneMarkedIndexValue x) (toMarkedIndexValue j)
    * T.coord j) *

  sorry



/-! TODO: Show that the Lorentz action commutes with multiplication. -/
/-! TODO: Show that the Lorentz action commutes with contraction. -/
/-! TODO: Show that the Lorentz action commutes with rising and lowering indices. -/
end RealLorentzTensor
