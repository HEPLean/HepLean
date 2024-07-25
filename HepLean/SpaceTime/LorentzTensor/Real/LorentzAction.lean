/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Real.Basic
import HepLean.SpaceTime.LorentzGroup.Basic
import Mathlib.RepresentationTheory.Basic
/-!

# Lorentz group action on Real Lorentz Tensors

We define the action of the Lorentz group on Real Lorentz Tensors.

The Lorentz action is currently only defined for finite and decidable types `X`.

-/

namespace RealLorentzTensor

variable {d : ℕ} {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
   (c : X → Color) (Λ Λ' : LorentzGroup d) {μ : Color}

open LorentzGroup BigOperators

/-- Monoid homomorphism from the Lorentz group to matrices indexed by `ColorsIndex d μ` for a
  color `μ`.

  This can be thought of as the representation of the Lorentz group for that color index. -/
def colorMatrix (μ : Color) : LorentzGroup d →* Matrix (ColorIndex d μ) (ColorIndex d μ) ℝ where
  toFun Λ := match μ with
    | .up => fun i j => Λ.1 i j
    | .down => fun i j => (LorentzGroup.transpose Λ⁻¹).1 i j
  map_one' := by
    ext i j
    match μ with
    | .up =>
        simp only [lorentzGroupIsGroup_one_coe, OfNat.ofNat, One.one, ColorIndex]
        congr
    | .down =>
        simp only [transpose, inv_one, lorentzGroupIsGroup_one_coe, Matrix.transpose_one]
        simp only [OfNat.ofNat, One.one, ColorIndex]
        congr
  map_mul' Λ Λ' := by
    ext i j
    match μ with
    | .up =>
        simp only [lorentzGroupIsGroup_mul_coe]
    | .down =>
        simp only [transpose, mul_inv_rev, lorentzGroupIsGroup_inv, lorentzGroupIsGroup_mul_coe,
          Matrix.transpose_mul, Matrix.transpose_apply]
        rfl

lemma colorMatrix_ext  {μ : Color} {a b c d : ColorIndex d μ} (hab : a = b) (hcd : c = d) :
    (colorMatrix μ) Λ  a c = (colorMatrix  μ) Λ b d := by
    rw [hab, hcd]

lemma colorMatrix_cast {μ ν : Color} (h : μ = ν) (Λ : LorentzGroup d) :
    colorMatrix ν Λ =
    Matrix.reindex (colorIndexCast h) (colorIndexCast h) (colorMatrix μ Λ) := by
  subst h
  rfl

lemma colorMatrix_dual_cast {μ ν : Color} (Λ : LorentzGroup d) (h : μ = τ ν) :
    colorMatrix ν Λ = Matrix.reindex (colorIndexDualCast h) (colorIndexDualCast h)
    (colorMatrix μ (LorentzGroup.transpose Λ⁻¹)) := by
  subst h
  match ν with
  | .up =>
    ext i j
    simp only [colorMatrix, MonoidHom.coe_mk, OneHom.coe_mk, τ, transpose, lorentzGroupIsGroup_inv,
      Matrix.transpose_apply, minkowskiMetric.dual_transpose, minkowskiMetric.dual_dual,
      Matrix.reindex_apply, colorIndexDualCast_symm, Matrix.submatrix_apply]
    rfl
  | .down =>
    ext i j
    simp only [τ, colorMatrix, MonoidHom.coe_mk, OneHom.coe_mk, colorIndexDualCastSelf, transpose,
      lorentzGroupIsGroup_inv, Matrix.transpose_apply, minkowskiMetric.dual_transpose,
      minkowskiMetric.dual_dual, Matrix.reindex_apply, Equiv.coe_fn_symm_mk, Matrix.submatrix_apply]
    rfl

lemma colorMatrix_transpose {μ : Color} (Λ : LorentzGroup d) :
    colorMatrix μ (LorentzGroup.transpose Λ) = (colorMatrix μ Λ).transpose := by
  match μ with
  | .up => rfl
  | .down =>
    ext i j
    simp only [colorMatrix, transpose, lorentzGroupIsGroup_inv, Matrix.transpose_apply,
      MonoidHom.coe_mk, OneHom.coe_mk, minkowskiMetric.dual_transpose]

/-!

## Lorentz group to tensor representation matrices.

-/

/-- The matrix representation of the Lorentz group given a color of index. -/
@[simps!]
def toTensorRepMat {c : X → Color} :
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
      rfl
    rw [h1]
    simp only [map_mul]
    rfl
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.prod_mul_distrib]

lemma toTensorRepMat_mul' (i j : IndexValue d c) :
    toTensorRepMat (Λ * Λ') i j = ∑ (k : IndexValue d c),
    ∏ x, colorMatrix (c x) Λ (i x) (k x) * colorMatrix (c x) Λ' (k x) (j x) := by
  simp [Matrix.mul_apply, IndexValue]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.prod_mul_distrib]
  rfl

lemma toTensorRepMat_of_indexValueSumEquiv {cX : X → Color} {cY : Y → Color}
    (i j : IndexValue d (Sum.elim cX cY)) :
    toTensorRepMat Λ i j = toTensorRepMat Λ (indexValueTensorator i).1 (indexValueTensorator j).1 *
    toTensorRepMat Λ (indexValueTensorator i).2 (indexValueTensorator j).2 :=
  Fintype.prod_sum_type fun x => (colorMatrix (Sum.elim cX cY x)) Λ (i x) (j x)

lemma toTensorRepMat_of_indexValueSumEquiv' {cX : X → Color} {cY : Y → Color}
    (i j : IndexValue d cX) (k l : IndexValue d cY) :
    toTensorRepMat Λ i j * toTensorRepMat Λ k l =
    toTensorRepMat Λ (indexValueTensorator.symm (i, k)) (indexValueTensorator.symm (j, l)) :=
  (Fintype.prod_sum_type fun x => (colorMatrix (Sum.elim cX cY x)) Λ
    (indexValueTensorator.symm (i, k) x) (indexValueTensorator.symm (j, l) x)).symm

/-!

## Tensor representation matrices and marked tensors.

-/

lemma toTensorRepMat_indexValueDualIso_left {f1 : X → Color} {f2 : Y → Color}
    (e : X ≃ Y) (hc : f1 = τ ∘ f2 ∘ e) (i : IndexValue d f1) (j : IndexValue d f2) :
    toTensorRepMat Λ (indexValueDualIso d e hc i) j =
    toTensorRepMat Λ⁻¹ (indexValueDualIso d e.symm (indexValueDualIso_cond_symm hc) j) i := by
  rw [toTensorRepMat_apply, toTensorRepMat_apply, ← Equiv.prod_comp e]
  apply Finset.prod_congr rfl (fun x _ => ?_)
  erw [colorMatrix_dual_cast Λ (congrFun hc x)]
  rw [Matrix.reindex_apply, colorMatrix_transpose]
  simp only [Function.comp_apply, colorIndexDualCast_symm,
    Matrix.submatrix_apply, Matrix.transpose_apply]
  rw [indexValueDualIso_eq_symm, indexValueDualIso_symm_apply',
    indexValueDualIso_eq_symm, indexValueDualIso_symm_apply']
  rw [← Equiv.trans_apply, colorIndexDualCast_symm, colorsIndexDualCast_trans]
  apply colorMatrix_ext
  simp
  simp [colorIndexCast]
  apply cast_eq_iff_heq.mpr
  rw [Equiv.symm_apply_apply]

lemma toTensorRepMat_indexValueDualIso_sum {f1 : X → Color} {f2 : Y → Color}
    (e : X ≃ Y) (hc : f1 = τ ∘ f2 ∘ e) (j : IndexValue d f1) (k : IndexValue d f2) :
    (∑ i : IndexValue d f1, toTensorRepMat Λ ((indexValueDualIso d e hc) i) k * toTensorRepMat Λ i j) =
    toTensorRepMat 1 (indexValueDualIso d e.symm (indexValueDualIso_cond_symm hc) k) j := by
  trans ∑ i, toTensorRepMat Λ⁻¹ (indexValueDualIso d e.symm (indexValueDualIso_cond_symm hc) k) i
    * toTensorRepMat Λ i j
  apply Finset.sum_congr rfl (fun i _ => ?_)
  rw [toTensorRepMat_indexValueDualIso_left]
  rw [← Matrix.mul_apply, ← toTensorRepMat.map_mul, inv_mul_self Λ]

lemma toTensorRepMat_one_coord_sum' {f1 : X → Color}
      (T : RealLorentzTensor d f1) (k : IndexValue d f1) :
        ∑ j, (toTensorRepMat 1 k j) * T j = T k := by
  erw [Finset.sum_eq_single_of_mem k]
  simp only [IndexValue, map_one, Matrix.one_apply_eq, one_mul]
  exact Finset.mem_univ k
  intro j _ hjk
  simp only [IndexValue, map_one, mul_eq_zero]
  exact Or.inl (Matrix.one_apply_ne' hjk)


/-!

## Definition of the Lorentz group action on Real Lorentz Tensors.

-/
@[simps!]
def lorentzAction {c : X → Color} :
    Representation ℝ (LorentzGroup d) (RealLorentzTensor d c) where
  toFun Λ :=  {
    toFun := fun T i => ∑ j, toTensorRepMat Λ i j * T j,
    map_add' := fun T S => by
      funext i
      trans  ∑ j,  (toTensorRepMat Λ i j * T j + toTensorRepMat Λ i j * S j)
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        erw [mul_add]
      · rw [Finset.sum_add_distrib]
        rfl
    map_smul' := fun a T => by
      funext i
      simp only [ RingHom.id_apply]
      trans ∑ j, a * (toTensorRepMat Λ i j * T j)
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← mul_assoc, mul_comm a _,  mul_assoc]
        rfl
      · rw [← Finset.mul_sum]
        rfl}
  map_one' := by
    ext T
    simp only [map_one, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.one_apply]
    funext i
    rw [Finset.sum_eq_single_of_mem i]
    simp only [Matrix.one_apply_eq, one_mul]
    exact Finset.mem_univ i
    exact fun j _ hij => mul_eq_zero.mpr (Or.inl (Matrix.one_apply_ne' hij))
  map_mul' Λ Λ' := by
    ext T
    simp only
    funext i
    trans ∑ j, ∑ k : IndexValue d c, (∏ x, colorMatrix (c x) Λ (i x) (k x) *
      colorMatrix (c x) Λ' (k x) (j x)) * T j
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [toTensorRepMat_mul', Finset.sum_mul]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, toTensorRepMat, IndexValue]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [← mul_assoc, Finset.prod_mul_distrib]
      rfl

scoped[RealLorentzTensor] infixl:78 " • " => lorentzAction

/-- The Lorentz action commutes with `mapIso`. -/
lemma lorentzAction_mapIso (e : X ≃ Y) {f1 : X → Color}
    {f2 : Y → Color} (h : f1 = f2 ∘ e) (Λ : LorentzGroup d)
    (T : RealLorentzTensor d f1) : mapIso e h (Λ • T) = Λ • (mapIso e h T) := by
  funext i
  rw [mapIso_apply, lorentzAction_apply_apply, lorentzAction_apply_apply]
  rw [← Equiv.sum_comp (indexValueIso d e h)]
  refine Finset.sum_congr rfl (fun j _ => Mathlib.Tactic.Ring.mul_congr ?_ ?_ rfl)
  · rw [← Equiv.prod_comp e]
    apply Finset.prod_congr rfl (fun x _ => ?_)
    erw [colorMatrix_cast (congrFun h x)]
    rw [Matrix.reindex_apply]
    simp
    apply colorMatrix_ext
    rw [indexValueIso_eq_symm, indexValueIso_symm_apply']
    erw [← Equiv.eq_symm_apply]
    simp only [Function.comp_apply, Equiv.symm_symm_apply, colorIndexCast, Equiv.cast_symm,
      Equiv.cast_apply, cast_cast, cast_eq]
    rw [indexValueIso_eq_symm, indexValueIso_symm_apply']
    simp [colorIndexCast]
    symm
    refine cast_eq_iff_heq.mpr ?_
    rw [Equiv.symm_apply_apply]
  · rw [mapIso_apply]
    apply congrArg
    rw [← Equiv.trans_apply]
    simp



section
variable {d : ℕ} {X Y Y' X'  : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype X'] [DecidableEq X']
  (cX : X → Color) (cY : Y → Color)

lemma lorentzAction_basis (Λ : LorentzGroup d)  (i : IndexValue d cX) :
    Λ • (basis cX i) = ∑ j, toTensorRepMat Λ j i • basis cX j := by
  funext k
  simp only [lorentzAction, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem i, Finset.sum_eq_single_of_mem k]
  change _ = toTensorRepMat Λ k i * (Pi.basisFun ℝ (IndexValue d cX)) k k
  rw [basis]
  erw [Pi.basisFun_apply, Pi.basisFun_apply]
  simp
  exact Finset.mem_univ k
  intro b _ hbk
  change toTensorRepMat Λ b i • (basis cX) b k = 0
  erw [basis, Pi.basisFun_apply]
  simp [hbk]
  exact Finset.mem_univ i
  intro b hb hbk
  erw [basis, Pi.basisFun_apply]
  simp [hbk]
  intro a
  subst a
  simp_all only [Finset.mem_univ, ne_eq, not_true_eq_false]

end
end RealLorentzTensor
