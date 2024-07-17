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
  (T : RealLorentzTensor d X) (c : X → Colors) (Λ Λ' : LorentzGroup d) {μ : Colors}

open LorentzGroup BigOperators Marked

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
    Matrix.reindex (colorsIndexCast h).symm (colorsIndexCast h).symm (colorMatrix ν Λ) := by
  subst h
  rfl

lemma colorMatrix_dual_cast {μ : Colors} (Λ : LorentzGroup d) :
    colorMatrix (τ μ) Λ = Matrix.reindex (colorsIndexDualCastSelf) (colorsIndexDualCastSelf)
    (colorMatrix μ (LorentzGroup.transpose Λ⁻¹)) := by
  match μ with
  | .up => rfl
  | .down =>
    ext i j
    simp only [τ, colorMatrix, MonoidHom.coe_mk, OneHom.coe_mk, colorsIndexDualCastSelf, transpose,
      lorentzGroupIsGroup_inv, Matrix.transpose_apply, minkowskiMetric.dual_transpose,
      minkowskiMetric.dual_dual, Matrix.reindex_apply, Equiv.coe_fn_symm_mk, Matrix.submatrix_apply]
lemma colorMatrix_transpose {μ : Colors} (Λ : LorentzGroup d) :
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
lemma toTensorRepMat_of_indexValueSumEquiv {cX : X → Colors} {cY : Y → Colors}
    (i j : IndexValue d (Sum.elim cX cY)) :
    toTensorRepMat Λ i j = toTensorRepMat Λ (indexValueSumEquiv i).1 (indexValueSumEquiv j).1 *
    toTensorRepMat Λ (indexValueSumEquiv i).2 (indexValueSumEquiv j).2 := by
  simp only [toTensorRepMat_apply]
  rw [Fintype.prod_sum_type]
  rfl

lemma toTensorRepMat_of_indexValueSumEquiv' {cX : X → Colors} {cY : Y → Colors}
    (i j : IndexValue d cX) (k l : IndexValue d cY) :
    toTensorRepMat Λ i j * toTensorRepMat Λ k l =
    toTensorRepMat Λ (indexValueSumEquiv.symm (i, k)) (indexValueSumEquiv.symm (j, l)) := by
  simp only [toTensorRepMat_apply]
  rw [Fintype.prod_sum_type]
  rfl

/-!

## Tensor representation matrices and marked tensors.

-/

lemma toTensorRepMat_of_splitIndexValue' (T : Marked d X n)
    (i j : T.UnmarkedIndexValue) (k l : T.MarkedIndexValue) :
    toTensorRepMat Λ i j * toTensorRepMat Λ k l =
    toTensorRepMat Λ (splitIndexValue.symm (i, k)) (splitIndexValue.symm (j, l)) := by
  simp only [toTensorRepMat_apply]
  rw [Fintype.prod_sum_type]
  rfl

lemma toTensorRepMat_oneMarkedIndexValue_dual (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) (x : ColorsIndex d (T.markedColor 0))
    (k : S.MarkedIndexValue) :
    toTensorRepMat Λ (oneMarkedIndexValue $ colorsIndexDualCast h x) k =
    toTensorRepMat Λ⁻¹ (oneMarkedIndexValue
      $ (colorsIndexDualCast h).symm $ oneMarkedIndexValue.symm k)
      (oneMarkedIndexValue x) := by
  rw [toTensorRepMat_apply, toTensorRepMat_apply]
  erw [Finset.prod_singleton, Finset.prod_singleton]
  simp only [Fin.zero_eta, Fin.isValue, lorentzGroupIsGroup_inv]
  rw [colorMatrix_cast h, colorMatrix_dual_cast]
  rw [Matrix.reindex_apply, Matrix.reindex_apply]
  simp only [Fin.isValue, lorentzGroupIsGroup_inv, minkowskiMetric.dual_dual, Subtype.coe_eta,
    Equiv.symm_symm, Matrix.submatrix_apply]
  rw [colorMatrix_transpose]
  simp only [Fin.isValue, Matrix.transpose_apply]
  apply congrArg
  simp only [Fin.isValue, oneMarkedIndexValue, colorsIndexDualCast, Equiv.coe_fn_symm_mk,
    Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.coe_fn_mk, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply]

lemma toTensorRepMap_sum_dual (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) (j : T.MarkedIndexValue) (k : S.MarkedIndexValue) :
    ∑ x, toTensorRepMat Λ (oneMarkedIndexValue $ colorsIndexDualCast h x) k
    * toTensorRepMat Λ (oneMarkedIndexValue x) j =
    toTensorRepMat 1
    (oneMarkedIndexValue $ (colorsIndexDualCast h).symm $ oneMarkedIndexValue.symm k) j := by
  trans ∑ x, toTensorRepMat Λ⁻¹ (oneMarkedIndexValue$ (colorsIndexDualCast h).symm $
    oneMarkedIndexValue.symm k) (oneMarkedIndexValue x) * toTensorRepMat Λ (oneMarkedIndexValue x) j
  apply Finset.sum_congr rfl (fun x _ => ?_)
  rw [toTensorRepMat_oneMarkedIndexValue_dual]
  rw [← Equiv.sum_comp oneMarkedIndexValue.symm]
  change ∑ i, toTensorRepMat Λ⁻¹ (oneMarkedIndexValue $ (colorsIndexDualCast h).symm $
    oneMarkedIndexValue.symm k) i * toTensorRepMat Λ i j = _
  rw [← Matrix.mul_apply, ← toTensorRepMat.map_mul, inv_mul_self Λ]

lemma toTensorRepMat_one_coord_sum (T : Marked d X n) (i : T.UnmarkedIndexValue)
    (k : T.MarkedIndexValue) : T.coord (splitIndexValue.symm (i, k)) = ∑ j, toTensorRepMat 1 k j *
    T.coord (splitIndexValue.symm (i, j)) := by
  erw [Finset.sum_eq_single_of_mem k]
  simp only [IndexValue, map_one, Matrix.one_apply_eq, one_mul]
  exact Finset.mem_univ k
  intro j _ hjk
  simp [hjk]
  exact Or.inl (Matrix.one_apply_ne' hjk)

/-!

## Definition of the Lorentz group action on Real Lorentz Tensors.

-/

/-- Action of the Lorentz group on `X`-indexed Real Lorentz Tensors. -/
@[simps!]
instance lorentzAction : MulAction (LorentzGroup d) (RealLorentzTensor d X) where
  smul Λ T := {color := T.color,
                coord := fun i => ∑ j, toTensorRepMat Λ i j * T.coord j}
  one_smul T := by
    refine ext rfl ?_
    funext i
    simp only [HSMul.hSMul, map_one]
    erw [Finset.sum_eq_single_of_mem i]
    simp only [Matrix.one_apply_eq, one_mul, IndexValue]
    rfl
    exact Finset.mem_univ i
    exact fun j _ hij => mul_eq_zero.mpr (Or.inl (Matrix.one_apply_ne' hij))
  mul_smul Λ Λ' T := by
    refine ext rfl ?_
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

lemma lorentzAction_smul_coord' {d : ℕ} {X : Type} [Fintype X] [DecidableEq X] (Λ : ↑(𝓛 d))
    (T : RealLorentzTensor d X) (i : IndexValue d T.color) :
    (Λ • T).coord i = ∑ j : IndexValue d T.color, toTensorRepMat Λ i j * T.coord j := by
  rfl

/-!

## Properties of the Lorentz action.

-/

/-- The action on an empty Lorentz tensor is trivial. -/
lemma lorentzAction_on_isEmpty [IsEmpty X] (Λ : LorentzGroup d) (T : RealLorentzTensor d X) :
    Λ • T = T := by
  refine ext rfl ?_
  funext i
  erw [lorentzAction_smul_coord]
  simp only [Finset.univ_unique, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
    Finset.sum_singleton, toTensorRepMat_apply]
  erw [toTensorRepMat_apply]
  simp only [IndexValue, toTensorRepMat, Unique.eq_default]
  rw [@mul_left_eq_self₀]
  exact Or.inl rfl

/-- The Lorentz action commutes with `mapIso`. -/
lemma lorentzAction_mapIso (f : X ≃ Y) (Λ : LorentzGroup d) (T : RealLorentzTensor d X) :
    mapIso d f (Λ • T) = Λ • (mapIso d f T) := by
  refine ext rfl ?_
  funext i
  rw [mapIso_apply_coord]
  rw [lorentzAction_smul_coord', lorentzAction_smul_coord']
  let is : IndexValue d T.color ≃ IndexValue d ((mapIso d f) T).color :=
    indexValueIso d f (by funext x; simp)
  rw [← Equiv.sum_comp is]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [mapIso_apply_coord]
  refine Mathlib.Tactic.Ring.mul_congr ?_ ?_ rfl
  · simp only [IndexValue, toTensorRepMat, MonoidHom.coe_mk, OneHom.coe_mk, mapIso_apply_color,
    indexValueIso_refl]
    rw [← Equiv.prod_comp f]
    apply Finset.prod_congr rfl (fun x _ => ?_)
    have h1 : (T.color (f.symm (f x))) = T.color x := by
      simp only [Equiv.symm_apply_apply]
    rw [colorMatrix_cast h1]
    apply congrArg
    simp only [is]
    erw [indexValueIso_eq_symm, indexValueIso_symm_apply']
    simp only [colorsIndexCast, Function.comp_apply, mapIso_apply_color, Equiv.cast_refl,
      Equiv.refl_symm, Equiv.refl_apply, Equiv.cast_apply]
    symm
    refine cast_eq_iff_heq.mpr ?_
    congr
    exact Equiv.symm_apply_apply f x
  · apply congrArg
    funext a
    simp only [IndexValue, mapIso_apply_color, Equiv.symm_apply_apply, is]

/-!

## The Lorentz action on marked tensors.

-/

@[simps!]
instance : MulAction (LorentzGroup d) (Marked d X n) := lorentzAction

/-- Action of the Lorentz group on just marked indices. -/
@[simps!]
def markedLorentzAction : MulAction (LorentzGroup d) (Marked d X n) where
  smul Λ T := {
    color := T.color,
    coord := fun i => ∑ j, toTensorRepMat Λ (splitIndexValue i).2 j *
      T.coord (splitIndexValue.symm ((splitIndexValue i).1, j))}
  one_smul T := by
    refine ext rfl ?_
    funext i
    simp only [HSMul.hSMul, map_one]
    erw [Finset.sum_eq_single_of_mem (splitIndexValue i).2]
    erw [Matrix.one_apply_eq (splitIndexValue i).2]
    simp only [IndexValue, one_mul, indexValueIso_refl, Equiv.refl_apply]
    apply congrArg
    exact Equiv.symm_apply_apply splitIndexValue i
    exact Finset.mem_univ (splitIndexValue i).2
    exact fun j _ hij => mul_eq_zero.mpr (Or.inl (Matrix.one_apply_ne' hij))
  mul_smul Λ Λ' T := by
    refine ext rfl ?_
    simp only [HSMul.hSMul]
    funext i
    have h1 : ∑ (j : T.MarkedIndexValue), toTensorRepMat (Λ * Λ') (splitIndexValue i).2 j
        * T.coord (splitIndexValue.symm ((splitIndexValue i).1, j)) =
        ∑ (j : T.MarkedIndexValue), ∑ (k : T.MarkedIndexValue),
        (∏ x, ((colorMatrix (T.markedColor x) Λ ((splitIndexValue i).2 x) (k x)) *
        (colorMatrix (T.markedColor x) Λ' (k x) (j x)))) *
        T.coord (splitIndexValue.symm ((splitIndexValue i).1, j)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [toTensorRepMat_mul', Finset.sum_mul]
      rfl
    erw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [toTensorRepMat, IndexValue]
    rw [← mul_assoc]
    congr
    rw [Finset.prod_mul_distrib]
    rfl

/-- Action of the Lorentz group on just unmarked indices. -/
@[simps!]
def unmarkedLorentzAction : MulAction (LorentzGroup d) (Marked d X n) where
  smul Λ T := {
    color := T.color,
    coord := fun i => ∑ j, toTensorRepMat Λ (splitIndexValue i).1 j *
      T.coord (splitIndexValue.symm (j, (splitIndexValue i).2))}
  one_smul T := by
    refine ext rfl ?_
    funext i
    simp only [HSMul.hSMul, map_one]
    erw [Finset.sum_eq_single_of_mem (splitIndexValue i).1]
    erw [Matrix.one_apply_eq (splitIndexValue i).1]
    simp only [IndexValue, one_mul, indexValueIso_refl, Equiv.refl_apply]
    apply congrArg
    exact Equiv.symm_apply_apply splitIndexValue i
    exact Finset.mem_univ (splitIndexValue i).1
    exact fun j _ hij => mul_eq_zero.mpr (Or.inl (Matrix.one_apply_ne' hij))
  mul_smul Λ Λ' T := by
    refine ext rfl ?_
    simp only [HSMul.hSMul]
    funext i
    have h1 : ∑ (j : T.UnmarkedIndexValue), toTensorRepMat (Λ * Λ') (splitIndexValue i).1 j
        * T.coord (splitIndexValue.symm (j, (splitIndexValue i).2)) =
        ∑ (j : T.UnmarkedIndexValue), ∑ (k : T.UnmarkedIndexValue),
        (∏ x, ((colorMatrix (T.unmarkedColor x) Λ ((splitIndexValue i).1 x) (k x)) *
        (colorMatrix (T.unmarkedColor x) Λ' (k x) (j x)))) *
        T.coord (splitIndexValue.symm (j, (splitIndexValue i).2)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [toTensorRepMat_mul', Finset.sum_mul]
      rfl
    erw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [toTensorRepMat, IndexValue]
    rw [← mul_assoc]
    congr
    rw [Finset.prod_mul_distrib]
    rfl

scoped[RealLorentzTensor] infixr:73 " •ₘ " => markedLorentzAction.smul
scoped[RealLorentzTensor] infixr:73 " •ᵤₘ " => unmarkedLorentzAction.smul

/-- Acting on unmarked and then marked indices is equivalent to acting on all indices. -/
lemma marked_unmarked_action_eq_action (T : Marked d X n) : Λ •ₘ (Λ •ᵤₘ T) = Λ • T := by
  refine ext rfl ?_
  funext i
  change ∑ j, toTensorRepMat Λ (splitIndexValue i).2 j *
    (∑ k, toTensorRepMat Λ (splitIndexValue i).1 k * T.coord (splitIndexValue.symm (k, j))) = _
  trans ∑ j, ∑ k, (toTensorRepMat Λ (splitIndexValue i).2 j *
      toTensorRepMat Λ (splitIndexValue i).1 k) * T.coord (splitIndexValue.symm (k, j))
  apply Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun k _ => ?_)
  exact Eq.symm (mul_assoc _ _ _)
  trans ∑ j, ∑ k, (toTensorRepMat Λ i (splitIndexValue.symm (k, j))
    * T.coord (splitIndexValue.symm (k, j)))
  apply Finset.sum_congr rfl (fun j _ => (Finset.sum_congr rfl (fun k _ => ?_)))
  rw [mul_comm (toTensorRepMat _ _ _), toTensorRepMat_of_splitIndexValue']
  simp only [IndexValue, Finset.mem_univ, Prod.mk.eta, Equiv.symm_apply_apply]
  trans ∑ p, (toTensorRepMat Λ i p * T.coord p)
  rw [← Equiv.sum_comp splitIndexValue.symm, Fintype.sum_prod_type, Finset.sum_comm]
  rfl
  rfl

/-- Acting on marked and then unmarked indices is equivalent to acting on all indices. -/
lemma unmarked_marked_action_eq_action (T : Marked d X n) : Λ •ᵤₘ (Λ •ₘ T) = Λ • T := by
  refine ext rfl ?_
  funext i
  change ∑ j, toTensorRepMat Λ (splitIndexValue i).1 j *
      (∑ k, toTensorRepMat Λ (splitIndexValue i).2 k * T.coord (splitIndexValue.symm (j, k))) = _
  trans ∑ j, ∑ k, (toTensorRepMat Λ (splitIndexValue i).1 j *
      toTensorRepMat Λ (splitIndexValue i).2 k) * T.coord (splitIndexValue.symm (j, k))
  apply Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl (fun k _ => ?_)
  exact Eq.symm (mul_assoc _ _ _)
  trans ∑ j, ∑ k, (toTensorRepMat Λ i (splitIndexValue.symm (j, k))
    * T.coord (splitIndexValue.symm (j, k)))
  apply Finset.sum_congr rfl (fun j _ => (Finset.sum_congr rfl (fun k _ => ?_)))
  rw [toTensorRepMat_of_splitIndexValue']
  simp only [IndexValue, Finset.mem_univ, Prod.mk.eta, Equiv.symm_apply_apply]
  trans ∑ p, (toTensorRepMat Λ i p * T.coord p)
  rw [← Equiv.sum_comp splitIndexValue.symm, Fintype.sum_prod_type]
  rfl
  rfl

/-- The marked and unmarked actions commute. -/
lemma marked_unmarked_action_comm (T : Marked d X n) : Λ •ᵤₘ (Λ •ₘ T) = Λ •ₘ (Λ •ᵤₘ T) := by
  rw [unmarked_marked_action_eq_action, marked_unmarked_action_eq_action]

/-! TODO: Show that the Lorentz action commutes with contraction. -/
/-! TODO: Show that the Lorentz action commutes with rising and lowering indices. -/
end RealLorentzTensor
