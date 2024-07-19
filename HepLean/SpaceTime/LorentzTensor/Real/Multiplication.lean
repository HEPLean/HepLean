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

/-- The index value appearing in the multiplication of Marked tensors on the left. -/
def mulFstArg {X Y : Type} {T : Marked d X 1} {S : Marked d Y 1}
    (i : IndexValue d (Sum.elim T.unmarkedColor S.unmarkedColor))
    (x : ColorsIndex d (T.color (markedPoint X 0))) : IndexValue d T.color :=
  splitIndexValue.symm ((indexValueSumEquiv i).1, oneMarkedIndexValue x)

lemma mulFstArg_inr {X Y : Type} {T : Marked d X 1} {S : Marked d Y 1}
    (i : IndexValue d (Sum.elim T.unmarkedColor S.unmarkedColor))
    (x : ColorsIndex d (T.color (markedPoint X 0))) :
    mulFstArg i x (Sum.inr 0) = x := by
  rfl

lemma mulFstArg_inl {X Y : Type} {T : Marked d X 1} {S : Marked d Y 1}
    (i : IndexValue d (Sum.elim T.unmarkedColor S.unmarkedColor))
    (x : ColorsIndex d (T.color (markedPoint X 0))) (c : X):
    mulFstArg i x (Sum.inl c) = i (Sum.inl c) := by
  rfl

/-- The index value appearing in the multiplication of Marked tensors on the right. -/
def mulSndArg {X Y : Type} {T : Marked d X 1} {S : Marked d Y 1}
    (i : IndexValue d (Sum.elim T.unmarkedColor S.unmarkedColor))
    (x : ColorsIndex d (T.color (markedPoint X 0))) (h : T.markedColor 0 = τ (S.markedColor 0)) :
    IndexValue d S.color :=
  splitIndexValue.symm ((indexValueSumEquiv i).2, oneMarkedIndexValue $ colorsIndexDualCast h x)

/-!

## Expressions for multiplication

-/
/-! TODO: Where appropriate write these expresions in terms of `indexValueDualIso`. -/
lemma mul_colorsIndex_right {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    (mul T S h).coord = fun i => ∑ x,
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1,
    oneMarkedIndexValue $ colorsIndexDualCast (color_eq_dual_symm h) x)) *
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, oneMarkedIndexValue x)) := by
  funext i
  rw [← Equiv.sum_comp (colorsIndexDualCast h)]
  apply Finset.sum_congr rfl (fun x _ => ?_)
  congr
  rw [← colorsIndexDualCast_symm]
  exact (Equiv.apply_eq_iff_eq_symm_apply (colorsIndexDualCast h)).mp rfl

lemma mul_indexValue_left {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    (mul T S h).coord = fun i => ∑ j,
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1, j)) *
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2,
    (oneMarkedIndexValue $ (colorsIndexDualCast h) $ oneMarkedIndexValue.symm j))) := by
  funext i
  rw [← Equiv.sum_comp (oneMarkedIndexValue)]
  rfl

lemma mul_indexValue_right {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    (mul T S h).coord = fun i => ∑ j,
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1,
    oneMarkedIndexValue $ (colorsIndexDualCast h).symm $ oneMarkedIndexValue.symm j)) *
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, j)) := by
  funext i
  rw [mul_colorsIndex_right]
  rw [← Equiv.sum_comp (oneMarkedIndexValue)]
  apply Finset.sum_congr rfl (fun x _ => ?_)
  congr
  exact Eq.symm (colorsIndexDualCast_symm h)

/-!

## Properties of multiplication

-/

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
    rw [mul_colorsIndex_right]
    refine Fintype.sum_congr _ _ (fun x => ?_)
    rw [mul_comm]
    rfl

/-- Multiplication commutes with `mapIso`. -/
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
      simp only [IndexValue]
      exact (Equiv.symm_apply_eq splitIndexValue).mpr rfl
    · apply congrArg
      exact (Equiv.symm_apply_eq splitIndexValue).mpr rfl

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

/-!

## Multiplication on selected indices

-/

variable {n m : ℕ} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {X' Y' Z : Type} [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y']
  [Fintype Z] [DecidableEq Z]

/-- The multiplication of two real Lorentz Tensors along specified indices. -/
@[simps!]
def mulS (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y) (x : X) (y : Y)
    (h : T.color x = τ (S.color y)) : RealLorentzTensor d ({x' // x' ≠ x} ⊕ {y' // y' ≠ y}) :=
  mul (markSingle x T) (markSingle y S) h

/-- The first index value appearing in the multiplication of two Lorentz tensors. -/
def mulSFstArg {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0))) :
    IndexValue d T.color := (markSingleIndexValue T x).symm (mulFstArg i a)

lemma mulSFstArg_ext {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    {i j : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor)}
    {a b : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0))}
    (hij : i = j) (hab : a = b) : mulSFstArg i a = mulSFstArg j b := by
  subst hij; subst hab
  rfl

lemma mulSFstArg_on_mem {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0))) :
    mulSFstArg i a x = a := by
  rw [mulSFstArg, markSingleIndexValue]
  simp only [ne_eq, Fintype.univ_ofSubsingleton, Fin.zero_eta, Fin.isValue, Equiv.symm_trans_apply,
     Sum.map_inr, id_eq]
  erw [markEmbeddingIndexValue_apply_symm_on_mem]
  swap
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.image_singleton, embedSingleton_apply, Finset.mem_singleton]
  rw [indexValueIso_symm_apply']
  erw [Equiv.symm_apply_eq, Equiv.symm_apply_eq]
  simp only [Function.comp_apply, colorsIndexCast, Equiv.cast_symm, Equiv.cast_apply, cast_cast]
  symm
  apply cast_eq_iff_heq.mpr
  rw [embedSingleton_toEquivRange_symm]
  rfl

lemma mulSFstArg_on_not_mem {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0)))
    (c : X) (hc : c ≠ x) : mulSFstArg i a c = i (Sum.inl ⟨c, hc⟩) := by
  rw [mulSFstArg, markSingleIndexValue]
  simp only [ne_eq, Fintype.univ_ofSubsingleton, Fin.zero_eta, Fin.isValue, Equiv.symm_trans_apply,
     Sum.map_inr, id_eq]
  erw [markEmbeddingIndexValue_apply_symm_on_not_mem]
  swap
  simpa using hc
  rfl

/-- The second index value appearing in the multiplication of two Lorentz tensors. -/
def mulSSndArg {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0)))
    (h : T.color x = τ (S.color y)) : IndexValue d S.color :=
  (markSingleIndexValue S y).symm (mulSndArg i a h)

lemma mulSSndArg_on_mem {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0)))
    (h : T.color x = τ (S.color y)) : mulSSndArg i a h y = colorsIndexDualCast h a := by
  rw [mulSSndArg, markSingleIndexValue]
  simp only [ne_eq, Fintype.univ_ofSubsingleton, Fin.zero_eta, Fin.isValue, Equiv.symm_trans_apply,
     Sum.map_inr, id_eq]
  erw [markEmbeddingIndexValue_apply_symm_on_mem]
  swap
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.image_singleton, embedSingleton_apply, Finset.mem_singleton]
  rw [indexValueIso_symm_apply']
  erw [Equiv.symm_apply_eq, Equiv.symm_apply_eq]
  simp only [Function.comp_apply, colorsIndexCast, Equiv.cast_symm, Equiv.cast_apply, cast_cast]
  symm
  apply cast_eq_iff_heq.mpr
  rw [embedSingleton_toEquivRange_symm]
  rfl

lemma mulSSndArg_on_not_mem {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0)))
    (h : T.color x = τ (S.color y)) (c : Y) (hc : c ≠ y) :
    mulSSndArg i a h c = i (Sum.inr ⟨c, hc⟩) := by
  rw [mulSSndArg, markSingleIndexValue]
  simp only [ne_eq, Fintype.univ_ofSubsingleton, Fin.zero_eta, Fin.isValue, Equiv.symm_trans_apply,
     Sum.map_inr, id_eq]
  erw [markEmbeddingIndexValue_apply_symm_on_not_mem]
  swap
  simpa using hc
  rfl

lemma mulSSndArg_ext {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    {i j : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor)}
    {a b : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0))}
    (h : T.color x = τ (S.color y)) (hij : i = j) (hab : a = b) :
    mulSSndArg i a h = mulSSndArg j b h := by
  subst hij
  subst hab
  rfl

lemma mulS_coord_arg (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y) (x : X) (y : Y)
    (h : T.color x = τ (S.color y))
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor)) :
  (mulS T S x y h).coord i = ∑ a, T.coord (mulSFstArg i a) * S.coord (mulSSndArg i a h) := by
  rfl

lemma mulS_mapIso (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y)
    (eX : X ≃ X') (eY : Y ≃ Y') (x : X) (y : Y) (x' : X') (y' : Y') (hx : eX x = x')
    (hy : eY y = y') (h : T.color x = τ (S.color y)) :
    mulS (mapIso d eX T) (mapIso d eY S) x' y' (by subst hx hy; simpa using h) =
    mapIso d (Equiv.sumCongr (equivSingleCompl eX hx) (equivSingleCompl eY hy))
      (mulS T S x y h) := by
  rw [mulS, mulS, mul_mapIso]
  congr 1 <;> rw [markSingle_mapIso]

lemma mulS_lorentzAction (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y)
    (x : X) (y : Y) (h : T.color x = τ (S.color y)) (Λ : LorentzGroup d) :
    mulS (Λ • T) (Λ • S) x y h = Λ • mulS T S x y h := by
  rw [mulS, mulS, ← mul_lorentzAction]
  congr 1
  all_goals
    rw [markSingle, markEmbedding, Equiv.trans_apply]
    erw [lorentzAction_mapIso, lorentzAction_mapIso]
    rfl

lemma mulS_symm (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y)
    (x : X) (y : Y) (h : T.color x = τ (S.color y)) :
    mapIso d (Equiv.sumComm _ _) (mulS T S x y h) = mulS S T y x (color_eq_dual_symm h) := by
  rw [mulS, mulS, mul_symm]

/-- An equivalence of types associated with multiplying two consecutive indices,
with the second index appearing on the left. -/
def mulSSplitLeft {y y' : Y} (hy : y ≠ y') (z : Z) :
    {yz // yz ≠ (Sum.inl ⟨y, hy⟩ : {y'' // y'' ≠ y'} ⊕ {z' // z' ≠ z})} ≃
    {y'' // y'' ≠ y' ∧ y'' ≠ y} ⊕ {z' // z' ≠ z} :=
  Equiv.subtypeSum.trans <|
  Equiv.sumCongr (
      (Equiv.subtypeEquivRight (fun a => by
        obtain ⟨a, p⟩ := a; simp only [ne_eq, Sum.inl.injEq, Subtype.mk.injEq])).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _)) <|
  Equiv.subtypeUnivEquiv (fun a => by simp)

/-- An equivalence of types associated with multiplying two consecutive indices with the
second index appearing on the right. -/
def mulSSplitRight {y y' : Y} (hy : y ≠ y') (z : Z) :
    {yz // yz ≠ (Sum.inr ⟨y', hy.symm⟩ : {z' // z' ≠ z} ⊕ {y'' // y'' ≠ y})} ≃
    {z' // z' ≠ z} ⊕ {y'' // y'' ≠ y' ∧ y'' ≠ y} :=
   Equiv.subtypeSum.trans <|
  Equiv.sumCongr (Equiv.subtypeUnivEquiv (fun a => by simp)) <|
  (Equiv.subtypeEquivRight (fun a => by
    obtain ⟨a, p⟩ := a; simp only [ne_eq, Sum.inr.injEq, Subtype.mk.injEq])).trans <|
  ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (Equiv.subtypeEquivRight (fun y'' => And.comm)))

/-- An equivalence of types associated with the associativity property of multiplication. -/
def mulSAssocIso (x : X) {y y' : Y} (hy : y ≠ y') (z : Z) :
    {x' // x' ≠ x} ⊕ {yz // yz ≠ (Sum.inl ⟨y, hy⟩ : {y'' // y'' ≠ y'} ⊕ {z' // z' ≠ z})}
    ≃ {xy // xy ≠ (Sum.inr ⟨y', hy.symm⟩ : {x' // x' ≠ x} ⊕ {y'' // y'' ≠ y})} ⊕ {z' // z' ≠ z} :=
  (Equiv.sumCongr (Equiv.refl _) (mulSSplitLeft hy z)).trans <|
  (Equiv.sumAssoc _ _ _).symm.trans <|
  (Equiv.sumCongr (mulSSplitRight hy x).symm (Equiv.refl _))

lemma mulS_assoc_color {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y}
    {U : RealLorentzTensor d Z} {x : X} {y y' : Y} (hy : y ≠ y') {z : Z}
    (h : T.color x = τ (S.color y))
    (h' : S.color y' = τ (U.color z)) : (mulS (mulS T S x y h) U (Sum.inr ⟨y', hy.symm⟩) z h').color
    = (mapIso d (mulSAssocIso x hy z) (mulS T (mulS S U y' z h') x (Sum.inl ⟨y, hy⟩) h)).color := by
  funext a
  match a with
  | .inl ⟨.inl _, _⟩ => rfl
  | .inl ⟨.inr _, _⟩ => rfl
  | .inr _ => rfl

/-- An equivalence of index values associated with the associativity property of multiplication. -/
def mulSAssocIndexValue {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y}
    {U : RealLorentzTensor d Z} {x : X} {y y' : Y} (hy : y ≠ y') {z : Z}
    (h : T.color x = τ (S.color y)) (h' : S.color y' = τ (U.color z)) :
    IndexValue d ((T.mulS S x y h).mulS U (Sum.inr ⟨y', hy.symm⟩) z h').color ≃
    IndexValue d (T.mulS (S.mulS U y' z h') x (Sum.inl ⟨y, hy⟩) h).color :=
  indexValueIso d (mulSAssocIso x hy z).symm (mulS_assoc_color hy h h')

/-- Multiplication of indices is associative, up to a `mapIso` equivalence. -/
lemma mulS_assoc (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y) (U : RealLorentzTensor d Z)
    (x : X) (y y' : Y) (hy : y ≠ y') (z : Z) (h : T.color x = τ (S.color y))
    (h' : S.color y' = τ (U.color z)) : mulS (mulS T S x y h) U (Sum.inr ⟨y', hy.symm⟩) z h' =
    mapIso d (mulSAssocIso x hy z) (mulS T (mulS S U y' z h') x (Sum.inl ⟨y, hy⟩) h) := by
  apply ext ?_ ?_
  · funext a
    match a with
    | .inl ⟨.inl _, _⟩ => rfl
    | .inl ⟨.inr _, _⟩ => rfl
    | .inr _ => rfl
  funext i
  trans ∑ a, (∑ b, T.coord (mulSFstArg (mulSFstArg i a) b) *
    S.coord (mulSSndArg (mulSFstArg i a) b h)) * U.coord (mulSSndArg i a h')
  rfl
  trans ∑ a, T.coord (mulSFstArg (mulSAssocIndexValue hy h h' i) a) *
    (∑ b, S.coord (mulSFstArg (mulSSndArg (mulSAssocIndexValue hy h h' i) a h) b) *
    U.coord (mulSSndArg (mulSSndArg (mulSAssocIndexValue hy h h' i) a h) b h'))
  swap
  rw [mapIso_apply_coord, mulS_coord_arg, indexValueIso_symm]
  rfl
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_mul _ _ _)]
  rw [Finset.sum_congr rfl (fun x _ => Finset.mul_sum _ _ _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [mul_assoc]
  refine Mathlib.Tactic.Ring.mul_congr rfl (Mathlib.Tactic.Ring.mul_congr ?_ rfl rfl) rfl
  apply congrArg
  funext c
  by_cases hcy : c = y
  · subst hcy
    rw [mulSSndArg_on_mem, mulSFstArg_on_not_mem, mulSSndArg_on_mem]
    rfl
  · by_cases hcy' : c = y'
    · subst hcy'
      rw [mulSFstArg_on_mem, mulSSndArg_on_not_mem, mulSFstArg_on_mem]
    · rw [mulSFstArg_on_not_mem, mulSSndArg_on_not_mem, mulSSndArg_on_not_mem,
        mulSFstArg_on_not_mem]
      rw [mulSAssocIndexValue, indexValueIso_eq_symm, indexValueIso_symm_apply']
      simp [colorsIndexCast, Equiv.refl_apply]
      erw [Equiv.refl_apply]
      rfl
      exact hcy'
      simpa using hcy

end RealLorentzTensor
