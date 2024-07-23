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

section mulMarkedFiber

variable {cX : X → Colors} {cY : Y → Colors} {fX : Fin 1 → Colors} {fY : Fin 1 → Colors}

/-- The index value appearing in the multiplication of Marked tensors on the left. -/
def mulMarkedFiberFstArg  (i : IndexValue d (Sum.elim cX cY)) (x : ColorsIndex d (fX 0)) :
    IndexValue d (Sum.elim cX fX) :=
  indexValueSumEquiv.symm ((indexValueSumEquiv i).1, indexValueFinOne x)

/-- The index value appearing in the multiplication of Marked tensors on the right. -/
def mulMarkedFiberSndArg (i : IndexValue d (Sum.elim cX cY)) (x : ColorsIndex d (fX 0))
    (h : fX 0 = τ (fY 0)) : IndexValue d (Sum.elim cY fY) :=
  indexValueSumEquiv.symm ((indexValueSumEquiv i).2, indexValueFinOne $ colorsIndexDualCast h x)

def mulMarkedFiber (h : fX 0 = τ (fY 0)) : ColorFiber d (Sum.elim cX fX) →ₗ[ℝ]
      ColorFiber d (Sum.elim cY fY) →ₗ[ℝ] ColorFiber d (Sum.elim cX cY) where
  toFun T := {
    toFun := fun S i => ∑ x, T (mulMarkedFiberFstArg i x) * S (mulMarkedFiberSndArg i x h),
    map_add' := fun F S => by
      funext i
      trans ∑ x , (T (mulMarkedFiberFstArg i x) * F (mulMarkedFiberSndArg i x h) +
        T (mulMarkedFiberFstArg i x) * S (mulMarkedFiberSndArg i x h))
      exact Finset.sum_congr rfl (fun x _ => mul_add _ _ _ )
      exact Finset.sum_add_distrib,
    map_smul' := fun r S => by
      funext i
      trans ∑ x , r * (T (mulMarkedFiberFstArg i x) * S (mulMarkedFiberSndArg i x h))
      refine Finset.sum_congr rfl (fun x _ => ?_)
      ring_nf
      rw [mul_assoc]
      rfl
      rw [← Finset.mul_sum]
      rfl}
  map_add' := fun T S => by
    ext F
    funext i
    trans ∑ x , (T (mulMarkedFiberFstArg i x) * F (mulMarkedFiberSndArg i x h) +
        S (mulMarkedFiberFstArg i x) * F (mulMarkedFiberSndArg i x h))
    exact Finset.sum_congr rfl (fun x _ => add_mul _ _ _)
    exact Finset.sum_add_distrib
  map_smul' := fun r T => by
    ext S
    funext i
    trans ∑ x , r * (T (mulMarkedFiberFstArg i x) * S (mulMarkedFiberSndArg i x h))
    refine Finset.sum_congr rfl (fun x _ => mul_assoc _ _ _)
    rw [← Finset.mul_sum]
    rfl

end mulMarkedFiber

/-- The contraction of the marked indices of two tensors each with one marked index, which
is dual to the others. The contraction is done via
`φ^μ ψ_μ = φ^0 ψ_0 + φ^1 ψ_1 + ...`. -/
@[simps!]
def mulMarked {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    RealLorentzTensor d (X ⊕ Y) where
  color := Sum.elim T.unmarkedColor S.unmarkedColor
  coord := fun i => ∑ x,
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1, oneMarkedIndexValue x)) *
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2,
      oneMarkedIndexValue $ colorsIndexDualCast h x))

/-- The index value appearing in the multiplication of Marked tensors on the left. -/
def mulMarkedFstArg {X Y : Type} {T : Marked d X 1} {S : Marked d Y 1}
    (i : IndexValue d (Sum.elim T.unmarkedColor S.unmarkedColor))
    (x : ColorsIndex d (T.color (markedPoint X 0))) : IndexValue d T.color :=
  splitIndexValue.symm ((indexValueSumEquiv i).1, oneMarkedIndexValue x)

lemma mulMarkedFstArg_inr {X Y : Type} {T : Marked d X 1} {S : Marked d Y 1}
    (i : IndexValue d (Sum.elim T.unmarkedColor S.unmarkedColor))
    (x : ColorsIndex d (T.color (markedPoint X 0))) :
    mulMarkedFstArg i x (Sum.inr 0) = x := by
  rfl

lemma mulMarkedFstArg_inl {X Y : Type} {T : Marked d X 1} {S : Marked d Y 1}
    (i : IndexValue d (Sum.elim T.unmarkedColor S.unmarkedColor))
    (x : ColorsIndex d (T.color (markedPoint X 0))) (c : X):
    mulMarkedFstArg i x (Sum.inl c) = i (Sum.inl c) := by
  rfl

/-- The index value appearing in the multiplication of Marked tensors on the right. -/
def mulMarkedSndArg {X Y : Type} {T : Marked d X 1} {S : Marked d Y 1}
    (i : IndexValue d (Sum.elim T.unmarkedColor S.unmarkedColor))
    (x : ColorsIndex d (T.color (markedPoint X 0))) (h : T.markedColor 0 = τ (S.markedColor 0)) :
    IndexValue d S.color :=
  splitIndexValue.symm ((indexValueSumEquiv i).2, oneMarkedIndexValue $ colorsIndexDualCast h x)

/-!

## Expressions for multiplication

-/
/-! TODO: Where appropriate write these expresions in terms of `indexValueDualIso`. -/
lemma mulMarked_colorsIndex_right {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    (mulMarked T S h).coord = fun i => ∑ x,
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1,
    oneMarkedIndexValue $ colorsIndexDualCast (color_eq_dual_symm h) x)) *
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, oneMarkedIndexValue x)) := by
  funext i
  rw [← Equiv.sum_comp (colorsIndexDualCast h)]
  apply Finset.sum_congr rfl (fun x _ => ?_)
  congr
  rw [← colorsIndexDualCast_symm]
  exact (Equiv.apply_eq_iff_eq_symm_apply (colorsIndexDualCast h)).mp rfl

lemma mulMarked_indexValue_left {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    (mulMarked T S h).coord = fun i => ∑ j,
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1, j)) *
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2,
    (oneMarkedIndexValue $ (colorsIndexDualCast h) $ oneMarkedIndexValue.symm j))) := by
  funext i
  rw [← Equiv.sum_comp (oneMarkedIndexValue)]
  rfl

lemma mulMarked_indexValue_right {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    (mulMarked T S h).coord = fun i => ∑ j,
    T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1,
    oneMarkedIndexValue $ (colorsIndexDualCast h).symm $ oneMarkedIndexValue.symm j)) *
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, j)) := by
  funext i
  rw [mulMarked_colorsIndex_right]
  rw [← Equiv.sum_comp (oneMarkedIndexValue)]
  apply Finset.sum_congr rfl (fun x _ => ?_)
  congr
  exact Eq.symm (colorsIndexDualCast_symm h)

/-!

## Properties of multiplication

-/

/-- Multiplication is well behaved with regard to swapping tensors. -/
lemma mulMarked_symm {X Y : Type} (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 0)) :
    mapIso d (Equiv.sumComm X Y) (mulMarked T S h) = mulMarked S T (color_eq_dual_symm h) := by
  refine ext ?_ ?_
  · funext a
    cases a with
    | inl _ => rfl
    | inr _ => rfl
  · funext i
    rw [mulMarked_colorsIndex_right]
    refine Fintype.sum_congr _ _ (fun x => ?_)
    rw [mul_comm]
    rfl

/-- Multiplication commutes with `mapIso`. -/
lemma mulMarked_mapIso {X Y Z : Type} (T : Marked d X 1) (S : Marked d Y 1) (f : X ≃ W)
    (g : Y ≃ Z) (h : T.markedColor 0 = τ (S.markedColor 0)) :
    mapIso d (Equiv.sumCongr f g) (mulMarked T S h) = mulMarked (mapIso d (Equiv.sumCongr f (Equiv.refl _)) T)
    (mapIso d (Equiv.sumCongr g (Equiv.refl _)) S) h := by
  refine ext ?_ ?_
  · funext a
    cases a with
    | inl _ => rfl
    | inr _ => rfl
  · funext i
    rw [mapIso_apply_coord, mapIsoFiber_apply, mapIsoFiber_apply, mulMarked_coord, mulMarked_coord]
    refine Fintype.sum_congr _ _ (fun x => ?_)
    rw [mapIso_apply_coord, mapIso_apply_coord]
    refine Mathlib.Tactic.Ring.mul_congr ?_ ?_ rfl
    · apply congrArg
      exact (Equiv.symm_apply_eq splitIndexValue).mpr rfl
    · apply congrArg
      exact (Equiv.symm_apply_eq splitIndexValue).mpr rfl

/-!

## Lorentz action and multiplication.

-/

/-- The marked Lorentz Action leaves multiplication invariant. -/
lemma mulMarked_markedLorentzAction (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 1)) :
    mulMarked (Λ •ₘ T) (Λ •ₘ S) h = mulMarked T S h := by
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
  rw [Finset.sum_mul_sum]
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
  trans ∑ k, T.coord (splitIndexValue.symm ((indexValueSumEquiv i).1,
    (oneMarkedIndexValue $ (colorsIndexDualCast h).symm $ oneMarkedIndexValue.symm k)))*
    S.coord (splitIndexValue.symm ((indexValueSumEquiv i).2, k))
  apply Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_mul, ← toTensorRepMat_one_coord_sum T]
  rw [← Equiv.sum_comp (oneMarkedIndexValue)]
  erw [← Equiv.sum_comp (colorsIndexDualCast h)]
  simp
  rfl

/-- The unmarked Lorentz Action commutes with multiplication. -/
lemma mulMarked_unmarkedLorentzAction (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 1)) :
    mulMarked (Λ •ᵤₘ T) (Λ •ᵤₘ S) h = Λ • mulMarked T S h := by
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
  · apply Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul_sum ]
    apply Finset.sum_congr rfl (fun j _ => ?_)
    apply Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [Finset.sum_comm]
  trans ∑ j, ∑ k, ∑ x, (toTensorRepMat Λ (indexValueSumEquiv i).1 j *
      T.coord (splitIndexValue.symm (j, oneMarkedIndexValue x)))*
      toTensorRepMat Λ (indexValueSumEquiv i).2 k *
      S.coord (splitIndexValue.symm (k, oneMarkedIndexValue $ colorsIndexDualCast h x))
  · exact Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
  trans ∑ j, ∑ k,
    ((toTensorRepMat Λ (indexValueSumEquiv i).1 j) * toTensorRepMat Λ (indexValueSumEquiv i).2 k)
    * ∑ x, (T.coord (splitIndexValue.symm (j, oneMarkedIndexValue x)))
    * S.coord (splitIndexValue.symm (k, oneMarkedIndexValue $ colorsIndexDualCast h x))
  · apply Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl (fun x _ => ?_)
    ring
  trans ∑ j, ∑ k, toTensorRepMat Λ i (indexValueSumEquiv.symm (j, k)) *
    ∑ x, (T.coord (splitIndexValue.symm (j, oneMarkedIndexValue x)))
      * S.coord (splitIndexValue.symm (k, oneMarkedIndexValue $ colorsIndexDualCast h x))
  apply Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  · rw [toTensorRepMat_of_indexValueSumEquiv']
    congr
    simp only [IndexValue, Finset.mem_univ, Prod.mk.eta, Equiv.symm_apply_apply, mulMarked_color]
  trans ∑ p, toTensorRepMat Λ i p *
    ∑ x, (T.coord (splitIndexValue.symm ((indexValueSumEquiv p).1, oneMarkedIndexValue x)))
    * S.coord (splitIndexValue.symm ((indexValueSumEquiv p).2,
      oneMarkedIndexValue $ colorsIndexDualCast h x))
  · erw [← Equiv.sum_comp indexValueSumEquiv.symm]
    exact Eq.symm Fintype.sum_prod_type
  rfl

/-- The Lorentz action commutes with multiplication. -/
lemma mulMarked_lorentzAction (T : Marked d X 1) (S : Marked d Y 1)
    (h : T.markedColor 0 = τ (S.markedColor 1)) :
    mulMarked (Λ • T) (Λ • S) h = Λ • mulMarked T S h := by
  simp only [← marked_unmarked_action_eq_action]
  rw [mulMarked_markedLorentzAction, mulMarked_unmarkedLorentzAction]

/-!

## Multiplication on selected indices

-/

variable {n m : ℕ} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  {X' Y' Z : Type} [Fintype X'] [DecidableEq X'] [Fintype Y'] [DecidableEq Y']
  [Fintype Z] [DecidableEq Z]

/-- The multiplication of two real Lorentz Tensors along specified indices. -/
@[simps!]
def mult (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y) (x : X) (y : Y)
    (h : T.color x = τ (S.color y)) : RealLorentzTensor d ({x' // x' ≠ x} ⊕ {y' // y' ≠ y}) :=
  mulMarked (markSingle x T) (markSingle y S) h

/-- The first index value appearing in the multiplication of two Lorentz tensors. -/
def multFstArg {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0))) :
    IndexValue d T.color := (markSingleIndexValue T x).symm (mulMarkedFstArg i a)

lemma multFstArg_ext {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    {i j : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor)}
    {a b : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0))}
    (hij : i = j) (hab : a = b) : multFstArg i a = multFstArg j b := by
  subst hij; subst hab
  rfl

lemma multFstArg_on_mem {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0))) :
    multFstArg i a x = a := by
  rw [multFstArg, markSingleIndexValue]
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

lemma multFstArg_on_not_mem {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0)))
    (c : X) (hc : c ≠ x) : multFstArg i a c = i (Sum.inl ⟨c, hc⟩) := by
  rw [multFstArg, markSingleIndexValue]
  simp only [ne_eq, Fintype.univ_ofSubsingleton, Fin.zero_eta, Fin.isValue, Equiv.symm_trans_apply,
     Sum.map_inr, id_eq]
  erw [markEmbeddingIndexValue_apply_symm_on_not_mem]
  swap
  simpa using hc
  rfl

/-- The second index value appearing in the multiplication of two Lorentz tensors. -/
def multSndArg {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0)))
    (h : T.color x = τ (S.color y)) : IndexValue d S.color :=
  (markSingleIndexValue S y).symm (mulMarkedSndArg i a h)

lemma multSndArg_on_mem {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0)))
    (h : T.color x = τ (S.color y)) : multSndArg i a h y = colorsIndexDualCast h a := by
  rw [multSndArg, markSingleIndexValue]
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

lemma multSndArg_on_not_mem {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor))
    (a : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0)))
    (h : T.color x = τ (S.color y)) (c : Y) (hc : c ≠ y) :
    multSndArg i a h c = i (Sum.inr ⟨c, hc⟩) := by
  rw [multSndArg, markSingleIndexValue]
  simp only [ne_eq, Fintype.univ_ofSubsingleton, Fin.zero_eta, Fin.isValue, Equiv.symm_trans_apply,
     Sum.map_inr, id_eq]
  erw [markEmbeddingIndexValue_apply_symm_on_not_mem]
  swap
  simpa using hc
  rfl

lemma multSndArg_ext {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y} {x : X} {y : Y}
    {i j : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor)}
    {a b : ColorsIndex d ((markSingle x T).color (markedPoint {x' // x' ≠ x} 0))}
    (h : T.color x = τ (S.color y)) (hij : i = j) (hab : a = b) :
    multSndArg i a h = multSndArg j b h := by
  subst hij
  subst hab
  rfl

lemma mult_coord_arg (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y) (x : X) (y : Y)
    (h : T.color x = τ (S.color y))
    (i : IndexValue d (Sum.elim (markSingle x T).unmarkedColor (markSingle y S).unmarkedColor)) :
  (mult T S x y h).coord i = ∑ a, T.coord (multFstArg i a) * S.coord (multSndArg i a h) := by
  rfl

lemma mult_mapIso (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y)
    (eX : X ≃ X') (eY : Y ≃ Y') (x : X) (y : Y) (x' : X') (y' : Y') (hx : eX x = x')
    (hy : eY y = y') (h : T.color x = τ (S.color y)) :
    mult (mapIso d eX T) (mapIso d eY S) x' y' (by subst hx hy; simpa using h) =
    mapIso d (Equiv.sumCongr (equivSingleCompl eX hx) (equivSingleCompl eY hy))
      (mult T S x y h) := by
  rw [mult, mult, mulMarked_mapIso]
  congr 1 <;> rw [markSingle_mapIso]

lemma mult_lorentzAction (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y)
    (x : X) (y : Y) (h : T.color x = τ (S.color y)) (Λ : LorentzGroup d) :
    mult (Λ • T) (Λ • S) x y h = Λ • mult T S x y h := by
  rw [mult, mult, ← mulMarked_lorentzAction]
  congr 1
  all_goals
    rw [markSingle, markEmbedding, Equiv.trans_apply]
    erw [lorentzAction_mapIso, lorentzAction_mapIso]
    rfl

lemma mult_symm (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y)
    (x : X) (y : Y) (h : T.color x = τ (S.color y)) :
    mapIso d (Equiv.sumComm _ _) (mult T S x y h) = mult S T y x (color_eq_dual_symm h) := by
  rw [mult, mult, mulMarked_symm]

/-- An equivalence of types associated with multiplying two consecutive indices,
with the second index appearing on the left. -/
def multSplitLeft {y y' : Y} (hy : y ≠ y') (z : Z) :
    {yz // yz ≠ (Sum.inl ⟨y, hy⟩ : {y'' // y'' ≠ y'} ⊕ {z' // z' ≠ z})} ≃
    {y'' // y'' ≠ y' ∧ y'' ≠ y} ⊕ {z' // z' ≠ z} :=
  Equiv.subtypeSum.trans <|
  Equiv.sumCongr (
      (Equiv.subtypeEquivRight (fun a => by
        obtain ⟨a, p⟩ := a; simp only [ne_eq, Sum.inl.injEq, Subtype.mk.injEq])).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _)) <|
  Equiv.subtypeUnivEquiv (fun a => Sum.inr_ne_inl)

/-- An equivalence of types associated with multiplying two consecutive indices with the
second index appearing on the right. -/
def multSplitRight {y y' : Y} (hy : y ≠ y') (z : Z) :
    {yz // yz ≠ (Sum.inr ⟨y', hy.symm⟩ : {z' // z' ≠ z} ⊕ {y'' // y'' ≠ y})} ≃
    {z' // z' ≠ z} ⊕ {y'' // y'' ≠ y' ∧ y'' ≠ y} :=
   Equiv.subtypeSum.trans <|
  Equiv.sumCongr (Equiv.subtypeUnivEquiv (fun a => Sum.inl_ne_inr)) <|
  (Equiv.subtypeEquivRight (fun a => by
    obtain ⟨a, p⟩ := a; simp only [ne_eq, Sum.inr.injEq, Subtype.mk.injEq])).trans <|
  ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
    (Equiv.subtypeEquivRight (fun y'' => And.comm)))

/-- An equivalence of types associated with the associativity property of multiplication. -/
def multAssocIso (x : X) {y y' : Y} (hy : y ≠ y') (z : Z) :
    {x' // x' ≠ x} ⊕ {yz // yz ≠ (Sum.inl ⟨y, hy⟩ : {y'' // y'' ≠ y'} ⊕ {z' // z' ≠ z})}
    ≃ {xy // xy ≠ (Sum.inr ⟨y', hy.symm⟩ : {x' // x' ≠ x} ⊕ {y'' // y'' ≠ y})} ⊕ {z' // z' ≠ z} :=
  (Equiv.sumCongr (Equiv.refl _) (multSplitLeft hy z)).trans <|
  (Equiv.sumAssoc _ _ _).symm.trans <|
  (Equiv.sumCongr (multSplitRight hy x).symm (Equiv.refl _))

lemma mult_assoc_color {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y}
    {U : RealLorentzTensor d Z} {x : X} {y y' : Y} (hy : y ≠ y') {z : Z}
    (h : T.color x = τ (S.color y))
    (h' : S.color y' = τ (U.color z)) : (mult (mult T S x y h) U (Sum.inr ⟨y', hy.symm⟩) z h').color
    = (mapIso d (multAssocIso x hy z) (mult T (mult S U y' z h') x (Sum.inl ⟨y, hy⟩) h)).color := by
  funext a
  match a with
  | .inl ⟨.inl _, _⟩ => rfl
  | .inl ⟨.inr _, _⟩ => rfl
  | .inr _ => rfl

/-- An equivalence of index values associated with the associativity property of multiplication. -/
def multAssocIndexValue {T : RealLorentzTensor d X} {S : RealLorentzTensor d Y}
    {U : RealLorentzTensor d Z} {x : X} {y y' : Y} (hy : y ≠ y') {z : Z}
    (h : T.color x = τ (S.color y)) (h' : S.color y' = τ (U.color z)) :
    IndexValue d ((T.mult S x y h).mult U (Sum.inr ⟨y', hy.symm⟩) z h').color ≃
    IndexValue d (T.mult (S.mult U y' z h') x (Sum.inl ⟨y, hy⟩) h).color :=
  indexValueIso d (multAssocIso x hy z).symm (mult_assoc_color hy h h')

/-- Multiplication of indices is associative, up to a `mapIso` equivalence. -/
lemma mult_assoc (T : RealLorentzTensor d X) (S : RealLorentzTensor d Y) (U : RealLorentzTensor d Z)
    (x : X) (y y' : Y) (hy : y ≠ y') (z : Z) (h : T.color x = τ (S.color y))
    (h' : S.color y' = τ (U.color z)) : mult (mult T S x y h) U (Sum.inr ⟨y', hy.symm⟩) z h' =
    mapIso d (multAssocIso x hy z) (mult T (mult S U y' z h') x (Sum.inl ⟨y, hy⟩) h) := by
  apply ext (mult_assoc_color _ _ _) ?_
  funext i
  trans ∑ a, (∑ b, T.coord (multFstArg (multFstArg i a) b) *
    S.coord (multSndArg (multFstArg i a) b h)) * U.coord (multSndArg i a h')
  rfl
  trans ∑ a, T.coord (multFstArg (multAssocIndexValue hy h h' i) a) *
    (∑ b, S.coord (multFstArg (multSndArg (multAssocIndexValue hy h h' i) a h) b) *
    U.coord (multSndArg (multSndArg (multAssocIndexValue hy h h' i) a h) b h'))
  swap
  rw [mapIso_apply_coord, mapIsoFiber_apply, mapIsoFiber_apply, mult_coord_arg, indexValueIso_symm]
  rfl
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_mul _ _ _)]
  rw [Finset.sum_congr rfl (fun x _ => Finset.mul_sum _ _ _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [mul_assoc]
  refine Mathlib.Tactic.Ring.mul_congr rfl (Mathlib.Tactic.Ring.mul_congr ?_ rfl rfl) rfl
  apply congrArg
  funext c
  by_cases hcy : c = y
  · subst hcy
    rw [multSndArg_on_mem, multFstArg_on_not_mem, multSndArg_on_mem]
    rfl
  · by_cases hcy' : c = y'
    · subst hcy'
      rw [multFstArg_on_mem, multSndArg_on_not_mem, multFstArg_on_mem]
    · rw [multFstArg_on_not_mem, multSndArg_on_not_mem, multSndArg_on_not_mem,
        multFstArg_on_not_mem]
      rw [multAssocIndexValue, indexValueIso_eq_symm, indexValueIso_symm_apply']
      simp only [ne_eq, Function.comp_apply, Equiv.symm_symm_apply, mult_color, Sum.elim_inr,
        colorsIndexCast, Equiv.cast_refl, Equiv.refl_symm]
      erw [Equiv.refl_apply]
      rfl
      exact hcy'
      simpa using hcy

end RealLorentzTensor
