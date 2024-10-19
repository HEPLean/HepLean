/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

## Basic node identities

This file contains the basic node identities for tensor trees.
More compliciated identities appear in there own files.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin
open TensorProduct

namespace TensorTree

variable {S : TensorStruct}

/-!

## Equality of constructors.

-/

informal_lemma constVecNode_eq_vecNode where
  math :≈ "A constVecNode has equal tensor to the vecNode with the map evaluated at 1."
  deps :≈ [``constVecNode, ``vecNode]

informal_lemma constTwoNode_eq_twoNode where
  math :≈ "A constTwoNode has equal tensor to the twoNode with the map evaluated at 1."
  deps :≈ [``constTwoNode, ``twoNode]

informal_lemma constThreeNode_eq_threeNode where
  math :≈ "A constThreeNode has equal tensor to the threeNode with the map evaluated at 1."
  deps :≈ [``constThreeNode, ``threeNode]

/-!

## Negation

-/

@[simp]
lemma neg_neg (t : TensorTree S c) : (neg (neg t)).tensor = t.tensor := by
  simp only [neg_tensor, _root_.neg_neg]

@[simp]
lemma neg_fst_prod  {c1 : Fin n → S.C} {c2 : Fin m → S.C} (T1 : TensorTree S c1)
    (T2 : TensorTree S c2) :
    (prod (neg T1) T2).tensor = (neg (prod T1 T2)).tensor := by
  simp only [prod_tensor, Functor.id_obj, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, neg_tensor, neg_tmul, map_neg]

@[simp]
lemma neg_snd_prod  {c1 : Fin n → S.C} {c2 : Fin m → S.C} (T1 : TensorTree S c1)
    (T2 : TensorTree S c2) :
    (prod T1 (neg T2)).tensor = (neg (prod T1 T2)).tensor := by
  simp only [prod_tensor, Functor.id_obj, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, neg_tensor, tmul_neg, map_neg]

@[simp]
lemma neg_contr {n : ℕ} {c : Fin n.succ.succ → S.C} {i : Fin n.succ.succ} {j : Fin n.succ} {h : c (i.succAbove j) = S.τ (c i)}
    (t : TensorTree S c) : (contr i j h (neg t)).tensor = (neg (contr i j h t)).tensor := by
  simp only [Nat.succ_eq_add_one, contr_tensor, neg_tensor, map_neg]

lemma neg_perm {n m : ℕ} {c : Fin n → S.C} {c1 : Fin m → S.C}
    (σ : (OverColor.mk c) ⟶ (OverColor.mk c1)) (t : TensorTree S c) :
    (perm σ (neg t)).tensor = (neg (perm σ t)).tensor := by
  simp only [perm_tensor, neg_tensor, map_neg]

end TensorTree
