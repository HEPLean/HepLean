/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.ComplexLorentz.BasisTrees
/-!

## Lemmas related to complex Lorentz tensors.

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open TensorTree
open OverColor.Discrete
noncomputable section

namespace Fermion
open complexLorentzTensor
set_option maxRecDepth 20000 in
lemma contr_rank_2_symm {T1 : (Lorentz.complexContr ⊗ Lorentz.complexContr).V}
    {T2 : (Lorentz.complexCo ⊗ Lorentz.complexCo).V} :
    {T1 | μ ν ⊗ T2 | μ ν = T2 | μ ν ⊗ T1 | μ ν}ᵀ := by
  rw [perm_tensor_eq (contr_tensor_eq (contr_tensor_eq (prod_comm _ _ _ _)))]
  rw [perm_tensor_eq (contr_tensor_eq (perm_contr _ _))]
  rw [perm_tensor_eq (perm_contr _ _)]
  rw [perm_perm]
  rw [perm_eq_id]
  · rw [(contr_tensor_eq (contr_swap _ _))]
    rw [perm_contr]
    rw [perm_tensor_eq (contr_swap _ _)]
    rw [perm_perm]
    rw [perm_eq_id]
    · rfl
    · rfl
  · apply OverColor.Hom.ext
    ext x
    exact Fin.elim0 x

lemma contr_rank_2_symm' {T1 : (Lorentz.complexCo ⊗ Lorentz.complexCo).V}
    {T2 : (Lorentz.complexContr ⊗ Lorentz.complexContr).V} :
    {T1 | μ ν ⊗ T2 | μ ν = T2 | μ ν ⊗ T1 | μ ν}ᵀ := by
  rw [perm_tensor_eq contr_rank_2_symm]
  rw [perm_perm]
  rw [perm_eq_id]
  apply OverColor.Hom.ext
  ext x
  exact Fin.elim0 x

set_option maxRecDepth 20000 in
/-- Contracting a rank-2 anti-symmetric tensor with a rank-2 symmetric tensor gives zero. -/
lemma antiSymm_contr_symm {A : (Lorentz.complexContr ⊗ Lorentz.complexContr).V}
    {S : (Lorentz.complexCo ⊗ Lorentz.complexCo).V}
    (hA : {A | μ ν = - (A | ν μ)}ᵀ) (hs : {S | μ ν = S | ν μ}ᵀ) :
    {A | μ ν ⊗ S | μ ν}ᵀ.tensor = 0 := by
  have h1 {M : Type} [AddCommGroup M] [Module ℂ M] {x : M} (h : x = - x) : x = 0 := by
    rw [eq_neg_iff_add_eq_zero, ← two_smul ℂ x] at h
    simpa using h
  refine h1 ?_
  rw [← neg_tensor]
  rw [neg_perm] at hA
  nth_rewrite 1 [contr_tensor_eq (contr_tensor_eq (prod_tensor_eq_fst hA))]
  nth_rewrite 1 [(contr_tensor_eq (contr_tensor_eq (prod_tensor_eq_snd hs)))]
  rw [contr_tensor_eq (contr_tensor_eq (neg_fst_prod _ _))]
  rw [contr_tensor_eq (neg_contr _)]
  rw [neg_contr]
  rw [neg_tensor]
  apply congrArg
  rw [contr_tensor_eq (contr_tensor_eq (prod_perm_left _ _ _ _))]
  rw [contr_tensor_eq (perm_contr _ _)]
  rw [perm_contr]
  rw [perm_tensor_eq (contr_tensor_eq (contr_tensor_eq (prod_perm_right _ _ _ _)))]
  rw [perm_tensor_eq (contr_tensor_eq (perm_contr _ _))]
  rw [perm_tensor_eq (perm_contr _ _)]
  rw [perm_perm]
  nth_rewrite 1 [perm_tensor_eq (contr_contr _ _ _)]
  rw [perm_perm]
  rw [perm_eq_id]
  · rfl
  · rfl

lemma symm_contr_antiSymm {S : (Lorentz.complexCo ⊗ Lorentz.complexCo).V}
    {A : (Lorentz.complexContr ⊗ Lorentz.complexContr).V}
    (hA : {A | μ ν = - (A | ν μ)}ᵀ) (hs : {S | μ ν = S | ν μ}ᵀ) :
    {S | μ ν ⊗ A | μ ν}ᵀ.tensor = 0 := by
  rw [contr_rank_2_symm', perm_tensor, antiSymm_contr_symm hA hs]
  rfl

lemma antiSymm_add_self {A : (Lorentz.complexContr ⊗ Lorentz.complexContr).V}
    (hA : {A | μ ν = - (A | ν μ)}ᵀ) :
    {A | μ ν + A | ν μ}ᵀ.tensor = 0 := by
  rw [← TensorTree.add_neg (twoNodeE complexLorentzTensor Color.up Color.up A)]
  apply TensorTree.add_tensor_eq_snd
  rw [neg_tensor_eq hA, neg_tensor_eq (neg_perm _ _), neg_neg]

/-!

## The contraction of Pauli matrices with Pauli matrices

And related results.

-/

/-- The map to color one gets when multiplying left and right metrics. -/
def leftMetricMulRightMap := (Sum.elim ![Color.upL, Color.upL] ![Color.upR, Color.upR]) ∘
  finSumFinEquiv.symm

lemma leftMetric_mul_rightMetric : {Fermion.leftMetric | α α' ⊗ Fermion.rightMetric | β β'}ᵀ.tensor
    = basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    - basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    - basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0) := by
  rw [prod_tensor_eq_fst (leftMetric_expand_tree)]
  rw [prod_tensor_eq_snd (rightMetric_expand_tree)]
  rw [prod_add_both]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_tensor_eq <| prod_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_eq_one _ _ (by simp)]
  rw [add_tensor_eq_fst <| add_tensor_eq_snd <| smul_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| prod_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_snd <| smul_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| prod_basisVector_tree _ _]
  rw [← add_assoc]
  simp only [add_tensor, smul_tensor, tensorNode_tensor]
  change _ = basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    +- basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    +- basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0)
  congr 1
  congr 1
  congr 1
  all_goals
    congr
    funext x
    fin_cases x <;> rfl

lemma leftMetric_mul_rightMetric_tree :
    {Fermion.leftMetric | α α' ⊗ Fermion.rightMetric | β β'}ᵀ.tensor
    = (TensorTree.add (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1))) <|
      TensorTree.add (TensorTree.smul (-1 : ℂ) (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)))) <|
      TensorTree.add (TensorTree.smul (-1 : ℂ) (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)))) <|
      (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0)))).tensor := by
  rw [leftMetric_mul_rightMetric]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, add_tensor, tensorNode_tensor,
    smul_tensor, neg_smul, one_smul]
  rfl

end Fermion

end
