/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.ComplexLorentz.Basis
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

namespace complexLorentzTensor
open Fermion
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

end complexLorentzTensor

end
