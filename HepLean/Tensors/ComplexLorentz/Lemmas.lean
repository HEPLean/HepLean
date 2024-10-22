/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.ComplexLorentz.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HepLean.Tensors.Tree.NodeIdentities.Basic
import HepLean.Tensors.Tree.NodeIdentities.PermProd
import HepLean.Tensors.Tree.NodeIdentities.PermContr
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.ContrContr
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

example : 0 < complexLorentzTensor.repDim (![Color.down] 0):= by decide


lemma coMetric_expand : {Lorentz.coMetric | μ ν}ᵀ.tensor =
    (PiTensorProduct.tprod ℂ (fun i => Fin.cases (Lorentz.complexCoBasis (Sum.inl 0))
        (fun i => Fin.cases (Lorentz.complexCoBasis (Sum.inl 0)) (fun i => i.elim0) i) i) :
        complexLorentzTensor.F.obj (OverColor.mk ![Color.down, Color.down]))
    - (PiTensorProduct.tprod ℂ (fun i => Fin.cases (Lorentz.complexCoBasis (Sum.inr 0))
        (fun i => Fin.cases (Lorentz.complexCoBasis (Sum.inr 0)) (fun i => i.elim0) i) i) :
        complexLorentzTensor.F.obj (OverColor.mk ![Color.down, Color.down]))
    - (PiTensorProduct.tprod ℂ (fun i => Fin.cases (Lorentz.complexCoBasis (Sum.inr 1))
        (fun i => Fin.cases (Lorentz.complexCoBasis (Sum.inr 1)) (fun i => i.elim0) i) i) :
        complexLorentzTensor.F.obj (OverColor.mk ![Color.down, Color.down]))
    - (PiTensorProduct.tprod ℂ (fun i => Fin.cases (Lorentz.complexCoBasis (Sum.inr 2))
        (fun i => Fin.cases (Lorentz.complexCoBasis (Sum.inr 2)) (fun i => i.elim0) i) i) :
        complexLorentzTensor.F.obj (OverColor.mk ![Color.down, Color.down])) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Functor.id_obj, Fin.isValue]
  erw [Lorentz.coMetric_apply_one, Lorentz.coMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul]
    rfl

/-- The covariant Lorentz metric is symmetric. -/
lemma coMetric_symm : {Lorentz.coMetric | μ ν = Lorentz.coMetric | ν μ}ᵀ := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, perm_tensor]
  rw [coMetric_expand]
  simp only [TensorSpecies.F, Nat.succ_eq_add_one, Nat.reduceAdd, Functor.id_obj, Fin.isValue,
    map_sub]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [OverColor.lift.map_tprod]
    apply congrArg
    funext i
    match i with
    | (0 : Fin 2) => rfl
    | (1 : Fin 2) => rfl

set_option maxRecDepth 20000 in
lemma contr_rank_2_symm {T1 : (Lorentz.complexContr ⊗ Lorentz.complexContr).V}
    {T2 : (Lorentz.complexCo ⊗ Lorentz.complexCo).V} :
    {(T1 | μ ν ⊗ T2 | μ ν) = (T2 | μ ν ⊗ T1 | μ ν)}ᵀ := by
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
    · apply OverColor.Hom.ext
      rfl
  · apply OverColor.Hom.ext
    ext x
    exact Fin.elim0 x

lemma contr_rank_2_symm' {T1 : (Lorentz.complexCo ⊗ Lorentz.complexCo).V}
    {T2 : (Lorentz.complexContr ⊗ Lorentz.complexContr).V} :
    {(T1 | μ ν ⊗ T2 | μ ν) = (T2 | μ ν ⊗ T1 | μ ν)}ᵀ := by
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
  rw [contr_rank_2_symm']
  rw [perm_tensor]
  rw [antiSymm_contr_symm hA hs]
  rfl

variable (p : Lorentz.complexCo) (q : Lorentz.complexContr)

lemma contr_rank_1_expand (p : Lorentz.complexCo) (q : Lorentz.complexContr) :
    {p | μ ⊗ q | μ = p | 0}ᵀ := by
  sorry

end Fermion

end
