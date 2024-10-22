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
import LLMLean
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


def coCoBasis (b : Fin 4 × Fin 4) :
    complexLorentzTensor.F.obj (OverColor.mk ![Color.down, Color.down]) :=
  PiTensorProduct.tprod ℂ (fun i => Fin.cases (Lorentz.complexCoBasisFin4 b.1)
  (fun i => Fin.cases (Lorentz.complexCoBasisFin4 b.2) (fun i => i.elim0) i) i)


lemma coCoBasis_eval (e1 e2 : Fin (complexLorentzTensor.repDim Color.down)) (i : Fin 4 × Fin 4) :
    complexLorentzTensor.castFin0ToField
      ((complexLorentzTensor.evalMap 0 e2) ((complexLorentzTensor.evalMap 0 e1) (coCoBasis i))) =
    if i = (e1, e2) then 1 else 0 := by
  simp only [coCoBasis]
  have h1 := @TensorSpecies.evalMap_tprod complexLorentzTensor _ (![Color.down, Color.down]) 0 e1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Functor.id_obj,
      OverColor.mk_hom, Function.comp_apply, cons_val_zero, Fin.cases_zero,  Fin.cases_succ] at h1
  erw [h1]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Functor.id_obj, OverColor.mk_hom,
    Fin.cases_zero, Fin.cases_succ, _root_.map_smul, smul_eq_mul]
  erw [TensorSpecies.evalMap_tprod]
  simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.succAbove_zero, Functor.id_obj,
    OverColor.mk_hom, Function.comp_apply, Fin.succ_zero_eq_one, cons_val_one, head_cons,
    Fin.cases_zero, Fin.zero_succAbove, Fin.cases_succ, _root_.map_smul, smul_eq_mul]
  erw [complexLorentzTensor.castFin0ToField_tprod]
  simp only [Fin.isValue, mul_one]
  change (Lorentz.complexCoBasisFin4.repr (Lorentz.complexCoBasisFin4 i.1)) e1 *
    (Lorentz.complexCoBasisFin4.repr (Lorentz.complexCoBasisFin4 i.2)) e2  = _
  simp only [Basis.repr_self]
  rw [Finsupp.single_apply, Finsupp.single_apply]
  rw [@ite_zero_mul_ite_zero]
  simp
  congr
  simp_all only [Fin.isValue, Fin.succAbove_zero, Fin.zero_succAbove, eq_iff_iff]
  obtain ⟨fst, snd⟩ := i
  simp_all only [Fin.isValue, Prod.mk.injEq]

lemma coMetric_expand : {Lorentz.coMetric | μ ν}ᵀ.tensor =
    coCoBasis (0, 0)
    - coCoBasis (1, 1)
    - coCoBasis (2, 2)
    - coCoBasis (3, 3):= by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Functor.id_obj, Fin.isValue]
  erw [Lorentz.coMetric_apply_one, Lorentz.coMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul, coCoBasis]
    simp only [Nat.reduceAdd, Nat.succ_eq_add_one, OverColor.mk_hom, Functor.id_obj, Fin.isValue,
      Lorentz.complexCoBasisFin4, Basis.coe_reindex, Function.comp_apply]
    rfl

/-- The covariant Lorentz metric is symmetric. -/
lemma coMetric_symm : {Lorentz.coMetric | μ ν = Lorentz.coMetric | ν μ}ᵀ := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, perm_tensor]
  rw [coMetric_expand]
  simp only [TensorSpecies.F, Nat.succ_eq_add_one, Nat.reduceAdd, Functor.id_obj, Fin.isValue,
    map_sub]
  simp only [coCoBasis, Nat.reduceAdd, Nat.succ_eq_add_one, OverColor.mk_hom, Functor.id_obj, Fin.isValue,
      Lorentz.complexCoBasisFin4, Basis.coe_reindex, Function.comp_apply]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [OverColor.lift.map_tprod]
    congr 1
    funext i
    match i with
    | (0 : Fin 2) => rfl
    | (1 : Fin 2) => rfl

lemma coMetric_0_0_field : {Lorentz.coMetric | 0 0}ᵀ.field  = 1 := by
  rw [field, eval_tensor, eval_tensor, coMetric_expand]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
    Function.comp_apply, Fin.succ_zero_eq_one, cons_val_one, head_cons, Fin.ofNat'_zero,
    cons_val_zero, Functor.id_obj, OverColor.mk_hom, map_sub]
  rw [coCoBasis_eval, coCoBasis_eval, coCoBasis_eval, coCoBasis_eval]
  simp only [Fin.isValue, Prod.mk_zero_zero, ↓reduceIte, Prod.mk_one_one, one_ne_zero, sub_zero,
    Prod.mk_eq_zero, Fin.reduceEq, and_self]

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

end Fermion

end
