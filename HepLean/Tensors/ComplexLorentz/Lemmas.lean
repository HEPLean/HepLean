/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.ComplexLorentz.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
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

lemma coMetric_symm : {Lorentz.coMetric | μ ν = Lorentz.coMetric | ν μ}ᵀ := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, perm_tensor]
  rw [coMetric_expand]
  simp only [TensorStruct.F, Nat.succ_eq_add_one, Nat.reduceAdd, Functor.id_obj, Fin.isValue,
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

/-
lemma coMetric_prod_antiSymm (A : (Lorentz.complexContr ⊗ Lorentz.complexContr).V)
    (S : (Lorentz.complexCo ⊗ Lorentz.complexCo).V)
    (hA : (twoNodeE complexLorentzTensor Color.up Color.up A).tensor =
      (TensorTree.neg (perm
      (OverColor.equivToHomEq (Equality.finMapToEquiv ![1, 0] ![1, 0]) (by decide))
      (twoNodeE complexLorentzTensor  Color.up  Color.up A))).tensor)
    (hs : {S | μ ν = S | ν μ}ᵀ) : {A | μ ν ⊗ S | μ ν}ᵀ.tensor = 0 := by
  have h1 : {A | μ ν ⊗ S | μ ν}ᵀ.tensor = - {A | μ ν ⊗ S | μ ν}ᵀ.tensor := by
    nth_rewrite 1 [contr_tensor_eq (contr_tensor_eq (prod_tensor_eq_fst hA))]
    rw [contr_tensor_eq (contr_tensor_eq (neg_fst_prod _ _))]
    rw [contr_tensor_eq (neg_contr _)]
    rw [neg_contr]
    rw [neg_tensor]
    apply congrArg
    sorry
    sorry
-/
end Fermion

end
