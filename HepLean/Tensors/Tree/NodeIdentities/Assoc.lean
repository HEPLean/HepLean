/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.PermProd
import HepLean.Tensors.Tree.NodeIdentities.PermContr
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.ProdContr
import HepLean.Tensors.Tree.NodeIdentities.ContrContr
import HepLean.Tensors.Tree.NodeIdentities.ProdAssoc
import HepLean.Tensors.TensorSpecies.Contractions.Categorical
/-!

## Specific associativity results for tensor trees

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin
open TensorProduct

namespace TensorTree

variable {S : TensorSpecies}

set_option maxRecDepth 2000 in
/-- The associativity lemma for `t1 | μ ⊗ t2 | μ ν ⊗ t3 | ν σ`. -/
lemma assoc_one_two_two {c1 c2 c3 : S.C} (t1 : S.F.obj (OverColor.mk ![c1]))
    (t2 : S.F.obj (OverColor.mk ![S.τ c1, c2])) (t3 : S.F.obj (OverColor.mk ![S.τ c2, c3])) :
    {t1 | μ ⊗ t2 | μ ν ⊗ t3 | ν σ}ᵀ.tensor = ({t1 | μ ⊗ (t2 | μ ν ⊗ t3 | ν σ)}ᵀ
    |> perm (OverColor.equivToHomEq (Equiv.refl (Fin 1)) (by
      intro x
      fin_cases x
      rfl))).tensor := by
  conv_lhs =>
    rw [contr_tensor_eq <| contr_prod _ _ _]
    rw [perm_contr_congr 0 0 (by rfl) (by rfl)]
    erw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <|
      perm_tensor_eq <| prod_assoc' _ _ _ _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| perm_perm _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr_congr 0 0 (by
      simp only [Nat.succ_eq_add_one,
      Nat.reduceAdd, Fin.isValue, mk_left, Functor.id_obj, mk_hom, Equiv.toFun_as_coe,
      Hom.toEquiv_comp, equivToIso_homToEquiv, Equiv.symm_trans_apply]
      rfl) (by
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, mk_left, Functor.id_obj, mk_hom,
          Equiv.toFun_as_coe, Fin.zero_succAbove, Fin.succ_zero_eq_one, Function.comp_apply,
          Hom.toEquiv_comp, equivToIso_homToEquiv, Equiv.symm_trans_apply, extractOne_homToEquiv,
          assocPerm_toHomEquiv_inv, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.refl_symm,
          Equiv.sumCongr_apply, Equiv.coe_refl, finExtractOnePerm_symm_apply, Equiv.trans_apply,
          Equiv.symm_apply_apply, Sum.map_map, CompTriple.comp_eq, Equiv.symm_comp_self,
          Sum.map_id_id, id_eq, Equiv.self_comp_symm, Equiv.apply_symm_apply,
          finExtractOne_symm_inr_apply]
        rfl)]
    rw [perm_tensor_eq <| perm_contr_congr 0 2 (by
      simp only [Nat.succ_eq_add_one,
      Nat.reduceAdd, Fin.isValue, mk_left, Functor.id_obj, mk_hom, Equiv.toFun_as_coe,
      Hom.toEquiv_comp, equivToIso_homToEquiv, Equiv.symm_trans_apply, equivToIso_mkIso_hom,
      extractTwo_toEquiv]
      simp only [Equiv.refl_symm, mk_left,
        Hom.toEquiv_comp, assocPerm_toHomEquiv_inv, equivToIso_homToEquiv, ContrPair.leftContr,
        Equiv.toFun_as_coe, ContrPair.leftContrI, ContrPair.leftContrJ, Equiv.symm_trans_apply,
        Equiv.symm_apply_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
        Equiv.coe_refl, finExtractOnePerm_symm_apply, Equiv.trans_apply, Sum.map_map,
        CompTriple.comp_eq, Equiv.symm_comp_self, Sum.map_id_id, id_eq, Equiv.self_comp_symm,
        Equiv.apply_symm_apply, finExtractOne_symm_inr_apply, finExtractOnePerm_apply,
        Equiv.refl_apply]
      decide) (by
      simp only [Nat.succ_eq_add_one,
      Nat.reduceAdd, Fin.isValue, mk_left, Functor.id_obj, mk_hom, Equiv.toFun_as_coe,
      Hom.toEquiv_comp, equivToIso_homToEquiv, Equiv.symm_trans_apply, equivToIso_mkIso_hom]
      rw [extractOne_homToEquiv]
      simp only [Hom.toEquiv_comp, extractTwo_toEquiv, assocPerm_toHomEquiv_inv,
        ContrPair.leftContrI, ContrPair.leftContrJ, ContrPair.leftContr]
      simp only [mk_left,
        extractOne_homToEquiv, Hom.toEquiv_comp, equivToIso_homToEquiv, Equiv.symm_trans_apply,
        finExtractOnePerm_symm_apply, Equiv.trans_apply, equivToIso_mkIso_hom,
        Equiv.symm_apply_apply, Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.refl_symm,
        Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_map, CompTriple.comp_eq, Equiv.symm_comp_self,
        Sum.map_id_id, id_eq, Equiv.self_comp_symm, Equiv.apply_symm_apply,
        finExtractOne_symm_inr_apply, Equiv.refl_trans, finExtractOnePerm_apply]
      decide)]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_contr _ _ _]
    rw [perm_perm]
  conv_rhs =>
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_contr _ _ _]
    rw [perm_tensor_eq <| perm_contr_congr 0 0 (by rfl) (by rfl)]
    rw [perm_perm]
  apply perm_congr (OverColor.Hom.fin_ext _ _ fun i => ?_) rfl
  fin_cases i
  simp only [Hom.hom_comp, types_comp_apply, Over.comp_left, extractTwo_hom_left_apply]
  simp only [mkIso_hom_hom_left_apply]
  simp only [Hom.toEquiv_comp, extractTwo_toEquiv, assocPerm_toHomEquiv_inv,
    ContrPair.leftContrI, ContrPair.leftContrJ, ContrPair.leftContr]
  simp only [mk_left, equivToIso_mkIso_hom]
  simp only [equivToIso_homToEquiv, equivToHomEq_hom_left]
  simp only [contrContrPerm_hom_left_apply]
  decide

end TensorTree
