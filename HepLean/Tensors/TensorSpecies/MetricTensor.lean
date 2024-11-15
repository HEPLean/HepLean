/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.TensorSpecies.UnitTensor
import HepLean.Tensors.TensorSpecies.ContractLemmas
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.PermProd
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.PermContr
/-!

## Metrics in tensor trees

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin
open TensorProduct
noncomputable section

namespace TensorSpecies
open TensorTree

/-- The metric of a tensor species in a `PiTensorProduct`. -/
def metricTensor (S : TensorSpecies) (c : S.C) : S.F.obj (OverColor.mk ![c, c]) :=
  (OverColor.Discrete.pairIsoSep S.FD).hom.hom ((S.metric.app (Discrete.mk c)).hom (1 : S.k))

variable {S : TensorSpecies}

lemma metricTensor_congr {c c' : S.C} (h : c = c') : {S.metricTensor c | μ ν}ᵀ.tensor =
    (perm (OverColor.equivToHomEq (Equiv.refl _) (fun x => by subst h; fin_cases x <;> rfl))
    {S.metricTensor c' | μ ν}ᵀ).tensor := by
  subst h
  change _ = (S.F.map (𝟙 _)).hom (S.metricTensor c)
  simp

lemma pairIsoSep_inv_metricTensor (c : S.C) :
    (Discrete.pairIsoSep S.FD).inv.hom (S.metricTensor c) =
    (S.metric.app (Discrete.mk c)).hom (1 : S.k) := by
  simp only [Action.instMonoidalCategory_tensorObj_V, Nat.succ_eq_add_one, Nat.reduceAdd,
    metricTensor, Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V]
  erw [Discrete.rep_iso_inv_hom_apply]

/-- Contraction of a metric tensor with a metric tensor gives the unit.
  Like `S.contr_metric` but with the braiding appearing on the side of the unit. -/
lemma contr_metric_braid_unit (c : S.C) : (((S.FD.obj (Discrete.mk c)) ◁
    (λ_ (S.FD.obj (Discrete.mk (S.τ c)))).hom).hom
    (((S.FD.obj (Discrete.mk c)) ◁ ((S.contr.app (Discrete.mk c)) ▷
    (S.FD.obj (Discrete.mk (S.τ c))))).hom
    (((S.FD.obj (Discrete.mk c)) ◁ (α_ (S.FD.obj (Discrete.mk (c)))
      (S.FD.obj (Discrete.mk (S.τ c))) (S.FD.obj (Discrete.mk (S.τ c)))).inv).hom
    ((α_ (S.FD.obj (Discrete.mk (c))) (S.FD.obj (Discrete.mk (c)))
      (S.FD.obj (Discrete.mk (S.τ c)) ⊗ S.FD.obj (Discrete.mk (S.τ c)))).hom.hom
    (((OverColor.Discrete.pairIsoSep S.FD).inv.hom (S.metricTensor c) ⊗ₜ
    (OverColor.Discrete.pairIsoSep S.FD).inv.hom (S.metricTensor (S.τ c)))))))) =
    (β_ (S.FD.obj (Discrete.mk (S.τ c))) (S.FD.obj (Discrete.mk c))).hom.hom
      ((S.unit.app (Discrete.mk c)).hom (1 : S.k)) := by
  apply (β_ _ _).toLinearEquiv.toEquiv.injective
  rw [pairIsoSep_inv_metricTensor, pairIsoSep_inv_metricTensor]
  erw [S.contr_metric c]
  change _ = (β_ (S.FD.obj { as := S.τ c }) (S.FD.obj { as := c })).inv.hom
    ((β_ (S.FD.obj { as := S.τ c }) (S.FD.obj { as := c })).hom.hom _)
  rw [Discrete.rep_iso_inv_hom_apply]

lemma metricTensor_contr_dual_metricTensor_perm_cond (c : S.C) : ∀ (x : Fin (Nat.succ 0).succ),
    ((Sum.elim ![c, c] ![S.τ c, S.τ c] ∘ ⇑finSumFinEquiv.symm) ∘
    Fin.succAbove 1 ∘ Fin.succAbove 1) x =
    (![S.τ c, c] ∘ ⇑(finMapToEquiv ![1, 0] ![1, 0]).symm) x := by
  intro x
  fin_cases x
  · rfl
  · rfl

/-- The contraction of a metric tensor with its dual via the inner indices gives the unit. -/
lemma metricTensor_contr_dual_metricTensor_eq_unit (c : S.C) :
    {S.metricTensor c | μ ν ⊗ S.metricTensor (S.τ c) | ν ρ}ᵀ.tensor = ({S.unitTensor c | μ ρ}ᵀ |>
    perm (OverColor.equivToHomEq (finMapToEquiv ![1, 0] ![1, 0])
      (metricTensor_contr_dual_metricTensor_perm_cond c))).tensor := by
  rw [contr_two_two_inner, contr_metric_braid_unit, Discrete.pairIsoSep_β]
  change (S.F.map _ ≫ S.F.map _).hom _ = _
  rw [← S.F.map_comp]
  rfl

/-- The contraction of a metric tensor with its dual via the outer indices gives the unit. -/
lemma metricTensor_contr_dual_metricTensor_outer_eq_unit (c : S.C) :
    {S.metricTensor c | ν μ ⊗ S.metricTensor (S.τ c) | ρ ν}ᵀ.tensor = ({S.unitTensor c | μ ρ}ᵀ |>
    perm (OverColor.equivToHomEq
      (finMapToEquiv ![1, 0] ![1, 0]) (fun x => by fin_cases x <;> rfl))).tensor := by
  conv_lhs =>
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| metricTensor_congr (S.τ_involution c).symm]
    rw [contr_tensor_eq <| prod_comm _ _ _ _]
    rw [perm_contr_congr 2 1 (by rfl) (by rfl)]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_perm_right _ _ _ _]
    rw [perm_tensor_eq <| perm_contr_congr 2 1 (by rfl) (by rfl)]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_swap _ _]
    rw [perm_perm]
    erw [perm_tensor_eq <| metricTensor_contr_dual_metricTensor_eq_unit _]
    rw [perm_perm]
    rw [perm_tensor_eq <| dual_unitTensor_eq_perm _]
    rw [perm_perm]
  apply perm_congr _ rfl
  apply OverColor.Hom.fin_ext
  intro i
  simp only [Functor.id_obj, mk_hom, Function.comp_apply, Equiv.refl_symm, Equiv.coe_refl, id_eq,
    Fin.zero_eta, Matrix.cons_val_zero, List.pmap.eq_1, ContrPair.contrSwapHom,
    extractOne_homToEquiv, Category.assoc, Hom.hom_comp, Over.comp_left, equivToHomEq_hom_left,
    Equiv.toFun_as_coe, types_comp_apply, finMapToEquiv_apply, mkIso_hom_hom_left_apply]
  rw [extractTwo_hom_left_apply]
  simp only [mk_left, braidPerm_toEquiv, Equiv.symm_trans_apply, Equiv.symm_symm,
    Equiv.sumComm_symm, Equiv.sumComm_apply, finExtractOnePerm_symm_apply, Equiv.trans_apply,
    Equiv.symm_apply_apply, Sum.swap_swap, Equiv.apply_symm_apply, finExtractOne_symm_inr_apply,
    Fin.zero_succAbove, List.pmap.eq_2, Fin.mk_one, List.pmap.eq_1, Matrix.cons_val_one,
    Matrix.head_cons, extractTwo_hom_left_apply, permProdRight_toEquiv, equivToHomEq_toEquiv,
    Equiv.sumCongr_refl, Equiv.refl_trans, Equiv.symm_trans_self, Equiv.refl_symm, Equiv.refl_apply,
    predAboveI_succAbove, finExtractOnePerm_apply]
  fin_cases i
  · decide
  · decide

end TensorSpecies

end
