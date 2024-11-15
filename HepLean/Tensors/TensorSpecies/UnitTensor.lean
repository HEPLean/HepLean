/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.Tree.NodeIdentities.Basic
import HepLean.Tensors.Tree.NodeIdentities.Congr
import HepLean.Tensors.TensorSpecies.ContractLemmas
/-!

## Units as tensors

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin
open TensorProduct
noncomputable section

namespace TensorSpecies

/-- The unit of a tensor species in a `PiTensorProduct`. -/
def unitTensor (S : TensorSpecies) (c : S.C) : S.F.obj (OverColor.mk ![S.τ c, c]) :=
  (OverColor.Discrete.pairIsoSep S.FD).hom.hom ((S.unit.app (Discrete.mk c)).hom (1 : S.k))

variable {S : TensorSpecies}
open TensorTree

/-- The relation between two units of colors which are equal. -/
lemma unitTensor_congr {c c' : S.C} (h : c = c') : {S.unitTensor c | μ ν}ᵀ.tensor =
    (perm (OverColor.equivToHomEq (Equiv.refl _) (fun x => by subst h; fin_cases x <;> rfl))
    {S.unitTensor c' | μ ν}ᵀ).tensor := by
  subst h
  change _ = (S.F.map (𝟙 _)).hom (S.unitTensor c)
  simp

lemma pairIsoSep_inv_unitTensor (c : S.C) :
    (Discrete.pairIsoSep S.FD).inv.hom (S.unitTensor c) =
    (S.unit.app (Discrete.mk c)).hom (1 : S.k) := by
  simp only [Action.instMonoidalCategory_tensorObj_V, Nat.succ_eq_add_one, Nat.reduceAdd,
    unitTensor, Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V]
  erw [Discrete.rep_iso_inv_hom_apply]

lemma unitTensor_eq_dual_perm_eq (c : S.C) : ∀ (x : Fin (Nat.succ 0).succ),
    ![S.τ c, c] x = (![S.τ (S.τ c), S.τ c] ∘ ⇑(finMapToEquiv ![1, 0] ![1, 0]).symm) x := fun x => by
  fin_cases x
  · rfl
  · exact (S.τ_involution c).symm

/-- The unit tensor is equal to a permutation of indices of the dual tensor. -/
lemma unitTensor_eq_dual_perm (c : S.C) : {S.unitTensor c | μ ν}ᵀ.tensor =
    (perm (OverColor.equivToHomEq (finMapToEquiv ![1,0] ![1, 0]) (unitTensor_eq_dual_perm_eq c))
    {S.unitTensor (S.τ c) | ν μ }ᵀ).tensor := by
  simp [unitTensor, tensorNode_tensor, perm_tensor]
  have h1 := S.unit_symm c
  erw [h1]
  have hg : (Discrete.pairIsoSep S.FD).hom.hom ∘ₗ (S.FD.obj { as := S.τ c } ◁
      S.FD.map (Discrete.eqToHom (S.τ_involution c))).hom ∘ₗ
      (β_ (S.FD.obj { as := S.τ (S.τ c) }) (S.FD.obj { as := S.τ c })).hom.hom =
      (S.F.map (equivToHomEq (finMapToEquiv ![1, 0] ![1, 0]) (unitTensor_eq_dual_perm_eq c))).hom
      ∘ₗ (Discrete.pairIsoSep S.FD).hom.hom := by
    apply TensorProduct.ext'
    intro x y
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_whiskerLeft_hom,
      LinearMap.coe_comp, Function.comp_apply, Fin.isValue]
    change (Discrete.pairIsoSep S.FD).hom.hom
      (((y ⊗ₜ[S.k] ((S.FD.map (Discrete.eqToHom _)).hom x)))) =
      ((S.F.map (equivToHomEq (finMapToEquiv ![1, 0] ![1, 0]) _)).hom ∘ₗ
      (Discrete.pairIsoSep S.FD).hom.hom) (x ⊗ₜ[S.k] y)
    rw [Discrete.pairIsoSep_tmul]
    conv_rhs =>
      simp [Discrete.pairIsoSep_tmul]
    change _ =
      (S.F.map (equivToHomEq (finMapToEquiv ![1, 0] ![1, 0]) _)).hom
      ((Discrete.pairIsoSep S.FD).hom.hom (x ⊗ₜ[S.k] y))
    rw [Discrete.pairIsoSep_tmul]
    simp only [F_def, Nat.succ_eq_add_one, Nat.reduceAdd, mk_hom, Functor.id_obj, Fin.isValue]
    erw [OverColor.lift.map_tprod]
    apply congrArg
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.cases_zero, mk_hom,
      Nat.succ_eq_add_one, Nat.reduceAdd, lift.discreteFunctorMapEqIso, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
      rfl
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, mk_hom,
      Nat.succ_eq_add_one, Nat.reduceAdd, lift.discreteFunctorMapEqIso, Functor.mapIso_hom,
      eqToIso.hom, Functor.mapIso_inv, eqToIso.inv, LinearEquiv.ofLinear_apply]
      rfl
  exact congrFun (congrArg (fun f => f.toFun) hg) _

lemma dual_unitTensor_eq_perm_eq (c : S.C) : ∀ (x : Fin (Nat.succ 0).succ),
    ![S.τ (S.τ c), S.τ c] x = (![S.τ c, c] ∘ ⇑(finMapToEquiv ![1, 0] ![1, 0]).symm) x := fun x => by
  fin_cases x
  · exact (S.τ_involution c)
  · rfl

lemma dual_unitTensor_eq_perm (c : S.C) : {S.unitTensor (S.τ c) | ν μ}ᵀ.tensor =
    (perm (OverColor.equivToHomEq (finMapToEquiv ![1, 0] ![1, 0]) (dual_unitTensor_eq_perm_eq c))
    {S.unitTensor c | μ ν}ᵀ).tensor := by
  rw [unitTensor_eq_dual_perm]
  conv =>
    lhs
    rw [perm_tensor_eq <| unitTensor_congr (S.τ_involution c)]
    rw [perm_perm]
  refine perm_congr ?_ rfl
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  rfl

lemma contrOneTwoLeft_unitTensor  {c1 : S.C}
    (x : S.F.obj (OverColor.mk ![c1])) :
    contrOneTwoLeft x (S.unitTensor c1) = x := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, contrOneTwoLeft,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Action.instMonoidalCategory_leftUnitor_hom_hom, Monoidal.tensorUnit_obj,
    Action.instMonoidalCategory_whiskerRight_hom, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply, Action.instMonoidalCategory_associator_inv_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj]
  erw [pairIsoSep_inv_unitTensor (S := S) (c := c1)]
  change (S.F.mapIso (mkIso _)).hom.hom _ = _
  rw [Discrete.rep_iso_apply_iff, Discrete.rep_iso_inv_apply_iff]
  simpa using  S.contr_unit c1 ((OverColor.forgetLiftApp S.FD c1).hom.hom ((S.F.map (OverColor.mkIso (by
    funext x; fin_cases x; rfl)).hom).hom x))

lemma one_contr_unitTensor_eq_self {c1 : S.C} (x : S.F.obj (OverColor.mk ![c1])) :
    {x | μ ⊗ S.unitTensor c1 | μ ν}ᵀ.tensor = ({x | ν}ᵀ |>
    perm (OverColor.equivToHomEq (Equiv.refl _) (fun x => by fin_cases x; rfl ))).tensor  := by
  rw [contr_one_two_left_eq_contrOneTwoLeft, contrOneTwoLeft_unitTensor]
  rfl

end TensorSpecies

end
