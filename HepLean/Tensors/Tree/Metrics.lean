/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.Tree.NodeIdentities.Basic
import HepLean.Tensors.Tree.NodeIdentities.Congr
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

/-- The metric of a tensor species in a `PiTensorProduct`. -/
def metricTensor (S : TensorSpecies) (c : S.C) :  S.F.obj (OverColor.mk ![c, c]) :=
  (OverColor.Discrete.pairIsoSep S.FD).hom.hom ((S.metric.app (Discrete.mk c)).hom (1 : S.k))

/-- The unit of a tensor species in a `PiTensorProduct`. -/
def unitTensor (S : TensorSpecies) (c : S.C) : S.F.obj (OverColor.mk ![S.τ c, c]) :=
  (OverColor.Discrete.pairIsoSep S.FD).hom.hom ((S.unit.app (Discrete.mk c)).hom (1 : S.k))

end TensorSpecies

namespace TensorTree

open TensorSpecies
variable {S : TensorSpecies}

lemma unitTensor_congr {c c' : S.C} (h : c = c') : {S.unitTensor c | μ ν}ᵀ.tensor =
    (perm  (OverColor.equivToHomEq (Equiv.refl _) (fun x => by subst h; fin_cases x <;> rfl ))
    {S.unitTensor c' | μ ν}ᵀ).tensor := by
  subst h
  change _ = (S.F.map (𝟙 _)).hom (S.unitTensor c)
  simp

lemma unitTensor_eq_dual_perm_eq (c : S.C) : ∀ (x : Fin (Nat.succ 0).succ),
   ![S.τ c, c] x = (![S.τ (S.τ c), S.τ c] ∘ ⇑(finMapToEquiv ![1, 0] ![1, 0]).symm) x := fun x => by
  fin_cases x
  · rfl
  · exact (S.τ_involution c).symm

/-- The unit tensor is equal to a permutation of indices of the dual tensor. -/
lemma unitTensor_eq_dual_perm (c : S.C) : {S.unitTensor c | μ ν}ᵀ.tensor =
    (perm  (OverColor.equivToHomEq (finMapToEquiv ![1,0] ![1, 0]) (unitTensor_eq_dual_perm_eq c))
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
  exact congrFun (congrArg (fun f => f.toFun) hg)  _

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

lemma pairIsoSep_inv_metricTensor (c : S.C) :
    (Discrete.pairIsoSep S.FD).inv.hom (S.metricTensor c) =
    (S.metric.app (Discrete.mk c)).hom (1 : S.k) := by
  simp [metricTensor]
  erw [Discrete.rep_iso_inv_hom_apply]


lemma contr_metric_braid_unit (c : S.C) :  (((S.FD.obj (Discrete.mk c)) ◁
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
  have hx : Function.Injective (β_ (S.FD.obj (Discrete.mk c)) (S.FD.obj (Discrete.mk (S.τ c))) ).hom.hom := by
    change  Function.Injective (β_ (S.FD.obj (Discrete.mk c)).V (S.FD.obj (Discrete.mk (S.τ c))).V ).hom
    exact (β_ (S.FD.obj (Discrete.mk c)).V (S.FD.obj (Discrete.mk (S.τ c))).V ).toLinearEquiv.toEquiv.injective
  apply hx
  rw [pairIsoSep_inv_metricTensor, pairIsoSep_inv_metricTensor]
  rw [S.contr_metric c]
  change  _ = (β_  (S.FD.obj { as := S.τ c }) (S.FD.obj { as := c })).inv.hom
    ((β_ (S.FD.obj { as := S.τ c }) (S.FD.obj { as := c })).hom.hom _)
  rw [Discrete.rep_iso_inv_hom_apply]


set_option maxHeartbeats 0 in
lemma contr_two_two_inner (c : S.C) (x : S.F.obj (OverColor.mk ![c, c]))
    (y : S.F.obj (OverColor.mk ![(S.τ c), (S.τ c)]) ):
    {x | μ ν ⊗ y| ν ρ}ᵀ.tensor =  (S.F.map (OverColor.mkIso (by
      funext x
      fin_cases x <;> rfl)).hom).hom ((OverColor.Discrete.pairIsoSep S.FD).hom.hom
    (((S.FD.obj (Discrete.mk c)) ◁ (λ_ (S.FD.obj (Discrete.mk (S.τ c)))).hom).hom
    (((S.FD.obj (Discrete.mk c)) ◁ ((S.contr.app (Discrete.mk c)) ▷
    (S.FD.obj (Discrete.mk (S.τ c))))).hom
    (((S.FD.obj (Discrete.mk c)) ◁ (α_ (S.FD.obj (Discrete.mk (c)))
      (S.FD.obj (Discrete.mk (S.τ c))) (S.FD.obj (Discrete.mk (S.τ c)))).inv).hom
    ((α_ (S.FD.obj (Discrete.mk (c))) (S.FD.obj (Discrete.mk (c)))
      (S.FD.obj (Discrete.mk (S.τ c)) ⊗ S.FD.obj (Discrete.mk (S.τ c)))).hom.hom
    (((OverColor.Discrete.pairIsoSep S.FD).inv.hom x ⊗ₜ
    (OverColor.Discrete.pairIsoSep S.FD).inv.hom y))))))):= by
  simp only [Nat.reduceAdd, Fin.isValue, contr_tensor, prod_tensor, Functor.id_obj, mk_hom,
    Action.instMonoidalCategory_tensorObj_V, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    tensorNode_tensor, Action.instMonoidalCategory_tensorUnit_V,
    Action.instMonoidalCategory_whiskerLeft_hom, Action.instMonoidalCategory_leftUnitor_hom_hom,
    Monoidal.tensorUnit_obj, Action.instMonoidalCategory_whiskerRight_hom,
    Action.instMonoidalCategory_associator_inv_hom, Action.instMonoidalCategory_associator_hom_hom]
  refine PiTensorProduct.induction_on' x ?_ (by
    intro a b hx hy
    simp only [Fin.isValue, Nat.reduceAdd, Functor.id_obj, mk_hom, add_tmul,
      map_add, hx, hy])
  intro rx fx
  refine PiTensorProduct.induction_on' y ?_ (by
      intro a b hx hy
      simp_all only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Functor.id_obj, mk_hom,
        PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul, map_add, tmul_add]
      )
  intro ry fy
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, tmul_smul, LinearMapClass.map_smul]
  apply congrArg
  simp only [smul_tmul, tmul_smul, LinearMapClass.map_smul]
  apply congrArg
  erw [Discrete.pairIsoSep_inv_tprod S.FD fx, Discrete.pairIsoSep_inv_tprod S.FD fy]
  change _ = (S.F.map (OverColor.mkIso _).hom).hom ((OverColor.Discrete.pairIsoSep S.FD).hom.hom
    ((fx (0 : Fin 2) ⊗ₜ[S.k]  (λ_ (S.FD.obj { as := S.τ c }).V).hom
      ((S.contr.app { as := c }).hom (fx (1 : Fin 2) ⊗ₜ[S.k] fy (0 : Fin 2)) ⊗ₜ[S.k] fy (1 : Fin 2)))))
  simp only [F_def, Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Monoidal.tensorUnit_obj,
    Action.instMonoidalCategory_tensorUnit_V, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, tmul_smul, map_smul]
  erw [OverColor.lift.μ_tmul_tprod S.FD]
  rw (config := { transparency := .instances }) [OverColor.lift.map_tprod]
  rw (config := { transparency := .instances }) [contrMap_tprod]
  congr 1
  /- The contraction. -/
  · congr
    · simp only [Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor, Fin.isValue,
      Function.comp_apply, Action.FunctorCategoryEquivalence.functor_obj_obj, mk_hom,
      equivToIso_homToEquiv, lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl,
      Iso.refl_hom, Action.id_hom, Iso.refl_inv, Functor.id_obj,
      instMonoidalCategoryStruct_tensorObj_hom, LinearEquiv.ofLinear_apply]
      rfl
    · simp only [Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor, Fin.isValue,
      Function.comp_apply, Functor.comp_obj, Discrete.functor_obj_eq_as,
      Action.FunctorCategoryEquivalence.functor_obj_obj, Nat.reduceAdd, eqToHom_refl,
      Discrete.functor_map_id, Action.id_hom, mk_hom, equivToIso_homToEquiv,
      lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Iso.refl_inv,
      Functor.id_obj, instMonoidalCategoryStruct_tensorObj_hom, LinearEquiv.ofLinear_apply]
      rfl
  /- The tensor. -/
  · rw (config := { transparency := .instances })  [Discrete.pairIsoSep_tmul, OverColor.lift.map_tprod]
    apply congrArg
    funext k
    match k with
    | (0 : Fin 2) => rfl
    | (1 : Fin 2) => rfl


lemma pairIsoSep_β_perm_cond (c1 c2 : S.C) :
   ∀ (x : Fin (Nat.succ 0).succ), ![c2, c1] x = (![c1, c2] ∘ ⇑(finMapToEquiv ![1, 0] ![1, 0]).symm) x:= by
  intro x
  fin_cases x
  · rfl
  · rfl

lemma pairIsoSep_β {c1 c2 : S.C} (x : ↑(S.FD.obj { as := c1 } ⊗ S.FD.obj { as := c2 }).V ) :
    (Discrete.pairIsoSep S.FD).hom.hom ((β_ (S.FD.obj (Discrete.mk c1)) _).hom.hom x) =
    (S.F.map ((OverColor.equivToHomEq (finMapToEquiv ![1, 0] ![1, 0]) (pairIsoSep_β_perm_cond c1 c2)))).hom
    ((Discrete.pairIsoSep S.FD).hom.hom x) := by
  have h1 : (Discrete.pairIsoSep S.FD).hom.hom ∘ₗ (β_ (S.FD.obj (Discrete.mk c1)) (S.FD.obj (Discrete.mk c2))).hom.hom
    = (S.F.map ((OverColor.equivToHomEq (finMapToEquiv ![1, 0] ![1, 0]) (pairIsoSep_β_perm_cond c1 c2)))).hom ∘ₗ (Discrete.pairIsoSep S.FD).hom.hom := by
    apply TensorProduct.ext'
    intro x y
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      Action.instMonoidalCategory_tensorObj_V, LinearMap.coe_comp, Function.comp_apply, Fin.isValue]
    change (Discrete.pairIsoSep S.FD).hom.hom (y ⊗ₜ x) =  (S.F.map ((OverColor.equivToHomEq (_) (pairIsoSep_β_perm_cond c1 c2)))).hom
      ((Discrete.pairIsoSep S.FD).hom.hom (x ⊗ₜ y))
    rw [Discrete.pairIsoSep_tmul, Discrete.pairIsoSep_tmul]
    erw [OverColor.lift.map_tprod]
    apply congrArg
    funext i
    fin_cases i
    · simp [lift.discreteFunctorMapEqIso]
      rfl
    · simp [lift.discreteFunctorMapEqIso]
      rfl
  exact congrFun (congrArg (fun f => f.toFun) h1)  _


lemma metricTensor_contr_dual_metricTensor_perm_cond (c : S.C) :
  ∀ (x : Fin (Nat.succ 0).succ),
  ((Sum.elim ![c, c] ![S.τ c, S.τ c] ∘ ⇑finSumFinEquiv.symm) ∘ Fin.succAbove 1 ∘ Fin.succAbove 1) x =
    (![S.τ c, c] ∘ ⇑(finMapToEquiv ![1, 0] ![1, 0]).symm) x := by
  intro x
  fin_cases x
  · rfl
  · rfl

/-- The contraction of a metric tensor with its dual gives the unit. -/
lemma metricTensor_contr_dual_metricTensor_eq_unit (c : S.C) :
    {S.metricTensor c | μ ν ⊗ S.metricTensor (S.τ c) | ν ρ}ᵀ.tensor =
    (perm (OverColor.equivToHomEq (finMapToEquiv ![1, 0] ![1, 0])
      (metricTensor_contr_dual_metricTensor_perm_cond c)) {S.unitTensor c | μ ρ}ᵀ).tensor := by
  rw [contr_two_two_inner, contr_metric_braid_unit, pairIsoSep_β]
  change (S.F.map _ ≫ S.F.map _ ).hom _ = _
  rw [← S.F.map_comp]
  rfl

end TensorTree

end
