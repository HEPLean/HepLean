/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.TensorSpecies.UnitTensor
/-!

## Contraction of specific tensor types

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

variable {S : TensorSpecies}

/-- Expands the inner contraction of two 2-tensors which are
  tprods in terms of basic categorical
  constructions and fields of the tensor species. -/
lemma contr_two_two_inner_tprod (c : S.C) (x : S.F.obj (OverColor.mk ![c, c]))
    (fx : (i : (𝟭 Type).obj (OverColor.mk ![c, c]).left) →
      CoeSort.coe (S.FD.obj { as := (OverColor.mk ![c, c]).hom i }))
    (y : S.F.obj (OverColor.mk ![(S.τ c), (S.τ c)]))
    (fy : (i : (𝟭 Type).obj (OverColor.mk ![S.τ c, S.τ c]).left) →
      CoeSort.coe (S.FD.obj { as := (OverColor.mk ![S.τ c, S.τ c]).hom i }))
    (hx : x = PiTensorProduct.tprod S.k fx)
    (hy : y = PiTensorProduct.tprod S.k fy) :
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
  subst hx
  subst hy
  rw [Discrete.pairIsoSep_inv_tprod S.FD fx, Discrete.pairIsoSep_inv_tprod S.FD fy]
  change _ = (S.F.map (OverColor.mkIso _).hom).hom ((OverColor.Discrete.pairIsoSep S.FD).hom.hom
    ((fx (0 : Fin 2) ⊗ₜ[S.k]  (λ_ (S.FD.obj { as := S.τ c }).V).hom
      ((S.contr.app { as := c }).hom (fx (1 : Fin 2) ⊗ₜ[S.k] fy (0 : Fin 2)) ⊗ₜ[S.k] fy (1 : Fin 2)))))
  simp only [F_def, Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Monoidal.tensorUnit_obj,
    Action.instMonoidalCategory_tensorUnit_V, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_hom_apply, tmul_smul, map_smul]
  conv_lhs =>
    simp only [Nat.reduceAdd, Fin.isValue, contr_tensor, prod_tensor, Functor.id_obj, mk_hom,
    Action.instMonoidalCategory_tensorObj_V, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    tensorNode_tensor, Action.instMonoidalCategory_tensorUnit_V,
    Action.instMonoidalCategory_whiskerLeft_hom, Action.instMonoidalCategory_leftUnitor_hom_hom,
    Monoidal.tensorUnit_obj, Action.instMonoidalCategory_whiskerRight_hom,
    Action.instMonoidalCategory_associator_inv_hom, Action.instMonoidalCategory_associator_hom_hom,
    F_def]
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
  · rw (config := { transparency := .instances })  [Discrete.pairIsoSep_tmul,
      OverColor.lift.map_tprod]
    apply congrArg
    funext k
    match k with
    | (0 : Fin 2) => rfl
    | (1 : Fin 2) => rfl

/-- Expands the inner contraction of two 2-tensors in terms of basic categorical
  constructions and fields of the tensor species. -/
lemma contr_two_two_inner (c : S.C) (x : S.F.obj (OverColor.mk ![c, c]))
    (y : S.F.obj (OverColor.mk ![(S.τ c), (S.τ c)])):
    {x | μ ν ⊗ y| ν ρ}ᵀ.tensor = (S.F.map (OverColor.mkIso (by
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
        PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul, map_add, tmul_add])
  intro ry fy
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, tmul_smul, LinearMapClass.map_smul]
  apply congrArg
  simp only [smul_tmul, tmul_smul, LinearMapClass.map_smul]
  apply congrArg
  simpa using contr_two_two_inner_tprod c (PiTensorProduct.tprod S.k fx) fx
    (PiTensorProduct.tprod S.k fy) fy

end TensorSpecies

end
