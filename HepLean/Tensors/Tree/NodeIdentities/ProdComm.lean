/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

# Commuting products

The results here follow from the properties of braided categories and braided functors.
-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorTree

variable {S : TensorSpecies} {n n2 : ℕ}
    (c : Fin n → S.C) (c2 : Fin n2 → S.C)

/-- The permutation that arises when moving a commuting terms in a `prod` node.
  This permutation is defined using braiding and composition with `finSumFinEquiv`
  based-isomorphisms. -/
def braidPerm : OverColor.mk (Sum.elim c2 c ∘ ⇑finSumFinEquiv.symm) ⟶
    OverColor.mk (Sum.elim c c2 ∘ ⇑finSumFinEquiv.symm) :=
  (equivToIso finSumFinEquiv).inv ≫
  (β_ (OverColor.mk c2) (OverColor.mk c)).hom
  ≫ (equivToIso finSumFinEquiv).hom

lemma finSumFinEquiv_comp_braidPerm :
    (equivToIso finSumFinEquiv).hom ≫ braidPerm c c2 =
    (β_ (OverColor.mk c2) (OverColor.mk c)).hom
    ≫ (equivToIso finSumFinEquiv).hom := by
  rw [braidPerm]
  simp only [Functor.id_obj, mk_hom, Iso.hom_inv_id_assoc]

/-- The arguments of a `prod` node can be commuted using braiding. -/
theorem prod_comm (t : TensorTree S c) (t2 : TensorTree S c2) :
    (prod t t2).tensor = (perm (braidPerm c c2) (prod t2 t)).tensor := by
  rw [perm_tensor]
  nth_rewrite 2 [prod_tensor]
  change _ = (S.F.map (equivToIso finSumFinEquiv).hom ≫ S.F.map (braidPerm c c2)).hom
    ((S.F.μ (OverColor.mk c2) (OverColor.mk c)).hom (t2.tensor ⊗ₜ[S.k] t.tensor))
  rw [← S.F.map_comp]
  rw [finSumFinEquiv_comp_braidPerm]
  rw [S.F.map_comp]
  simp only [BraidedFunctor.braided, Category.assoc, Action.comp_hom,
    Action.instMonoidalCategory_tensorObj_V, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    ModuleCat.coe_comp, Function.comp_apply]
  rw [prod_tensor]
  apply congrArg
  apply congrArg
  change _ = (β_ (S.F.obj (OverColor.mk c2)) (S.F.obj (OverColor.mk c))).hom.hom
    ((inv (lift.μ S.FD (OverColor.mk c2) (OverColor.mk c)).hom).hom
    ((lift.μ S.FD (OverColor.mk c2) (OverColor.mk c)).hom.hom (t2.tensor ⊗ₜ[S.k] t.tensor)))
  simp only [Action.instMonoidalCategory_tensorObj_V, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    lift.objObj'_V_carrier, instMonoidalCategoryStruct_tensorObj_left,
    instMonoidalCategoryStruct_tensorObj_hom, mk_hom, IsIso.Iso.inv_hom]
  change _ = (β_ (S.F.obj (OverColor.mk c2)) (S.F.obj (OverColor.mk c))).hom.hom
    (((lift.μ S.FD (OverColor.mk c2) (OverColor.mk c)).hom ≫
    (lift.μ S.FD (OverColor.mk c2) (OverColor.mk c)).inv).hom ((t2.tensor ⊗ₜ[S.k] t.tensor)))
  simp only [Action.instMonoidalCategory_tensorObj_V, Iso.hom_inv_id, Action.id_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, lift.objObj'_V_carrier, mk_hom,
    ModuleCat.id_apply]
  rfl

end TensorTree
