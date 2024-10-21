/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

# Swapping permutations and contractions

The results here follow from the properties of Monoidal categories and monoidal functors.
-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorTree

variable {S : TensorStruct} {n n' n2 : ℕ}
    {c : Fin n → S.C} {c' : Fin n' → S.C} (c2 : Fin n2 → S.C)
    (σ : OverColor.mk c ⟶ OverColor.mk c')

/-- The permutation that arises when moving a `perm` node in the left entry through a `prod` node.
  This permutation is defined using right-whiskering and composition with `finSumFinEquiv`
  based-isomorphisms. -/
def permProdLeft := (equivToIso finSumFinEquiv).inv ≫ σ ▷ OverColor.mk c2
  ≫ (equivToIso finSumFinEquiv).hom

/-- The permutation that arises when moving a `perm` node in the right entry through a `prod` node.
  This permutation is defined using left-whiskering and composition with `finSumFinEquiv`
  based-isomorphisms. -/
def permProdRight := (equivToIso finSumFinEquiv).inv ≫ OverColor.mk c2 ◁ σ
  ≫ (equivToIso finSumFinEquiv).hom

/-- When a `prod` acts on a `perm` node in the left entry, the `perm` node can be moved through
  the `prod` node via right-whiskering. -/
theorem prod_perm_left (t : TensorTree S c) (t2 : TensorTree S c2) :
    (prod (perm σ t) t2).tensor = (perm (permProdLeft c2 σ) (prod t t2)).tensor := by
  simp only [prod_tensor, Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, perm_tensor]
  change (S.F.map (equivToIso finSumFinEquiv).hom).hom
    (((S.F.map (σ) ▷ S.F.obj (OverColor.mk c2)) ≫
    S.F.μ (OverColor.mk c') (OverColor.mk c2)).hom (t.tensor ⊗ₜ[S.k] t2.tensor)) = _
  rw [S.F.μ_natural_left]
  simp only [Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V, Action.comp_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.coe_comp, Function.comp_apply]
  change (S.F.map (σ ▷ OverColor.mk c2) ≫ S.F.map (equivToIso finSumFinEquiv).hom).hom _ = _
  rw [← S.F.map_comp, ← (Iso.hom_inv_id_assoc (equivToIso finSumFinEquiv)
      (σ ▷ OverColor.mk c2 ≫ (equivToIso finSumFinEquiv).hom)), S.F.map_comp]
  rfl

/-- When a `prod` acts on a `perm` node in the right entry, the `perm` node can be moved through
  the `prod` node via left-whiskering. -/
theorem prod_perm_right (t2 : TensorTree S c2) (t : TensorTree S c) :
    (prod t2 (perm σ t)).tensor = (perm (permProdRight c2 σ) (prod t2 t)).tensor := by
  simp only [prod_tensor, Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, perm_tensor]
  change (S.F.map (equivToIso finSumFinEquiv).hom).hom
    (((S.F.obj (OverColor.mk c2) ◁ S.F.map σ) ≫ S.F.μ (OverColor.mk c2) (OverColor.mk c')).hom
    (t2.tensor ⊗ₜ[S.k] t.tensor)) = _
  rw [S.F.μ_natural_right]
  simp only [Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V, Action.comp_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.coe_comp, Function.comp_apply]
  change (S.F.map (OverColor.mk c2 ◁ σ) ≫ S.F.map (equivToIso finSumFinEquiv).hom).hom _ = _
  rw [← S.F.map_comp]
  have hx : OverColor.mk c2 ◁ σ ≫ (equivToIso finSumFinEquiv).hom =
    (equivToIso finSumFinEquiv).hom ≫ (permProdRight c2 σ) := by
    simp only [Functor.id_obj, mk_hom, permProdRight, Iso.hom_inv_id_assoc]
  rw [hx, S.F.map_comp]
  rfl

end TensorTree
