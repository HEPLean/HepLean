/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
import HepLean.Tensors.Tree.NodeIdentities.Basic
/-!

# Associativity of products

The results here follow from the properties of braided categories and braided functors.
-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorTree

variable {S : TensorSpecies} {n n2 n3 : ℕ}
    (c : Fin n → S.C) (c2 : Fin n2 → S.C) (c3 : Fin n3 → S.C)

/-- The permutation that arises from assocativity of `prod` node.
  This permutation is defined using braiding and composition with `finSumFinEquiv`
  based-isomorphisms. -/
def assocPerm : OverColor.mk
    (Sum.elim (Sum.elim c c2 ∘ ⇑finSumFinEquiv.symm) c3 ∘ ⇑finSumFinEquiv.symm) ≅
    OverColor.mk (Sum.elim c (Sum.elim c2 c3 ∘ ⇑finSumFinEquiv.symm) ∘ ⇑finSumFinEquiv.symm) :=
  (equivToIso finSumFinEquiv).symm.trans <|
  (whiskerRightIso (equivToIso finSumFinEquiv).symm (OverColor.mk c3)).trans <|
  (α_ (OverColor.mk c) (OverColor.mk c2) (OverColor.mk c3)).trans <|
  (whiskerLeftIso (OverColor.mk c) (equivToIso finSumFinEquiv)).trans <|
  equivToIso finSumFinEquiv

lemma finSumFinEquiv_comp_assocPerm :
    (equivToIso finSumFinEquiv).hom ≫ (assocPerm c c2 c3).hom =
    (whiskerRightIso (equivToIso finSumFinEquiv).symm (OverColor.mk c3)).hom ≫
    (α_ (OverColor.mk c) (OverColor.mk c2) (OverColor.mk c3)).hom ≫
    (whiskerLeftIso (OverColor.mk c) (equivToIso finSumFinEquiv)).hom
    ≫ (equivToIso finSumFinEquiv).hom := by
  rw [assocPerm]
  simp

@[simp]
lemma assocPerm_toHomEquiv_hom : Hom.toEquiv (assocPerm c c2 c3).hom = finSumFinEquiv.symm.trans
    ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin n3))).trans
    ((Equiv.sumAssoc (Fin n) (Fin n2) (Fin n3)).trans
    (((Equiv.refl (Fin n)).sumCongr finSumFinEquiv).trans finSumFinEquiv))) := by
  simp [assocPerm]

@[simp]
lemma assocPerm_toHomEquiv_inv : Hom.toEquiv (assocPerm c c2 c3).inv = finSumFinEquiv.symm.trans
    (((Equiv.refl (Fin n)).sumCongr finSumFinEquiv.symm).trans
    ((Equiv.sumAssoc (Fin n) (Fin n2) (Fin n3)).symm.trans
    ((finSumFinEquiv.sumCongr (Equiv.refl (Fin n3))).trans finSumFinEquiv))) := by
  simp [assocPerm]

/-- The `prod` obeys associativity. -/
theorem prod_assoc (t : TensorTree S c) (t2 : TensorTree S c2) (t3 : TensorTree S c3) :
    (prod t (prod t2 t3)).tensor = (perm (assocPerm c c2 c3).hom (prod (prod t t2) t3)).tensor := by
  rw [perm_tensor]
  nth_rewrite 2 [prod_tensor]
  change _ = ((S.F.map (equivToIso finSumFinEquiv).hom) ≫ S.F.map (assocPerm c c2 c3).hom).hom
    (((Functor.LaxMonoidal.μ S.F (OverColor.mk (Sum.elim c c2 ∘ ⇑finSumFinEquiv.symm)) (OverColor.mk c3)).hom
        ((t.prod t2).tensor ⊗ₜ[S.k] t3.tensor)))
  rw [← S.F.map_comp, finSumFinEquiv_comp_assocPerm]
  simp only [Functor.id_obj, mk_hom, whiskerRightIso_hom, Iso.symm_hom, whiskerLeftIso_hom,
    Functor.map_comp, Action.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.coe_comp, Function.comp_apply]
  rw [prod_tensor]
  apply congrArg
  change _ = (S.F.map (OverColor.mk c ◁ (equivToIso finSumFinEquiv).hom)).hom
    ((S.F.map (α_ (OverColor.mk c) (OverColor.mk c2) (OverColor.mk c3)).hom).hom
    ((Functor.LaxMonoidal.μ S.F (OverColor.mk (Sum.elim c c2 ∘ ⇑finSumFinEquiv.symm)) (OverColor.mk c3)
    ≫ S.F.map ((equivToIso finSumFinEquiv).inv ▷ OverColor.mk c3)).hom
    (((t.prod t2).tensor ⊗ₜ[S.k] t3.tensor))))
  rw [← Functor.LaxMonoidal.μ_natural_left]
  simp only [Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Action.comp_hom,
    Action.instMonoidalCategory_whiskerRight_hom, ModuleCat.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  nth_rewrite 2 [prod_tensor]
  simp only [Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj]
  change _ = (S.F.map (OverColor.mk c ◁ (equivToIso finSumFinEquiv).hom)).hom
    ((S.F.map (α_ (OverColor.mk c) (OverColor.mk c2) (OverColor.mk c3)).hom).hom
    ((Functor.LaxMonoidal.μ S.F (OverColor.mk (Sum.elim c c2)) (OverColor.mk c3)).hom
    ((S.F.map (equivToIso finSumFinEquiv).hom ≫ S.F.map (equivToIso finSumFinEquiv).inv).hom
    (((Functor.LaxMonoidal.μ S.F (OverColor.mk c) (OverColor.mk c2)).hom (t.tensor ⊗ₜ[S.k] t2.tensor))) ⊗ₜ[S.k]
    t3.tensor)))
  simp only [Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Iso.map_hom_inv_id, Action.id_hom,
    ModuleCat.id_apply]
  change _ = (S.F.map (OverColor.mk c ◁ (equivToIso finSumFinEquiv).hom)).hom
    (((Functor.LaxMonoidal.μ S.F (OverColor.mk c) (OverColor.mk c2) ▷ S.F.obj (OverColor.mk c3)) ≫
    Functor.LaxMonoidal.μ S.F (OverColor.mk (Sum.elim c c2)) (OverColor.mk c3) ≫
    S.F.map (α_ (OverColor.mk c) (OverColor.mk c2) (OverColor.mk c3)).hom).hom
    (((t.tensor ⊗ₜ[S.k] t2.tensor) ⊗ₜ[S.k] t3.tensor)))
  erw [Functor.LaxMonoidal.associativity]
  simp only [Functor.id_obj, mk_hom, Action.instMonoidalCategory_tensorObj_V, Action.comp_hom,
    Action.instMonoidalCategory_associator_hom_hom, Action.instMonoidalCategory_whiskerLeft_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.associator_hom_apply]
  rw [prod_tensor]
  change ((_ ◁ (S.F.map (equivToIso finSumFinEquiv).hom)) ≫
    Functor.LaxMonoidal.μ S.F (OverColor.mk c) (OverColor.mk (Sum.elim c2 c3 ∘ ⇑finSumFinEquiv.symm))).hom
    (t.tensor ⊗ₜ[S.k]
    ((Functor.LaxMonoidal.μ S.F (OverColor.mk c2) (OverColor.mk c3)).hom (t2.tensor ⊗ₜ[S.k] t3.tensor))) = _
  rw [Functor.LaxMonoidal.μ_natural_right]
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.comp_hom, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    ModuleCat.coe_comp, Function.comp_apply]
  rfl

/-- The alternative version of associativity for `prod` where the permutation is on the opposite
  side. -/
lemma prod_assoc' (t : TensorTree S c) (t2 : TensorTree S c2) (t3 : TensorTree S c3) :
    (prod (prod t t2) t3).tensor = (perm (assocPerm c c2 c3).inv (prod t (prod t2 t3))).tensor :=
  perm_eq_of_eq_perm _ (prod_assoc c c2 c3 t t2 t3).symm

end TensorTree
