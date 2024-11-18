/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.TensorSpecies.Basic
import HepLean.Tensors.TensorSpecies.MetricTensor
/-!

# Isomorphism between rep of color `c` and rep of dual color.

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

noncomputable section

namespace TensorSpecies
open TensorTree
variable (S : TensorSpecies)

/-- The morphism from `S.FD.obj (Discrete.mk c)` to `S.FD.obj (Discrete.mk (S.τ c))`
  defined by contracting with the metric. -/
def toDualRep (c : S.C) : S.FD.obj (Discrete.mk c) ⟶ S.FD.obj (Discrete.mk (S.τ c)) :=
  (ρ_ (S.FD.obj (Discrete.mk c))).inv
  ≫ (S.FD.obj { as := c } ◁ (S.metric.app (Discrete.mk (S.τ c))))
  ≫ (α_ (S.FD.obj (Discrete.mk c)) (S.FD.obj (Discrete.mk (S.τ c)))
    (S.FD.obj (Discrete.mk (S.τ c)))).inv
  ≫ (S.contr.app (Discrete.mk c) ▷ S.FD.obj { as := S.τ c })
  ≫ (λ_ (S.FD.obj (Discrete.mk (S.τ c)))).hom

/-- The `toDualRep` for equal colors is the same, up-to conjugation by a trivial equivalence. -/
lemma toDualRep_congr {c c' : S.C} (h : c = c') : S.toDualRep c = S.FD.map (Discrete.eqToHom h) ≫
    S.toDualRep c' ≫ S.FD.map (Discrete.eqToHom (congrArg S.τ h.symm)) := by
  subst h
  simp only [eqToHom_refl, Discrete.functor_map_id, Category.comp_id, Category.id_comp]

/-- The morphism from `S.FD.obj (Discrete.mk (S.τ c))` to `S.FD.obj (Discrete.mk c)`
  defined by contracting with the metric. -/
def fromDualRep (c : S.C) : S.FD.obj (Discrete.mk (S.τ c)) ⟶ S.FD.obj (Discrete.mk c) :=
  S.toDualRep (S.τ c) ≫ S.FD.map (Discrete.eqToHom (S.τ_involution c))

/-- The rewriting of `toDualRep` in terms of `contrOneTwoLeft`. -/
lemma toDualRep_apply_eq_contrOneTwoLeft (c : S.C) (x : S.FD.obj (Discrete.mk c)) :
    (S.toDualRep c).hom x = (S.tensorToVec (S.τ c)).hom.hom
    (contrOneTwoLeft (((S.tensorToVec c).inv.hom x))
    (S.metricTensor (S.τ c))) := by
  simp only [toDualRep, Monoidal.tensorUnit_obj, Action.comp_hom,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Action.instMonoidalCategory_rightUnitor_inv_hom, Action.instMonoidalCategory_whiskerLeft_hom,
    Action.instMonoidalCategory_associator_inv_hom, Action.instMonoidalCategory_whiskerRight_hom,
    Action.instMonoidalCategory_leftUnitor_hom_hom, ModuleCat.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply,
    Nat.succ_eq_add_one, Nat.reduceAdd, contrOneTwoLeft, Functor.comp_obj,
    Discrete.functor_obj_eq_as, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, OverColor.Discrete.rep_iso_hom_inv_apply]
  repeat apply congrArg
  erw [pairIsoSep_inv_metricTensor]
  rfl

/-- Expansion of `toDualRep` is
  `(S.tensorToVec c).inv.hom x | μ ⊗ S.metricTensor (S.τ c) | μ ν`. -/
lemma toDualRep_tensorTree (c : S.C) (x : S.FD.obj (Discrete.mk c)) :
    let y : S.F.obj (OverColor.mk ![c]) := (S.tensorToVec c).inv.hom x
    (S.toDualRep c).hom x = (S.tensorToVec (S.τ c)).hom.hom
    ({y | μ ⊗ S.metricTensor (S.τ c) | μ ν}ᵀ
    |> perm (OverColor.equivToHomEq (Equiv.refl _) (fun x => by fin_cases x; rfl ))).tensor := by
  simp only
  rw [toDualRep_apply_eq_contrOneTwoLeft]
  apply congrArg
  exact contrOneTwoLeft_tensorTree ((S.tensorToVec c).inv.hom x) (S.metricTensor (S.τ c))

lemma fromDualRep_tensorTree (c : S.C) (x : S.FD.obj (Discrete.mk (S.τ c))) :
    let y : S.F.obj (OverColor.mk ![S.τ c]) := (S.tensorToVec (S.τ c)).inv.hom x
    (S.fromDualRep c).hom x = (S.tensorToVec c).hom.hom
    ({y | μ ⊗ S.metricTensor (S.τ (S.τ c))| μ ν}ᵀ
    |> perm (OverColor.equivToHomEq (Equiv.refl _) (fun x => by fin_cases x; exact (S.τ_involution c).symm ))).tensor := by
  simp only
  rw [fromDualRep]
  simp only [Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply, Nat.succ_eq_add_one,
    Nat.reduceAdd, Fin.isValue, Fin.succAbove_zero]
  rw [toDualRep_tensorTree]

end TensorSpecies

end
