/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Basic
import HepLean.Tensors.OverColor.Lift
import HepLean.Mathematics.PiTensorProduct
import HepLean.Tensors.OverColor.Iso
import LLMLean
/-!

# Discrete color category

-/

namespace IndexNotation
namespace OverColor
namespace Discrete

open CategoryTheory
open MonoidalCategory
open TensorProduct
variable {C k : Type} [CommRing k] {G : Type} [Group G]

variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')
noncomputable section

/-- The functor taking `c` to `F c ⊗ F c`. -/
def pair : Discrete C ⥤ Rep k G := F ⊗ F

/-- The isomorphism between the image of `(pair F).obj` and
  `(lift.obj F).obj (OverColor.mk ![c,c])`. -/
def pairIso (c : C) : (pair F).obj (Discrete.mk c) ≅ (lift.obj F).obj (OverColor.mk ![c,c]) := by
  symm
  apply ((lift.obj F).mapIso fin2Iso).trans
  apply ((lift.obj F).μIso _ _).symm.trans
  apply tensorIso ?_ ?_
  · symm
    apply (forgetLiftApp F c).symm.trans
    refine (lift.obj F).mapIso (mkIso ?_)
    funext x
    fin_cases x
    rfl
  · symm
    apply (forgetLiftApp F c).symm.trans
    refine (lift.obj F).mapIso (mkIso ?_)
    funext x
    fin_cases x
    rfl

def pairIsoSep {c1 c2 : C} : F.obj (Discrete.mk c1) ⊗ F.obj (Discrete.mk c2) ≅
    (lift.obj F).obj (OverColor.mk ![c1,c2]) := by
  symm
  apply ((lift.obj F).mapIso fin2Iso).trans
  apply ((lift.obj F).μIso _ _).symm.trans
  apply tensorIso ?_ ?_
  · symm
    apply (forgetLiftApp F c1).symm.trans
    refine (lift.obj F).mapIso (mkIso ?_)
    funext x
    fin_cases x
    rfl
  · symm
    apply (forgetLiftApp F c2).symm.trans
    refine (lift.obj F).mapIso (mkIso ?_)
    funext x
    fin_cases x
    rfl

lemma pairIsoSep_tmul {c1 c2 : C} (x : F.obj (Discrete.mk c1)) (y : F.obj (Discrete.mk c2)) :
    (pairIsoSep F).hom.hom (x ⊗ₜ[k] y) =
    PiTensorProduct.tprod k (Fin.cases x (Fin.cases y (fun i  => Fin.elim0 i))) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Action.instMonoidalCategory_tensorObj_V,
    pairIsoSep, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    forgetLiftApp, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom,
    tensorIso_inv, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, tensor_comp,
    MonoidalFunctor.μIso_hom, Functor.mapIso_inv, Category.assoc,
    LaxMonoidalFunctor.μ_natural_assoc, Action.comp_hom, Action.instMonoidalCategory_tensorHom_hom,
    Action.mkIso_inv_hom, LinearEquiv.toModuleIso_inv, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    ModuleCat.coe_comp, Function.comp_apply, ModuleCat.MonoidalCategory.hom_apply, Functor.id_obj]
  erw [forgetLiftAppV_symm_apply F c1, forgetLiftAppV_symm_apply F c2]
  change ((lift.obj F).map fin2Iso.inv).hom
    (((lift.obj F).map ((mkIso _).hom ⊗ (mkIso _).hom)).hom
      (((lift.obj F).μ (mk fun _ => c1) (mk fun _ => c2)).hom
        (((PiTensorProduct.tprod k) fun _ => x) ⊗ₜ[k] (PiTensorProduct.tprod k) fun x => y))) = _
  rw [lift.obj_μ_tprod_tmul F (mk fun _ => c1) (mk fun _ => c2)]
  change ((lift.obj F).map fin2Iso.inv).hom
    (((lift.obj F).map ((mkIso _).hom ⊗ (mkIso _).hom)).hom
      ((PiTensorProduct.tprod k) _))  = _
  rw [lift.map_tprod]
  change ((lift.obj F).map fin2Iso.inv).hom ((PiTensorProduct.tprod k) fun i => _) = _
  rw [lift.map_tprod]
  congr
  funext i
  match i with
  | (0 : Fin 2) =>
    simp [fin2Iso, HepLean.PiTensorProduct.elimPureTensor, mkIso, mkSum]
    exact (LinearEquiv.eq_symm_apply _).mp rfl
  | (1 : Fin 2) =>
    simp [fin2Iso, HepLean.PiTensorProduct.elimPureTensor, mkIso, mkSum]
    exact (LinearEquiv.eq_symm_apply _).mp rfl






/-- The functor taking `c` to `F c ⊗ F (τ c)`. -/
def pairτ (τ : C → C) : Discrete C ⥤ Rep k G :=
  F ⊗ ((Discrete.functor (Discrete.mk ∘ τ) : Discrete C ⥤ Discrete C) ⋙ F)

/-- The functor taking `c` to `F (τ c) ⊗ F c`. -/
def τPair (τ : C → C) : Discrete C ⥤ Rep k G :=
  ((Discrete.functor (Discrete.mk ∘ τ) : Discrete C ⥤ Discrete C) ⋙ F) ⊗ F

end
end Discrete
end OverColor
end IndexNotation
