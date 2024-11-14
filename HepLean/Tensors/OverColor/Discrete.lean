/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Basic
import HepLean.Tensors.OverColor.Lift
import HepLean.Mathematics.PiTensorProduct
import HepLean.Tensors.OverColor.Iso
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

/-- The isomorphism between `F.obj (Discrete.mk c1) ⊗ F.obj (Discrete.mk c2)` and
  `(lift.obj F).obj (OverColor.mk ![c1,c2])` formed by the tensorate. -/
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
    PiTensorProduct.tprod k (Fin.cases x (Fin.cases y (fun i => Fin.elim0 i))) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Action.instMonoidalCategory_tensorObj_V,
    pairIsoSep, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    forgetLiftApp, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom,
    tensorIso_inv, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, tensor_comp,
    MonoidalFunctor.μIso_hom, Functor.mapIso_inv, Category.assoc,
    LaxMonoidalFunctor.μ_natural_assoc, Action.comp_hom, Action.instMonoidalCategory_tensorHom_hom,
    Action.mkIso_inv_hom, LinearEquiv.toModuleIso_inv, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    ModuleCat.coe_comp, Function.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul,
    Functor.id_obj]
  erw [forgetLiftAppV_symm_apply F c1, forgetLiftAppV_symm_apply F c2]
  change ((lift.obj F).map fin2Iso.inv).hom
    (((lift.obj F).map ((mkIso _).hom ⊗ (mkIso _).hom)).hom
      (((lift.obj F).μ (mk fun _ => c1) (mk fun _ => c2)).hom
        (((PiTensorProduct.tprod k) fun _ => x) ⊗ₜ[k] (PiTensorProduct.tprod k) fun _ => y))) = _
  rw [lift.obj_μ_tprod_tmul F (mk fun _ => c1) (mk fun _ => c2)]
  change ((lift.obj F).map fin2Iso.inv).hom
    (((lift.obj F).map ((mkIso _).hom ⊗ (mkIso _).hom)).hom
      ((PiTensorProduct.tprod k) _)) = _
  rw [lift.map_tprod]
  erw [lift.map_tprod]
  congr
  funext i
  match i with
  | (0 : Fin 2) =>
    simp only [mk_hom, Fin.isValue, Matrix.cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
      Matrix.cons_val_one, Matrix.head_cons, instMonoidalCategoryStruct_tensorObj_left, fin2Iso,
      Equiv.symm_symm, mkSum, mkIso, Iso.trans_inv, tensorIso_inv,
      instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj,
      HepLean.PiTensorProduct.elimPureTensor, Fin.cases_zero]
    exact (LinearEquiv.eq_symm_apply _).mp rfl
  | (1 : Fin 2) =>
    simp only [mk_hom, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Nat.succ_eq_add_one,
      Nat.reduceAdd, Matrix.cons_val_zero, instMonoidalCategoryStruct_tensorObj_left, fin2Iso,
      Equiv.symm_symm, mkSum, mkIso, Iso.trans_inv, tensorIso_inv,
      instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj,
      HepLean.PiTensorProduct.elimPureTensor]
    exact (LinearEquiv.eq_symm_apply _).mp rfl

lemma pairIsoSep_inv_tprod {c1 c2 : C} (fx : (i : (𝟭 Type).obj (OverColor.mk ![c1, c2]).left) →
      CoeSort.coe (F.obj { as := (OverColor.mk ![c1, c2]).hom i })) :
    (pairIsoSep F).inv.hom (PiTensorProduct.tprod k fx) = fx (0 : Fin 2) ⊗ₜ fx (1 : Fin 2) := by
  simp [pairIsoSep]
  erw [lift.map_tprod]
  erw [lift.μIso_inv_tprod]
  change (((forgetLiftApp F c1).hom.hom  (((lift.obj F).map (mkIso _).inv).hom
    ((PiTensorProduct.tprod k) fun i =>
    (lift.discreteFunctorMapEqIso F _) (fx ((Hom.toEquiv fin2Iso.hom).symm (Sum.inl i)))))) ⊗ₜ[k]
    (forgetLiftApp F c2).hom.hom ( ((lift.obj F).map (mkIso _).inv).hom ((PiTensorProduct.tprod k)
    fun i =>
    (lift.discreteFunctorMapEqIso F _) (fx ((Hom.toEquiv fin2Iso.hom).symm (Sum.inr i)))))) = _
  congr 1
  · rw [lift.map_tprod]
    rw [forgetLiftApp_hom_hom_apply_eq]
    apply congrArg
    funext x
    match x with
    | (0 : Fin 1) =>
      simp only [mk_hom, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_zero,
        equivToIso_mkIso_inv, Equiv.refl_symm, lift.discreteFunctorMapEqIso, eqToIso_refl,
        Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv, Matrix.cons_val_one,
        Matrix.head_cons, instMonoidalCategoryStruct_tensorObj_left, Functor.id_obj,
        LinearEquiv.ofLinear_apply]
      rfl
  · rw [lift.map_tprod]
    rw [forgetLiftApp_hom_hom_apply_eq]
    apply congrArg
    funext x
    match x with
    | (0 : Fin 1) =>
      simp only [mk_hom, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val_one,
        Matrix.head_cons, equivToIso_mkIso_inv, Equiv.refl_symm, lift.discreteFunctorMapEqIso,
        eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv,
        Matrix.cons_val_zero, instMonoidalCategoryStruct_tensorObj_left, Functor.id_obj,
        LinearEquiv.ofLinear_apply]
      rfl

open HepLean.Fin

/-! TODO: Find a better place for this. -/
lemma pairIsoSep_β_perm_cond (c1 c2 : C) :  ∀ (x : Fin (Nat.succ 0).succ), ![c2, c1] x =
   (![c1, c2] ∘ ⇑(finMapToEquiv ![1, 0] ![1, 0]).symm) x:= by
  intro x
  fin_cases x
  · rfl
  · rfl

lemma pairIsoSep_β {c1 c2 : C} (x : ↑(F.obj { as := c1 } ⊗ F.obj { as := c2 }).V ) :
    (Discrete.pairIsoSep F).hom.hom ((β_ (F.obj (Discrete.mk c1)) _).hom.hom x) =
    ((lift.obj F).map ((OverColor.equivToHomEq (finMapToEquiv ![1, 0] ![1, 0]) (pairIsoSep_β_perm_cond c1 c2)))).hom
    ((Discrete.pairIsoSep F).hom.hom x) := by
  have h1 : (Discrete.pairIsoSep F).hom.hom ∘ₗ (β_ (F.obj (Discrete.mk c1)) (F.obj (Discrete.mk c2))).hom.hom
    = ((lift.obj F).map ((OverColor.equivToHomEq (finMapToEquiv ![1, 0] ![1, 0]) (pairIsoSep_β_perm_cond c1 c2)))).hom ∘ₗ (Discrete.pairIsoSep F).hom.hom := by
    apply TensorProduct.ext'
    intro x y
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Equivalence.symm_inverse,
      Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
      Action.instMonoidalCategory_tensorObj_V, LinearMap.coe_comp, Function.comp_apply, Fin.isValue]
    change (Discrete.pairIsoSep F).hom.hom (y ⊗ₜ x) =  ((lift.obj F).map ((OverColor.equivToHomEq (_) (pairIsoSep_β_perm_cond c1 c2)))).hom
      ((Discrete.pairIsoSep F).hom.hom (x ⊗ₜ y))
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


/-- The isomorphism between
  `F.obj (Discrete.mk c1) ⊗ F.obj (Discrete.mk c2) ⊗ F.obj (Discrete.mk c3)` and
  `(lift.obj F).obj (OverColor.mk ![c1,c2])` formed by the tensorate. -/
def tripleIsoSep {c1 c2 c3 : C} :
    F.obj (Discrete.mk c1) ⊗ F.obj (Discrete.mk c2) ⊗ F.obj (Discrete.mk c3) ≅
    (lift.obj F).obj (OverColor.mk ![c1,c2,c3]) :=
  (whiskerLeftIso (F.obj (Discrete.mk c1)) (pairIsoSep F (c1 := c2) (c2 := c3))).trans <|
  (whiskerRightIso (forgetLiftApp F c1).symm _).trans <|
  ((lift.obj F).μIso _ _).trans <|
  (lift.obj F).mapIso fin3Iso'.symm

lemma tripleIsoSep_tmul {c1 c2 c3 : C} (x : F.obj (Discrete.mk c1)) (y : F.obj (Discrete.mk c2))
    (z : F.obj (Discrete.mk c3)) :
    (tripleIsoSep F).hom.hom (x ⊗ₜ[k] y ⊗ₜ[k] z) = PiTensorProduct.tprod k
      (fun | (0 : Fin 3) => x | (1 : Fin 3) => y | (2 : Fin 3) => z) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Action.instMonoidalCategory_tensorObj_V,
    tripleIsoSep, Functor.mapIso_symm, Iso.trans_hom, whiskerLeftIso_hom, whiskerRightIso_hom,
    Iso.symm_hom, MonoidalFunctor.μIso_hom, Functor.mapIso_inv, Action.comp_hom,
    Action.instMonoidalCategory_whiskerLeft_hom, Action.instMonoidalCategory_whiskerRight_hom,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, ModuleCat.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
    Functor.id_obj, mk_hom]
  erw [pairIsoSep_tmul F y z]
  erw [forgetLiftAppV_symm_apply F c1]
  erw [lift.obj_μ_tprod_tmul F _ _]
  erw [lift.map_tprod]
  apply congrArg
  funext i
  match i with
  | (0 : Fin 3) =>
    simp only [mk_hom, Fin.isValue, Matrix.cons_val_zero, instMonoidalCategoryStruct_tensorObj_left,
      instMonoidalCategoryStruct_tensorObj_hom, lift.discreteFunctorMapEqIso, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv, Functor.id_obj, Nat.reduceAdd,
      Nat.succ_eq_add_one, LinearEquiv.ofLinear_apply]
    rfl
  | (1 : Fin 3) =>
    simp only [mk_hom, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons,
      instMonoidalCategoryStruct_tensorObj_left, instMonoidalCategoryStruct_tensorObj_hom,
      lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom,
      Iso.refl_inv, Functor.id_obj, Nat.reduceAdd, Nat.succ_eq_add_one, LinearEquiv.ofLinear_apply]
    rfl
  | (2 : Fin 3) =>
    simp only [mk_hom, Fin.isValue, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
      instMonoidalCategoryStruct_tensorObj_left, instMonoidalCategoryStruct_tensorObj_hom,
      lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom,
      Iso.refl_inv, Functor.id_obj, LinearEquiv.ofLinear_apply]
    rfl

/-- The functor taking `c` to `F c ⊗ F (τ c)`. -/
def pairτ (τ : C → C) : Discrete C ⥤ Rep k G :=
  F ⊗ ((Discrete.functor (Discrete.mk ∘ τ) : Discrete C ⥤ Discrete C) ⋙ F)

lemma pairτ_tmul {c : C} (x : F.obj (Discrete.mk c))
    (y : ↑(((Action.functorCategoryEquivalence (ModuleCat k) (MonCat.of G)).symm.inverse.obj
    ((Discrete.functor (Discrete.mk ∘ τ) ⋙ F).obj { as := c })).obj PUnit.unit)) (h : c = c1) :
    ((pairτ F τ).map (Discrete.eqToHom h)).hom (x ⊗ₜ[k] y)= ((F.map (Discrete.eqToHom h)).hom x)
    ⊗ₜ[k] ((F.map (Discrete.eqToHom (by simp [h]))).hom y) := by
  rfl

/-- The functor taking `c` to `F (τ c) ⊗ F c`. -/
def τPair (τ : C → C) : Discrete C ⥤ Rep k G :=
  ((Discrete.functor (Discrete.mk ∘ τ) : Discrete C ⥤ Discrete C) ⋙ F) ⊗ F

/-!

## A need lemma about rep

-/

@[simp]
lemma rep_iso_inv_hom_apply (x y : Rep k G) (f : x ≅ y) (i : x) :
    f.inv.hom (f.hom.hom i) = i := by
  change (f.hom ≫ f.inv).hom i = i
  simp

@[simp]
lemma rep_iso_hom_inv_apply (x y : Rep k G) (f : x ≅ y) (i : y) :
    f.hom.hom (f.inv.hom i) = i := by
  change (f.inv ≫ f.hom).hom i = i
  simp

end
end Discrete
end OverColor
end IndexNotation
