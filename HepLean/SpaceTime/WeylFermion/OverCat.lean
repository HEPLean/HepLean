/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Core
import HepLean.SpaceTime.WeylFermion.Basic
import HepLean.SpaceTime.LorentzVector.Complex
/-!

## Category over color

-/

namespace IndexNotation
open CategoryTheory

/-- The core of the category of Types over C. -/
def OverColor (C : Type) := CategoryTheory.Core (CategoryTheory.Over C)

/-- The instance of `OverColor C` as a groupoid. -/
instance (C : Type) : Groupoid (OverColor C) := coreCategory

namespace OverColor

namespace Hom

variable {C : Type} {f g h : OverColor C}

/-- Given a hom in `OverColor C` the underlying equivalence between types. -/
def toEquiv (m : f ⟶ g) : f.left ≃ g.left where
  toFun := m.hom.left
  invFun := m.inv.left
  left_inv := by
    simpa only [Over.comp_left] using congrFun (congrArg (fun x => x.left) m.hom_inv_id)
  right_inv := by
    simpa only [Over.comp_left] using congrFun (congrArg (fun x => x.left) m.inv_hom_id)

@[simp]
lemma toEquiv_comp (m : f ⟶ g) (n : g ⟶ h) : toEquiv (m ≫ n) = (toEquiv m).trans (toEquiv n) := by
  ext x
  simp [toEquiv]
  rfl

lemma toEquiv_symm_apply (m : f ⟶ g) (i : g.left) :
    f.hom ((toEquiv m).symm i) = g.hom i := by
  simpa [toEquiv, types_comp] using congrFun m.inv.w i

lemma toEquiv_comp_hom (m : f ⟶ g) : g.hom ∘ (toEquiv m) = f.hom := by
  ext x
  simpa [types_comp, toEquiv] using congrFun m.hom.w x

end Hom

instance (C : Type) : MonoidalCategoryStruct (OverColor C) where
  tensorObj f g := Over.mk (Sum.elim f.hom g.hom)
  tensorUnit := Over.mk Empty.elim
  whiskerLeft X Y1 Y2 m := Over.isoMk (Equiv.sumCongr (Equiv.refl X.left) (Hom.toEquiv m)).toIso
    (by
      ext x
      simp only [Functor.id_obj, Functor.const_obj_obj, Over.mk_left, Equiv.toIso_hom, Over.mk_hom,
        types_comp_apply, Equiv.sumCongr_apply, Equiv.coe_refl]
      rw [Sum.elim_map, Hom.toEquiv_comp_hom]
      rfl)
  whiskerRight m X := Over.isoMk (Equiv.sumCongr (Hom.toEquiv m) (Equiv.refl X.left)).toIso
    (by
      ext x
      simp only [Functor.id_obj, Functor.const_obj_obj, Over.mk_left, Equiv.toIso_hom, Over.mk_hom,
        types_comp_apply, Equiv.sumCongr_apply, Equiv.coe_refl]
      rw [Sum.elim_map, Hom.toEquiv_comp_hom]
      rfl)
  associator X Y Z := {
    hom := Over.isoMk (Equiv.sumAssoc X.left Y.left Z.left).toIso (by
      simp only [Functor.id_obj, Over.mk_left, Over.mk_hom, Functor.const_obj_obj, Equiv.sumAssoc,
        Equiv.toIso_hom, Equiv.coe_fn_mk, types_comp]
      ext x
      simp only [Function.comp_apply]
      cases x with
      | inl val =>
        cases val with
        | inl val_1 => simp_all only [Sum.elim_inl]
        | inr val_2 => simp_all only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
      | inr val_1 => simp_all only [Sum.elim_inr, Function.comp_apply]),
    inv := (Over.isoMk (Equiv.sumAssoc X.left Y.left Z.left).toIso (by
      simp only [Functor.id_obj, Over.mk_left, Over.mk_hom, Functor.const_obj_obj, Equiv.sumAssoc,
        Equiv.toIso_hom, Equiv.coe_fn_mk, types_comp]
      ext x
      simp only [Function.comp_apply]
      cases x with
      | inl val =>
        cases val with
        | inl val_1 => simp_all only [Sum.elim_inl]
        | inr val_2 => simp_all only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
      | inr val_1 => simp_all only [Sum.elim_inr, Function.comp_apply])).symm,
    hom_inv_id := by
      apply CategoryTheory.Iso.ext
      erw [CategoryTheory.Iso.trans_hom]
      simp only [Functor.id_obj, Over.mk_left, Over.mk_hom, Iso.symm_hom, Iso.hom_inv_id]
      rfl,
    inv_hom_id := by
      apply CategoryTheory.Iso.ext
      erw [CategoryTheory.Iso.trans_hom]
      simp only [Functor.id_obj, Over.mk_left, Over.mk_hom, Iso.symm_hom, Iso.inv_hom_id]
      rfl}
  leftUnitor X := {
    hom := Over.isoMk (Equiv.emptySum Empty X.left).toIso
    inv := (Over.isoMk (Equiv.emptySum Empty X.left).toIso).symm
    hom_inv_id := by
      apply CategoryTheory.Iso.ext
      erw [CategoryTheory.Iso.trans_hom]
      simp only [Functor.id_obj, Over.mk_left, Over.mk_hom, Iso.symm_hom, Iso.hom_inv_id]
      rfl,
    inv_hom_id := by
      apply CategoryTheory.Iso.ext
      erw [CategoryTheory.Iso.trans_hom]}
  rightUnitor X := {
    hom := Over.isoMk (Equiv.sumEmpty X.left Empty).toIso
    inv := (Over.isoMk (Equiv.sumEmpty X.left Empty).toIso).symm
    hom_inv_id := by
      apply CategoryTheory.Iso.ext
      erw [CategoryTheory.Iso.trans_hom]
      simp only [Functor.id_obj, Over.mk_left, Over.mk_hom, Iso.symm_hom, Iso.hom_inv_id]
      rfl,
    inv_hom_id := by
      apply CategoryTheory.Iso.ext
      erw [CategoryTheory.Iso.trans_hom]}

end OverColor

end IndexNotation

namespace Fermion

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory

/-- The colors associated with complex representations of SL(2, ℂ) of intrest to physics. -/
inductive Color
  | upL : Color
  | downL : Color
  | upR : Color
  | downR : Color
  | up : Color
  | down : Color

/-- The corresponding representations associated with a color. -/
def colorToRep (c : Color) : Rep ℂ SL(2, ℂ) :=
  match c with
  | Color.upL => altLeftHanded
  | Color.downL => leftHanded
  | Color.upR => altRightHanded
  | Color.downR => rightHanded
  | Color.up => Lorentz.complexContr
  | Color.down => Lorentz.complexCo

/-- The linear equivalence between `colorToRep c1` and `colorToRep c2` when `c1 = c2`. -/
def colorToRepCongr {c1 c2 : Color} (h : c1 = c2) : colorToRep c1 ≃ₗ[ℂ] colorToRep c2 where
  toFun := Equiv.cast (congrArg (CoeSort.coe ∘ colorToRep) h)
  invFun := (Equiv.cast (congrArg (CoeSort.coe ∘ colorToRep) h)).symm
  map_add' x y := by
    subst h
    rfl
  map_smul' x y := by
    subst h
    rfl
  left_inv x := Equiv.symm_apply_apply (Equiv.cast (congrArg (CoeSort.coe ∘ colorToRep) h)) x
  right_inv x := Equiv.apply_symm_apply (Equiv.cast (congrArg (CoeSort.coe ∘ colorToRep) h)) x

lemma colorToRepCongr_comm_ρ {c1 c2 : Color} (h : c1 = c2) (M : SL(2, ℂ)) (x : (colorToRep c1)) :
    (colorToRepCongr h) ((colorToRep c1).ρ M x) = (colorToRep c2).ρ M ((colorToRepCongr h) x) := by
  subst h
  rfl

namespace colorFun

/-- Given a object in `OverColor Color` the correpsonding tensor product of representations. -/
def obj' (f : OverColor Color) : Rep ℂ SL(2, ℂ) := Rep.of {
  toFun := fun M => PiTensorProduct.map (fun x => (colorToRep (f.hom x)).ρ M),
  map_one' := by
    simp
  map_mul' := fun M N => by
    simp only [CategoryTheory.Functor.id_obj, _root_.map_mul]
    ext x : 2
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.mul_apply]}

lemma obj'_ρ (f : OverColor Color) (M : SL(2, ℂ)) : (obj' f).ρ M =
    PiTensorProduct.map (fun x => (colorToRep (f.hom x)).ρ M) := rfl

lemma obj'_ρ_tprod (f : OverColor Color) (M : SL(2, ℂ))
    (x : (i : f.left) → CoeSort.coe (colorToRep (f.hom i))) :
    (obj' f).ρ M ((PiTensorProduct.tprod ℂ) x) =
    PiTensorProduct.tprod ℂ (fun i => (colorToRep (f.hom i)).ρ M (x i)) := by
  rw [obj'_ρ]
  change (PiTensorProduct.map fun x => (colorToRep (f.hom x)).ρ M) ((PiTensorProduct.tprod ℂ) x) =
    (PiTensorProduct.tprod ℂ) fun i => ((colorToRep (f.hom i)).ρ M) (x i)
  rw [PiTensorProduct.map_tprod]

/-- Given a morphism in `OverColor Color` the corresopnding linear equivalence between `obj' _`
  induced by reindexing. -/
def mapToLinearEquiv' {f g : OverColor Color} (m : f ⟶ g) : (obj' f).V ≃ₗ[ℂ] (obj' g).V :=
  (PiTensorProduct.reindex ℂ (fun x => colorToRep (f.hom x)) (OverColor.Hom.toEquiv m)).trans
  (PiTensorProduct.congr (fun i => colorToRepCongr (OverColor.Hom.toEquiv_symm_apply m i)))

lemma mapToLinearEquiv'_tprod {f g : OverColor Color} (m : f ⟶ g)
    (x : (i : f.left) → CoeSort.coe (colorToRep (f.hom i))) :
    mapToLinearEquiv' m (PiTensorProduct.tprod ℂ x) =
    PiTensorProduct.tprod ℂ (fun i => (colorToRepCongr (OverColor.Hom.toEquiv_symm_apply m i))
    (x ((OverColor.Hom.toEquiv m).symm i))) := by
  rw [mapToLinearEquiv']
  simp only [CategoryTheory.Functor.id_obj, LinearEquiv.trans_apply]
  change (PiTensorProduct.congr fun i => colorToRepCongr _)
    ((PiTensorProduct.reindex ℂ (fun x => CoeSort.coe (colorToRep (f.hom x)))
    (OverColor.Hom.toEquiv m)) ((PiTensorProduct.tprod ℂ) x)) = _
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod]
  rfl

/-- Given a morphism in `OverColor Color` the corresopnding map of representations induced by
  reindexing. -/
def map' {f g : OverColor Color} (m : f ⟶ g) : obj' f ⟶ obj' g where
  hom := (mapToLinearEquiv' m).toLinearMap
  comm M := by
    ext x : 2
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy])
    intro r x
    simp only [CategoryTheory.Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod,
      _root_.map_smul, ModuleCat.coe_comp, Function.comp_apply]
    apply congrArg
    change (mapToLinearEquiv' m) (((obj' f).ρ M) ((PiTensorProduct.tprod ℂ) x)) =
      ((obj' g).ρ M) ((mapToLinearEquiv' m) ((PiTensorProduct.tprod ℂ) x))
    rw [mapToLinearEquiv'_tprod, obj'_ρ_tprod]
    erw [mapToLinearEquiv'_tprod, obj'_ρ_tprod]
    apply congrArg
    funext i
    rw [colorToRepCongr_comm_ρ]

end colorFun

/-- The functor between `OverColor Color` and `Rep ℂ SL(2, ℂ)` taking a map of colors
  to the corresponding tensor product representation. -/
def colorFun : OverColor Color ⥤ Rep ℂ SL(2, ℂ) where
  obj := colorFun.obj'
  map := colorFun.map'
  map_id f := by
    ext x
    refine PiTensorProduct.induction_on' x (fun r x => ?_) (fun x y hx hy => by
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy])
    simp only [CategoryTheory.Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod,
      _root_.map_smul, Action.id_hom, ModuleCat.id_apply]
    apply congrArg
    erw [colorFun.mapToLinearEquiv'_tprod]
    exact congrArg _ (funext (fun i => rfl))
  map_comp {X Y Z} f g := by
    ext x
    refine PiTensorProduct.induction_on' x (fun r x => ?_) (fun x y hx hy => by
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy])
    simp only [Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod, _root_.map_smul,
      Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply]
    apply congrArg
    rw [colorFun.map', colorFun.map', colorFun.map']
    change (colorFun.mapToLinearEquiv' (CategoryTheory.CategoryStruct.comp f g))
      ((PiTensorProduct.tprod ℂ) x) =
      (colorFun.mapToLinearEquiv' g) ((colorFun.mapToLinearEquiv' f) ((PiTensorProduct.tprod ℂ) x))
    rw [colorFun.mapToLinearEquiv'_tprod, colorFun.mapToLinearEquiv'_tprod]
    erw [colorFun.mapToLinearEquiv'_tprod]
    refine congrArg _ (funext (fun i => ?_))
    simp only [colorToRepCongr, Function.comp_apply, Equiv.cast_symm, LinearEquiv.coe_mk,
      Equiv.cast_apply, cast_cast, cast_inj]
    rfl

end
end Fermion
