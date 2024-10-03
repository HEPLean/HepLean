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

end Hom

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

/-- The corresponding representations associated with a color. -/
def colorToRep (c : Color) : Rep ℂ SL(2, ℂ) :=
  match c with
  | Color.upL => altLeftHanded
  | Color.downL => leftHanded
  | Color.upR => altRightHanded
  | Color.downR => rightHanded

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
    simp only
    ext x
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy])
    intro r x
    simp only [CategoryTheory.Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod,
      _root_.map_smul, Action.id_hom, ModuleCat.id_apply]
    apply congrArg
    rw [colorFun.map']
    erw [colorFun.mapToLinearEquiv'_tprod]
    apply congrArg
    funext i
    rfl
  map_comp {X Y Z} f g := by
    simp only
    ext x
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy])
    intro r x
    simp only [Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod, _root_.map_smul,
      Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply]
    apply congrArg
    rw [colorFun.map', colorFun.map', colorFun.map']
    simp only
    change (colorFun.mapToLinearEquiv' (CategoryTheory.CategoryStruct.comp f g))
      ((PiTensorProduct.tprod ℂ) x) =
      (colorFun.mapToLinearEquiv' g) ((colorFun.mapToLinearEquiv' f) ((PiTensorProduct.tprod ℂ) x))
    rw [colorFun.mapToLinearEquiv'_tprod, colorFun.mapToLinearEquiv'_tprod]
    erw [colorFun.mapToLinearEquiv'_tprod]
    apply congrArg
    funext i
    simp only [colorToRepCongr, Function.comp_apply, Equiv.cast_symm, LinearEquiv.coe_mk,
      Equiv.cast_apply, cast_cast, cast_inj]
    rfl

end
end Fermion
