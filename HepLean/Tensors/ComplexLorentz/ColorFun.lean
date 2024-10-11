/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.ComplexLorentz.Basic
import HepLean.Tensors.OverColor.Basic
import HepLean.Mathematics.PiTensorProduct
/-!

## Monodial functor from color cat.

-/
namespace Fermion

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory

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
@[simps! obj_V_carrier]
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

namespace colorFun

open CategoryTheory
open MonoidalCategory

lemma map_tprod {X Y : OverColor Color} (p : (i : X.left) → (colorToRep (X.hom i)))
    (f : X ⟶ Y) : (colorFun.map f).hom (PiTensorProduct.tprod ℂ p) =
    PiTensorProduct.tprod ℂ fun (i : Y.left) => colorToRepCongr
    (OverColor.Hom.toEquiv_comp_inv_apply f i) (p ((OverColor.Hom.toEquiv f).symm i)) := by
  change (colorFun.map' f).hom ((PiTensorProduct.tprod ℂ) p) = _
  simp [colorFun.map', mapToLinearEquiv']
  erw [LinearEquiv.trans_apply]
  change (PiTensorProduct.congr fun i => colorToRepCongr _)
    ((PiTensorProduct.reindex ℂ (fun x => _) (OverColor.Hom.toEquiv f))
      ((PiTensorProduct.tprod ℂ) p)) = _
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod]

lemma obj_ρ_tprod (f : OverColor Color) (M : SL(2, ℂ))
    (x : (i : f.left) → CoeSort.coe (colorToRep (f.hom i))) :
    (colorFun.obj f).ρ M ((PiTensorProduct.tprod ℂ) x) =
    PiTensorProduct.tprod ℂ (fun i => (colorToRep (f.hom i)).ρ M (x i)) := by
  exact obj'_ρ_tprod _ _ _

@[simp]
lemma obj_ρ_empty (g : SL(2, ℂ)) : (colorFun.obj (𝟙_ (OverColor Color))).ρ g = LinearMap.id := by
  erw [colorFun.obj'_ρ]
  ext x
  refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
    simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
      Function.comp_apply, hy]
    erw [hx, hy]
    rfl
  simp only [OverColor.instMonoidalCategoryStruct_tensorUnit_left, Functor.id_obj,
    OverColor.instMonoidalCategoryStruct_tensorUnit_hom, PiTensorProduct.tprodCoeff_eq_smul_tprod,
    _root_.map_smul, PiTensorProduct.map_tprod, LinearMap.id_coe, id_eq]
  apply congrArg
  apply congrArg
  funext i
  exact Empty.elim i

/-- The unit natural isomorphism. -/
def ε : 𝟙_ (Rep ℂ SL(2, ℂ)) ≅ colorFun.obj (𝟙_ (OverColor Color)) where
  hom := {
    hom := (PiTensorProduct.isEmptyEquiv Empty).symm.toLinearMap
    comm := fun M => by
      refine LinearMap.ext (fun x => ?_)
      simp only [colorFun_obj_V_carrier, OverColor.instMonoidalCategoryStruct_tensorUnit_left,
        OverColor.instMonoidalCategoryStruct_tensorUnit_hom,
        Action.instMonoidalCategory_tensorUnit_V, Action.tensorUnit_ρ', Functor.id_obj,
        Category.id_comp, LinearEquiv.coe_coe]
      erw [obj_ρ_empty M]
      rfl}
  inv := {
    hom := (PiTensorProduct.isEmptyEquiv Empty).toLinearMap
    comm := fun M => by
      refine LinearMap.ext (fun x => ?_)
      simp only [Action.instMonoidalCategory_tensorUnit_V, colorFun_obj_V_carrier,
        OverColor.instMonoidalCategoryStruct_tensorUnit_left,
        OverColor.instMonoidalCategoryStruct_tensorUnit_hom, Functor.id_obj, Action.tensorUnit_ρ']
      erw [obj_ρ_empty M]
      rfl}
  hom_inv_id := by
    ext1
    simp only [Action.instMonoidalCategory_tensorUnit_V, CategoryStruct.comp,
      OverColor.instMonoidalCategoryStruct_tensorUnit_hom,
      OverColor.instMonoidalCategoryStruct_tensorUnit_left, Functor.id_obj, Action.Hom.comp_hom,
      colorFun_obj_V_carrier, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, Action.id_hom]
    rfl
  inv_hom_id := by
    ext1
    simp only [CategoryStruct.comp, OverColor.instMonoidalCategoryStruct_tensorUnit_hom,
      OverColor.instMonoidalCategoryStruct_tensorUnit_left, Functor.id_obj, Action.Hom.comp_hom,
      colorFun_obj_V_carrier, Action.instMonoidalCategory_tensorUnit_V, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, Action.id_hom]
    rfl

/-- An auxillary equivalence, and trivial, of modules needed to define `μModEquiv`. -/
def colorToRepSumEquiv {X Y : OverColor Color} (i : X.left ⊕ Y.left) :
    Sum.elim (fun i => colorToRep (X.hom i)) (fun i => colorToRep (Y.hom i)) i ≃ₗ[ℂ]
    colorToRep (Sum.elim X.hom Y.hom i) :=
  match i with
  | Sum.inl _ => LinearEquiv.refl _ _
  | Sum.inr _ => LinearEquiv.refl _ _

/-- The equivalence of modules corresonding to the tensorate. -/
def μModEquiv (X Y : OverColor Color) :
    (colorFun.obj X ⊗ colorFun.obj Y).V ≃ₗ[ℂ] colorFun.obj (X ⊗ Y) :=
  HepLean.PiTensorProduct.tmulEquiv ≪≫ₗ PiTensorProduct.congr colorToRepSumEquiv

lemma μModEquiv_tmul_tprod {X Y : OverColor Color}(p : (i : X.left) → (colorToRep (X.hom i)))
    (q : (i : Y.left) → (colorToRep (Y.hom i))) :
    (μModEquiv X Y) ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q) =
    (PiTensorProduct.tprod ℂ) fun i =>
    (colorToRepSumEquiv i) (HepLean.PiTensorProduct.elimPureTensor p q i) := by
  rw [μModEquiv]
  simp only [colorFun_obj_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Action.instMonoidalCategory_tensorObj_V,
    Functor.id_obj, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj]
  rw [LinearEquiv.trans_apply]
  erw [HepLean.PiTensorProduct.tmulEquiv_tmul_tprod]
  change (PiTensorProduct.congr colorToRepSumEquiv) ((PiTensorProduct.tprod ℂ)
    (HepLean.PiTensorProduct.elimPureTensor p q)) = _
  rw [PiTensorProduct.congr_tprod]
  rfl

/-- The natural isomorphism corresponding to the tensorate. -/
def μ (X Y : OverColor Color) : colorFun.obj X ⊗ colorFun.obj Y ≅ colorFun.obj (X ⊗ Y) where
  hom := {
    hom := (μModEquiv X Y).toLinearMap
    comm := fun M => by
      refine HepLean.PiTensorProduct.induction_tmul (fun p q => ?_)
      simp only [colorFun_obj_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
        OverColor.instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
        Action.instMonoidalCategory_tensorObj_V, Action.tensor_ρ', LinearMap.coe_comp,
        Function.comp_apply]
      change (μModEquiv X Y) (((((colorFun.obj X).ρ M) (PiTensorProduct.tprod ℂ p)) ⊗ₜ[ℂ]
        (((colorFun.obj Y).ρ M) (PiTensorProduct.tprod ℂ q)))) = ((colorFun.obj (X ⊗ Y)).ρ M)
        ((μModEquiv X Y) ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q))
      rw [μModEquiv_tmul_tprod]
      erw [obj'_ρ_tprod, obj'_ρ_tprod, obj'_ρ_tprod]
      rw [μModEquiv_tmul_tprod]
      apply congrArg
      funext i
      match i with
      | Sum.inl i =>
        rfl
      | Sum.inr i =>
        rfl
  }
  inv := {
    hom := (μModEquiv X Y).symm.toLinearMap
    comm := fun M => by
      simp [CategoryStruct.comp]
      erw [LinearEquiv.eq_comp_toLinearMap_symm,LinearMap.comp_assoc,
      LinearEquiv.toLinearMap_symm_comp_eq]
      refine HepLean.PiTensorProduct.induction_tmul (fun p q => ?_)
      simp only [colorFun_obj_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
        OverColor.instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
        Action.instMonoidalCategory_tensorObj_V, Action.tensor_ρ', LinearMap.coe_comp,
        Function.comp_apply]
      symm
      change (μModEquiv X Y) (((((colorFun.obj X).ρ M) (PiTensorProduct.tprod ℂ p)) ⊗ₜ[ℂ]
        (((colorFun.obj Y).ρ M) (PiTensorProduct.tprod ℂ q)))) = ((colorFun.obj (X ⊗ Y)).ρ M)
        ((μModEquiv X Y) ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q))
      rw [μModEquiv_tmul_tprod]
      erw [obj'_ρ_tprod, obj'_ρ_tprod, obj'_ρ_tprod]
      rw [μModEquiv_tmul_tprod]
      apply congrArg
      funext i
      match i with
      | Sum.inl i =>
        rfl
      | Sum.inr i =>
        rfl}
  hom_inv_id := by
    ext1
    simp only [Action.instMonoidalCategory_tensorObj_V, CategoryStruct.comp, Action.Hom.comp_hom,
      colorFun_obj_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
      OverColor.instMonoidalCategoryStruct_tensorObj_hom, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, Action.id_hom]
    rfl
  inv_hom_id := by
    ext1
    simp only [CategoryStruct.comp, Action.instMonoidalCategory_tensorObj_V, Action.Hom.comp_hom,
      colorFun_obj_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
      OverColor.instMonoidalCategoryStruct_tensorObj_hom, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, Action.id_hom]
    rfl

lemma μ_tmul_tprod {X Y : OverColor Color} (p : (i : X.left) → (colorToRep (X.hom i)))
    (q : (i : Y.left) → (colorToRep (Y.hom i))) :
    (μ X Y).hom.hom ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q) =
    (PiTensorProduct.tprod ℂ) fun i =>
    (colorToRepSumEquiv i) (HepLean.PiTensorProduct.elimPureTensor p q i) := by
  exact μModEquiv_tmul_tprod p q

lemma μ_natural_left {X Y : OverColor Color} (f : X ⟶ Y) (Z : OverColor Color) :
    MonoidalCategory.whiskerRight (colorFun.map f) (colorFun.obj Z) ≫ (μ Y Z).hom =
    (μ X Z).hom ≫ colorFun.map (MonoidalCategory.whiskerRight f Z) := by
  ext1
  refine HepLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [colorFun_obj_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
    Action.Hom.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_whiskerRight_hom, LinearMap.coe_comp, Function.comp_apply]
  change _ = (colorFun.map (MonoidalCategory.whiskerRight f Z)).hom
    ((μ X Z).hom.hom ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q))
  rw [μ_tmul_tprod]
  change _ = (colorFun.map (f ▷ Z)).hom
    ((PiTensorProduct.tprod ℂ) fun i => (colorToRepSumEquiv i)
    (HepLean.PiTensorProduct.elimPureTensor p q i))
  rw [colorFun.map_tprod]
  have h1 : (((colorFun.map f).hom ▷ (colorFun.obj Z).V) ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ]
      (PiTensorProduct.tprod ℂ) q)) = ((colorFun.map f).hom
      ((PiTensorProduct.tprod ℂ) p) ⊗ₜ[ℂ] ((PiTensorProduct.tprod ℂ) q)) := by rfl
  erw [h1]
  rw [colorFun.map_tprod]
  change (μ Y Z).hom.hom (((PiTensorProduct.tprod ℂ) fun i => (colorToRepCongr _)
    (p ((OverColor.Hom.toEquiv f).symm i))) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q) = _
  rw [μ_tmul_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i => rfl
  | Sum.inr i => rfl

lemma μ_natural_right {X Y : OverColor Color} (X' : OverColor Color) (f : X ⟶ Y) :
    MonoidalCategory.whiskerLeft (colorFun.obj X') (colorFun.map f) ≫ (μ X' Y).hom =
    (μ X' X).hom ≫ colorFun.map (MonoidalCategory.whiskerLeft X' f) := by
  ext1
  refine HepLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [colorFun_obj_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
    Action.Hom.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_whiskerLeft_hom, LinearMap.coe_comp, Function.comp_apply]
  change _ = (colorFun.map (X' ◁ f)).hom ((μ X' X).hom.hom
    ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q))
  rw [μ_tmul_tprod]
  change _ = (colorFun.map (X' ◁ f)).hom ((PiTensorProduct.tprod ℂ) fun i =>
    (colorToRepSumEquiv i) (HepLean.PiTensorProduct.elimPureTensor p q i))
  rw [map_tprod]
  have h1 : (((colorFun.obj X').V ◁ (colorFun.map f).hom)
      ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q))
      = ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (colorFun.map f).hom ((PiTensorProduct.tprod ℂ) q)) := by
    rfl
  erw [h1]
  rw [map_tprod]
  change (μ X' Y).hom.hom ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) fun i =>
    (colorToRepCongr _) (q ((OverColor.Hom.toEquiv f).symm i))) = _
  rw [μ_tmul_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i => rfl
  | Sum.inr i => rfl

lemma associativity (X Y Z : OverColor Color) :
    whiskerRight (μ X Y).hom (colorFun.obj Z) ≫
    (μ (X ⊗ Y) Z).hom ≫ colorFun.map (associator X Y Z).hom =
    (associator (colorFun.obj X) (colorFun.obj Y) (colorFun.obj Z)).hom ≫
    whiskerLeft (colorFun.obj X) (μ Y Z).hom ≫ (μ X (Y ⊗ Z)).hom := by
  ext1
  refine HepLean.PiTensorProduct.induction_assoc' (fun p q m => ?_)
  simp only [colorFun_obj_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
    Action.Hom.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_whiskerRight_hom, LinearMap.coe_comp, Function.comp_apply,
    Action.instMonoidalCategory_whiskerLeft_hom, Action.instMonoidalCategory_associator_hom_hom]
  change (colorFun.map (α_ X Y Z).hom).hom ((μ (X ⊗ Y) Z).hom.hom
    ((((μ X Y).hom.hom ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ]
    (PiTensorProduct.tprod ℂ) q)) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) m))) =
    (μ X (Y ⊗ Z)).hom.hom ((((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] ((μ Y Z).hom.hom
    ((PiTensorProduct.tprod ℂ) q ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) m)))))
  rw [μ_tmul_tprod, μ_tmul_tprod]
  change (colorFun.map (α_ X Y Z).hom).hom ((μ (X ⊗ Y) Z).hom.hom
    (((PiTensorProduct.tprod ℂ) fun i => (colorToRepSumEquiv i)
    (HepLean.PiTensorProduct.elimPureTensor p q i)) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) m)) =
    (μ X (Y ⊗ Z)).hom.hom ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) fun i =>
    (colorToRepSumEquiv i) (HepLean.PiTensorProduct.elimPureTensor q m i))
  rw [μ_tmul_tprod, μ_tmul_tprod]
  erw [map_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i => rfl
  | Sum.inr (Sum.inl i) => rfl
  | Sum.inr (Sum.inr i) => rfl

lemma left_unitality (X : OverColor Color) : (leftUnitor (colorFun.obj X)).hom =
    whiskerRight colorFun.ε.hom (colorFun.obj X) ≫
    (μ (𝟙_ (OverColor Color)) X).hom ≫ colorFun.map (leftUnitor X).hom := by
  ext1
  apply HepLean.PiTensorProduct.induction_mod_tmul (fun x q => ?_)
  simp only [colorFun_obj_V_carrier, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Action.instMonoidalCategory_tensorUnit_V, Functor.id_obj,
    Action.instMonoidalCategory_leftUnitor_hom_hom, CategoryStruct.comp, Action.Hom.comp_hom,
    Action.instMonoidalCategory_tensorObj_V, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorUnit_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom,
    Action.instMonoidalCategory_whiskerRight_hom, LinearMap.coe_comp, Function.comp_apply]
  change TensorProduct.lid ℂ (colorFun.obj X) (x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q) =
    (colorFun.map (λ_ X).hom).hom ((μ (𝟙_ (OverColor Color)) X).hom.hom
    ((((PiTensorProduct.isEmptyEquiv Empty).symm x) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q)))
  simp [PiTensorProduct.isEmptyEquiv]
  rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  erw [LinearMap.map_smul, LinearMap.map_smul]
  apply congrArg
  change _ = (colorFun.map (λ_ X).hom).hom ((μ (𝟙_ (OverColor Color)) X).hom.hom
    ((PiTensorProduct.tprod ℂ) _ ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) q))
  rw [μ_tmul_tprod]
  erw [map_tprod]
  rfl

lemma right_unitality (X : OverColor Color) : (MonoidalCategory.rightUnitor (colorFun.obj X)).hom =
    whiskerLeft (colorFun.obj X) ε.hom ≫
    (μ X (𝟙_ (OverColor Color))).hom ≫ colorFun.map (MonoidalCategory.rightUnitor X).hom := by
  ext1
  apply HepLean.PiTensorProduct.induction_tmul_mod (fun p x => ?_)
  simp only [colorFun_obj_V_carrier, Functor.id_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_rightUnitor_hom_hom,
    CategoryStruct.comp, Action.Hom.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorUnit_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Action.instMonoidalCategory_whiskerLeft_hom,
    LinearMap.coe_comp, Function.comp_apply]
  change TensorProduct.rid ℂ (colorFun.obj X) ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] x) =
    (colorFun.map (ρ_ X).hom).hom ((μ X (𝟙_ (OverColor Color))).hom.hom
    ((((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] ((PiTensorProduct.isEmptyEquiv Empty).symm x)))))
  simp [PiTensorProduct.isEmptyEquiv]
  erw [LinearMap.map_smul, LinearMap.map_smul]
  apply congrArg
  change _ = (colorFun.map (ρ_ X).hom).hom ((μ X (𝟙_ (OverColor Color))).hom.hom
    ((PiTensorProduct.tprod ℂ) p ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ) _))
  rw [μ_tmul_tprod]
  erw [map_tprod]
  rfl

end colorFun

/-- The monoidal functor between `OverColor Color` and `Rep ℂ SL(2, ℂ)` taking a map of colors
  to the corresponding tensor product representation. -/
def colorFunMon : MonoidalFunctor (OverColor Color) (Rep ℂ SL(2, ℂ)) where
  toFunctor := colorFun
  ε := colorFun.ε.hom
  μ X Y := (colorFun.μ X Y).hom
  μ_natural_left := colorFun.μ_natural_left
  μ_natural_right := colorFun.μ_natural_right
  associativity := colorFun.associativity
  left_unitality := colorFun.left_unitality
  right_unitality := colorFun.right_unitality

end
end Fermion
