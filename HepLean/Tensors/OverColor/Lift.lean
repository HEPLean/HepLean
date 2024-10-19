/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Basic
import HepLean.Mathematics.PiTensorProduct
/-!

## Lifting functors.

There is a functor from functors `Discrete C ⥤ Rep k G` to
monoidal functors `MonoidalFunctor (OverColor C) (Rep k G)`.
We call this functor `lift`. It is a lift in the
sense that it is a section of the forgetful functor
`MonoidalFunctor (OverColor C) (Rep k G) ⥤ (Discrete C ⥤ Rep k G)`.

Functors in `Discrete C ⥤ Rep k G` form the basic building blocks of tensor structures.
The fact that they extend to monoidal functors `OverColor C ⥤ Rep k G` allows us to
interfact more generally with tensors.

-/

namespace IndexNotation
namespace OverColor

open CategoryTheory
open MonoidalCategory
open TensorProduct
variable {C k : Type} [CommRing k] {G : Type} [Group G]

namespace Discrete

/-- Takes a homorphism in `Discrete C` to an isomorphism built on the same objects. -/
def homToIso {c1 c2 : Discrete C} (h : c1 ⟶ c2) : c1 ≅ c2 :=
  Discrete.eqToIso (Discrete.eq_of_hom h)

end Discrete

namespace lift
noncomputable section
variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')

/-- Takes a homorphisms of `Discrete C` to an isomorphism `F.obj c1 ≅ F.obj c2`. -/
def discreteFunctorMapIso {c1 c2 : Discrete C} (h : c1 ⟶ c2) :
    F.obj c1 ≅ F.obj c2 := F.mapIso (Discrete.homToIso h)

lemma discreteFun_hom_trans {c1 c2 c3 : Discrete C} (h1 : c1 = c2) (h2 : c2 = c3)
    (v : F.obj c1) : (F.map (eqToHom h2)).hom ((F.map (eqToHom h1)).hom v)
    = (F.map (eqToHom (h1.trans h2))).hom v := by
  subst h2 h1
  simp_all only [eqToHom_refl, Discrete.functor_map_id, Action.id_hom, ModuleCat.id_apply]

/-- The linear equivalence between `(F.obj c1).V ≃ₗ[k] (F.obj c2).V` induced by an equality of
  `c1` and `c2`. -/
def discreteFunctorMapEqIso {c1 c2 : Discrete C} (h : c1.as = c2.as) :
    (F.obj c1).V ≃ₗ[k] (F.obj c2).V := LinearEquiv.ofLinear
  (F.mapIso (Discrete.eqToIso h)).hom.hom (F.mapIso (Discrete.eqToIso h)).inv.hom
  (by
    ext x : 2
    simp only [Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv, eqToIso.inv, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq]
    have h1 := congrArg (fun f => f.hom) (F.mapIso (Discrete.eqToIso h)).inv_hom_id
    rw [ModuleCat.ext_iff] at h1
    have h1x := h1 x
    simp only [CategoryStruct.comp] at h1x
    simpa using h1x)
  (by
    ext x : 2
    simp only [Functor.mapIso_inv, eqToIso.inv, Functor.mapIso_hom, eqToIso.hom, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq]
    have h1 := congrArg (fun f => f.hom) (F.mapIso (Discrete.eqToIso h)).hom_inv_id
    rw [ModuleCat.ext_iff] at h1
    have h1x := h1 x
    simp only [CategoryStruct.comp] at h1x
    simpa using h1x)

lemma discreteFunctorMapEqIso_comm_ρ {c1 c2 : Discrete C} (h : c1.as = c2.as) (M : G)
    (x : F.obj c1) : discreteFunctorMapEqIso F h ((F.obj c1).ρ M x) =
    (F.obj c2).ρ M (discreteFunctorMapEqIso F h x) := by
  have h1 := Discrete.ext_iff.mpr h
  subst h1
  simp only [discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom,
    Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
  rfl

/-- Given a object in `OverColor Color` the correpsonding tensor product of representations. -/
def objObj' (f : OverColor C) : Rep k G := Rep.of {
  toFun := fun M => PiTensorProduct.map (fun x =>
    (F.obj (Discrete.mk (f.hom x))).ρ M),
  map_one' := by
    simp only [Functor.id_obj, map_one, PiTensorProduct.map_one]
  map_mul' := fun M N => by
    simp only [CategoryTheory.Functor.id_obj, _root_.map_mul]
    ext x : 2
    simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.mul_apply]}

lemma objObj'_ρ (f : OverColor C) (M : G) : (objObj' F f).ρ M =
    PiTensorProduct.map (fun x => (F.obj (Discrete.mk (f.hom x))).ρ M) := rfl

lemma objObj'_ρ_tprod (f : OverColor C) (M : G) (x : (i : f.left) → F.obj (Discrete.mk (f.hom i))) :
    (objObj' F f).ρ M (PiTensorProduct.tprod k x) =
    PiTensorProduct.tprod k fun i => (F.obj (Discrete.mk (f.hom i))).ρ M (x i) := by
  rw [objObj'_ρ]
  change (PiTensorProduct.map fun x => _) ((PiTensorProduct.tprod k) x) =_
  rw [PiTensorProduct.map_tprod]
  rfl

@[simp]
lemma objObj'_ρ_empty (g : G) : (objObj' F (𝟙_ (OverColor C))).ρ g = LinearMap.id := by
  erw [objObj'_ρ]
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

open TensorProduct in
@[simp]
lemma objObj'_V_carrier (f : OverColor C) :
    (objObj' F f).V = ⨂[k] (i : f.left), F.obj (Discrete.mk (f.hom i)) := rfl

/-- Given a morphism in `OverColor C` the corresopnding linear equivalence between `obj' _`
  induced by reindexing. -/
def mapToLinearEquiv' {f g : OverColor C} (m : f ⟶ g) : (objObj' F f).V ≃ₗ[k] (objObj' F g).V :=
  (PiTensorProduct.reindex k (fun x => (F.obj (Discrete.mk (f.hom x))))
    (OverColor.Hom.toEquiv m)).trans
  (PiTensorProduct.congr (fun i =>
    discreteFunctorMapEqIso F (Hom.toEquiv_symm_apply m i)))

lemma mapToLinearEquiv'_tprod {f g : OverColor C} (m : f ⟶ g)
    (x : (i : f.left) → (F.obj (Discrete.mk (f.hom i)))) :
    mapToLinearEquiv' F m (PiTensorProduct.tprod k x) =
    PiTensorProduct.tprod k (fun i => (discreteFunctorMapEqIso F (Hom.toEquiv_symm_apply m i))
    (x ((OverColor.Hom.toEquiv m).symm i))) := by
  rw [mapToLinearEquiv']
  simp only [CategoryTheory.Functor.id_obj, LinearEquiv.trans_apply]
  change (PiTensorProduct.congr fun i => _) ((PiTensorProduct.reindex k
    (fun x => ↑(F.obj (Discrete.mk (f.hom x))).V) (OverColor.Hom.toEquiv m))
    ((PiTensorProduct.tprod k) x)) = _
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod]
  rfl

/-- Given a morphism in `OverColor C` the corresopnding map of representations induced by
  reindexing. -/
def objMap' {f g : OverColor C} (m : f ⟶ g) : objObj' F f ⟶ objObj' F g where
  hom := (mapToLinearEquiv' F m).toLinearMap
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
    change (mapToLinearEquiv' F m) (((objObj' F f).ρ M) ((PiTensorProduct.tprod k) x)) =
      ((objObj' F g).ρ M) ((mapToLinearEquiv' F m) ((PiTensorProduct.tprod k) x))
    rw [mapToLinearEquiv'_tprod, objObj'_ρ_tprod]
    erw [mapToLinearEquiv'_tprod, objObj'_ρ_tprod]
    apply congrArg
    funext i
    rw [discreteFunctorMapEqIso_comm_ρ]

lemma objMap'_tprod {X Y : OverColor C} (p : (i : X.left) → F.obj (Discrete.mk (X.hom i)))
    (f : X ⟶ Y) : (objMap' F f).hom (PiTensorProduct.tprod k p) =
    PiTensorProduct.tprod k fun (i : Y.left) => discreteFunctorMapEqIso F
    (OverColor.Hom.toEquiv_comp_inv_apply f i) (p ((OverColor.Hom.toEquiv f).symm i)) := by
  change (objMap' F f).hom (PiTensorProduct.tprod k p) = _
  simp only [objMap', mapToLinearEquiv', Functor.id_obj]
  erw [LinearEquiv.trans_apply]
  change (PiTensorProduct.congr fun i => discreteFunctorMapEqIso F _)
    ((PiTensorProduct.reindex k (fun x => _) (OverColor.Hom.toEquiv f))
      ((PiTensorProduct.tprod k) p)) = _
  rw [PiTensorProduct.reindex_tprod]
  exact PiTensorProduct.congr_tprod
    (fun i => discreteFunctorMapEqIso F (Hom.toEquiv_symm_apply f i))
    fun i => p ((Hom.toEquiv f).symm i)

/-- The unit natural isomorphism. -/
def ε : 𝟙_ (Rep k G) ≅ objObj' F (𝟙_ (OverColor C)) :=
  Action.mkIso (PiTensorProduct.isEmptyEquiv Empty).symm.toModuleIso
  (by
    intro g
    refine LinearMap.ext (fun x => ?_)
    simp only [objObj'_V_carrier, OverColor.instMonoidalCategoryStruct_tensorUnit_left,
      OverColor.instMonoidalCategoryStruct_tensorUnit_hom,
      Action.instMonoidalCategory_tensorUnit_V, Action.tensorUnit_ρ', Functor.id_obj,
      Category.id_comp, LinearEquiv.coe_coe]
    erw [objObj'_ρ_empty F g]
    rfl)

/-- An auxillary equivalence, and trivial, of modules needed to define `μModEquiv`. -/
def discreteSumEquiv {X Y : OverColor C} (i : X.left ⊕ Y.left) :
    Sum.elim (fun i => F.obj (Discrete.mk (X.hom i)))
    (fun i => F.obj (Discrete.mk (Y.hom i))) i ≃ₗ[k] F.obj (Discrete.mk ((X ⊗ Y).hom i)) :=
  match i with
  | Sum.inl _ => LinearEquiv.refl _ _
  | Sum.inr _ => LinearEquiv.refl _ _

/-- The equivalence of modules corresonding to the tensorate. -/
def μModEquiv (X Y : OverColor C) :
    (objObj' F X ⊗ objObj' F Y).V ≃ₗ[k] objObj' F (X ⊗ Y) :=
  HepLean.PiTensorProduct.tmulEquiv ≪≫ₗ PiTensorProduct.congr (discreteSumEquiv F)

lemma μModEquiv_tmul_tprod {X Y : OverColor C}
    (p : (i : X.left) → F.obj (Discrete.mk (X.hom i)))
    (q : (i : Y.left) → F.obj (Discrete.mk (Y.hom i))) :
    μModEquiv F X Y (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    PiTensorProduct.tprod k fun i =>
    (discreteSumEquiv F i) (HepLean.PiTensorProduct.elimPureTensor p q i) := by
  rw [μModEquiv]
  simp only [objObj'_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Action.instMonoidalCategory_tensorObj_V,
    Functor.id_obj, Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj]
  rw [LinearEquiv.trans_apply]
  erw [HepLean.PiTensorProduct.tmulEquiv_tmul_tprod]
  change PiTensorProduct.congr (discreteSumEquiv F)
    (PiTensorProduct.tprod k (HepLean.PiTensorProduct.elimPureTensor p q)) = _
  rw [PiTensorProduct.congr_tprod]
  rfl

/-- The natural isomorphism corresponding to the tensorate. -/
def μ (X Y : OverColor C) : objObj' F X ⊗ objObj' F Y ≅ objObj' F (X ⊗ Y) :=
  Action.mkIso (μModEquiv F X Y).toModuleIso
  (fun M => by
    refine HepLean.PiTensorProduct.induction_tmul (fun p q => ?_)
    simp only [objObj'_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
      OverColor.instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
      Action.instMonoidalCategory_tensorObj_V, Action.tensor_ρ', LinearMap.coe_comp,
      Function.comp_apply]
    change (μModEquiv F X Y)
      ((objObj' F X).ρ M (PiTensorProduct.tprod k p) ⊗ₜ[k]
      (objObj' F Y).ρ M (PiTensorProduct.tprod k q)) = (objObj' F (X ⊗ Y)).ρ M
      (μModEquiv F X Y (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q))
    rw [μModEquiv_tmul_tprod]
    erw [objObj'_ρ_tprod, objObj'_ρ_tprod, objObj'_ρ_tprod]
    rw [μModEquiv_tmul_tprod]
    apply congrArg
    funext i
    match i with
    | Sum.inl i =>
      rfl
    | Sum.inr i =>
      rfl)

lemma μ_tmul_tprod {X Y : OverColor C} (p : (i : X.left) → F.obj (Discrete.mk <| X.hom i))
    (q : (i : Y.left) → (F.obj <| Discrete.mk (Y.hom i))) :
    (μ F X Y).hom.hom (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (HepLean.PiTensorProduct.elimPureTensor p q i) := by
  exact μModEquiv_tmul_tprod F p q

lemma μ_natural_left {X Y : OverColor C} (f : X ⟶ Y) (Z : OverColor C) :
    MonoidalCategory.whiskerRight (objMap' F f) (objObj' F Z) ≫ (μ F Y Z).hom =
    (μ F X Z).hom ≫ objMap' F (MonoidalCategory.whiskerRight f Z) := by
  ext1
  refine HepLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [objObj'_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
    Action.Hom.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_whiskerRight_hom, LinearMap.coe_comp, Function.comp_apply]
  change _ = (objMap' F (MonoidalCategory.whiskerRight f Z)).hom
    ((μ F X Z).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) q))
  rw [μ_tmul_tprod]
  change _ = (objMap' F (f ▷ Z)).hom
    (PiTensorProduct.tprod k fun i => discreteSumEquiv F i
    (HepLean.PiTensorProduct.elimPureTensor p q i))
  rw [objMap'_tprod]
  have h1 : (((objMap' F f).hom ▷ (objObj' F Z).V) (PiTensorProduct.tprod k p ⊗ₜ[k]
      PiTensorProduct.tprod k q)) = ((objMap' F f).hom
      ((PiTensorProduct.tprod k) p) ⊗ₜ[k] ((PiTensorProduct.tprod k) q)) := by rfl
  erw [h1]
  rw [objMap'_tprod]
  change (μ F Y Z).hom.hom (((PiTensorProduct.tprod k) fun i => (discreteFunctorMapEqIso F _)
    (p ((OverColor.Hom.toEquiv f).symm i))) ⊗ₜ[k] (PiTensorProduct.tprod k) q) = _
  rw [μ_tmul_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i => rfl
  | Sum.inr i =>
    simp only [instMonoidalCategoryStruct_tensorObj_hom, Sum.elim_inr, Functor.id_obj,
      discreteSumEquiv, Hom.toEquiv, Equiv.coe_fn_symm_mk, discreteFunctorMapEqIso,
      Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv, eqToIso.inv, LinearEquiv.ofLinear_apply,
      LinearEquiv.refl_apply, instMonoidalCategoryStruct_tensorObj_left,
      instMonoidalCategoryStruct_whiskerRight_inv_left, Sum.map_inr, id_eq, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv]
    rfl

lemma μ_natural_right {X Y : OverColor C} (X' : OverColor C) (f : X ⟶ Y) :
    MonoidalCategory.whiskerLeft (objObj' F X') (objMap' F f) ≫ (μ F X' Y).hom =
    (μ F X' X).hom ≫ objMap' F (MonoidalCategory.whiskerLeft X' f) := by
  ext1
  refine HepLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [objObj'_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
    Action.Hom.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_whiskerLeft_hom, LinearMap.coe_comp, Function.comp_apply]
  change _ = (objMap' F (X' ◁ f)).hom ((μ F X' X).hom.hom
    ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) q))
  rw [μ_tmul_tprod]
  change _ = (objMap' F (X' ◁ f)).hom ((PiTensorProduct.tprod k) fun i =>
    (discreteSumEquiv F i) (HepLean.PiTensorProduct.elimPureTensor p q i))
  rw [objMap'_tprod]
  have h1 : (((objObj' F X').V ◁ (objMap' F f).hom)
      ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) q))
      = ((PiTensorProduct.tprod k) p ⊗ₜ[k] (objMap' F f).hom ((PiTensorProduct.tprod k) q)) := by
    rfl
  erw [h1]
  rw [objMap'_tprod]
  change (μ F X' Y).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) fun i =>
    (discreteFunctorMapEqIso F _) (q ((OverColor.Hom.toEquiv f).symm i))) = _
  rw [μ_tmul_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i =>
    simp only [instMonoidalCategoryStruct_tensorObj_hom, Sum.elim_inl, Functor.id_obj,
      discreteFunctorMapEqIso, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv, eqToIso.inv,
      LinearEquiv.ofLinear_apply, instMonoidalCategoryStruct_tensorObj_left, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv]
    rfl
  | Sum.inr i => rfl

lemma associativity (X Y Z : OverColor C) :
    whiskerRight (μ F X Y).hom (objObj' F Z) ≫
    (μ F (X ⊗ Y) Z).hom ≫ objMap' F (associator X Y Z).hom =
    (associator (objObj' F X) (objObj' F Y) (objObj' F Z)).hom ≫
    whiskerLeft (objObj' F X) (μ F Y Z).hom ≫ (μ F X (Y ⊗ Z)).hom := by
  ext1
  refine HepLean.PiTensorProduct.induction_assoc' (fun p q m => ?_)
  simp only [objObj'_V_carrier, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
    Action.Hom.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    Action.instMonoidalCategory_whiskerRight_hom, LinearMap.coe_comp, Function.comp_apply,
    Action.instMonoidalCategory_whiskerLeft_hom, Action.instMonoidalCategory_associator_hom_hom]
  change (objMap' F (α_ X Y Z).hom).hom ((μ F (X ⊗ Y) Z).hom.hom
    ((((μ F X Y).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k]
    (PiTensorProduct.tprod k) q)) ⊗ₜ[k] (PiTensorProduct.tprod k) m))) =
    (μ F X (Y ⊗ Z)).hom.hom ((((PiTensorProduct.tprod k) p ⊗ₜ[k] ((μ F Y Z).hom.hom
    ((PiTensorProduct.tprod k) q ⊗ₜ[k] (PiTensorProduct.tprod k) m)))))
  rw [μ_tmul_tprod, μ_tmul_tprod]
  change (objMap' F (α_ X Y Z).hom).hom ((μ F (X ⊗ Y) Z).hom.hom
    (((PiTensorProduct.tprod k) fun i => (discreteSumEquiv F i)
    (HepLean.PiTensorProduct.elimPureTensor p q i)) ⊗ₜ[k] (PiTensorProduct.tprod k) m)) =
    (μ F X (Y ⊗ Z)).hom.hom ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) fun i =>
    (discreteSumEquiv F i) (HepLean.PiTensorProduct.elimPureTensor q m i))
  rw [μ_tmul_tprod, μ_tmul_tprod]
  erw [objMap'_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inl i =>
    simp only [Functor.id_obj, instMonoidalCategoryStruct_tensorObj_left,
      instMonoidalCategoryStruct_tensorObj_hom, Sum.elim_inl, discreteFunctorMapEqIso, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
    rfl
  | Sum.inr (Sum.inl i) =>
    simp only [Functor.id_obj, instMonoidalCategoryStruct_tensorObj_left,
      instMonoidalCategoryStruct_tensorObj_hom, Sum.elim_inr, Sum.elim_inl, discreteFunctorMapEqIso,
      eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv,
      LinearEquiv.ofLinear_apply]
    rfl
  | Sum.inr (Sum.inr i) =>
    simp only [Functor.id_obj, instMonoidalCategoryStruct_tensorObj_left,
      instMonoidalCategoryStruct_tensorObj_hom, Sum.elim_inr, discreteFunctorMapEqIso, eqToIso_refl,
      Functor.mapIso_refl, Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
    rfl

lemma left_unitality (X : OverColor C) : (leftUnitor (objObj' F X)).hom =
    whiskerRight (ε F).hom (objObj' F X) ≫
    (μ F (𝟙_ (OverColor C)) X).hom ≫ objMap' F (leftUnitor X).hom := by
  ext1
  apply HepLean.PiTensorProduct.induction_mod_tmul (fun x q => ?_)
  simp only [objObj'_V_carrier, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Action.instMonoidalCategory_tensorUnit_V, Functor.id_obj,
    Action.instMonoidalCategory_leftUnitor_hom_hom, CategoryStruct.comp, Action.Hom.comp_hom,
    Action.instMonoidalCategory_tensorObj_V, OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorUnit_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom,
    Action.instMonoidalCategory_whiskerRight_hom, LinearMap.coe_comp, Function.comp_apply]
  change TensorProduct.lid k (objObj' F X) (x ⊗ₜ[k] (PiTensorProduct.tprod k) q) =
    (objMap' F (λ_ X).hom).hom ((μ F (𝟙_ (OverColor C)) X).hom.hom
    ((((PiTensorProduct.isEmptyEquiv Empty).symm x) ⊗ₜ[k] (PiTensorProduct.tprod k) q)))
  simp only [Functor.id_obj, lid_tmul, objObj'_V_carrier,
    OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorUnit_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj,
    OverColor.instMonoidalCategoryStruct_tensorUnit_hom, PiTensorProduct.isEmptyEquiv,
    LinearEquiv.coe_symm_mk]
  rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  erw [LinearMap.map_smul, LinearMap.map_smul]
  apply congrArg
  change _ = (objMap' F (λ_ X).hom).hom ((μ F (𝟙_ (OverColor C)) X).hom.hom
    ((PiTensorProduct.tprod k) _ ⊗ₜ[k] (PiTensorProduct.tprod k) q))
  rw [μ_tmul_tprod]
  erw [objMap'_tprod]
  simp only [objObj'_V_carrier, instMonoidalCategoryStruct_tensorObj_left,
    instMonoidalCategoryStruct_tensorUnit_left, instMonoidalCategoryStruct_tensorObj_hom,
    discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom,
    Iso.refl_inv, Functor.id_obj, instMonoidalCategoryStruct_tensorUnit_hom,
    LinearEquiv.ofLinear_apply]
  rfl

lemma right_unitality (X : OverColor C) : (rightUnitor (objObj' F X)).hom =
    whiskerLeft (objObj' F X) (ε F).hom ≫
    (μ F X (𝟙_ (OverColor C))).hom ≫ objMap' F (rightUnitor X).hom := by
  ext1
  apply HepLean.PiTensorProduct.induction_tmul_mod (fun p x => ?_)
  simp only [objObj'_ρ, Functor.id_obj, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_rightUnitor_hom_hom,
    CategoryStruct.comp, Action.Hom.comp_hom, Action.instMonoidalCategory_tensorObj_V,
    OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorUnit_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Action.instMonoidalCategory_whiskerLeft_hom,
    LinearMap.coe_comp, Function.comp_apply]
  change TensorProduct.rid k (objObj' F X) ((PiTensorProduct.tprod k) p ⊗ₜ[k] x) =
    (objMap' F (ρ_ X).hom).hom ((μ F X (𝟙_ (OverColor C))).hom.hom
    ((((PiTensorProduct.tprod k) p ⊗ₜ[k] ((PiTensorProduct.isEmptyEquiv Empty).symm x)))))
  simp only [Functor.id_obj, rid_tmul, objObj'_ρ,
    OverColor.instMonoidalCategoryStruct_tensorObj_left,
    OverColor.instMonoidalCategoryStruct_tensorUnit_left,
    OverColor.instMonoidalCategoryStruct_tensorObj_hom, Action.instMonoidalCategory_tensorObj_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj,
    OverColor.instMonoidalCategoryStruct_tensorUnit_hom, PiTensorProduct.isEmptyEquiv,
    LinearEquiv.coe_symm_mk, tmul_smul]
  erw [LinearMap.map_smul, LinearMap.map_smul]
  apply congrArg
  change _ = (objMap' F (ρ_ X).hom).hom ((μ F X (𝟙_ (OverColor C))).hom.hom
    ((PiTensorProduct.tprod k) p ⊗ₜ[k] (PiTensorProduct.tprod k) _))
  rw [μ_tmul_tprod]
  erw [objMap'_tprod]
  simp only [objObj'_V_carrier, instMonoidalCategoryStruct_tensorObj_left,
    instMonoidalCategoryStruct_tensorUnit_left, instMonoidalCategoryStruct_tensorObj_hom,
    discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom, Action.id_hom,
    Iso.refl_inv, Functor.id_obj, instMonoidalCategoryStruct_tensorUnit_hom,
    LinearEquiv.ofLinear_apply]
  rfl

/-- The `MonoidalFunctor (OverColor C) (Rep k G)` from a functor `Discrete C ⥤ Rep k G`. -/
def obj' : MonoidalFunctor (OverColor C) (Rep k G) where
  obj := objObj' F
  map := objMap' F
  ε := (ε F).hom
  μ X Y := (μ F X Y).hom
  map_id f := by
    ext x
    refine PiTensorProduct.induction_on' x (fun r x => ?_) (fun x y hx hy => by
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy])
    simp only [CategoryTheory.Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod,
      _root_.map_smul, Action.id_hom, ModuleCat.id_apply]
    apply congrArg
    erw [mapToLinearEquiv'_tprod]
    simp only [objObj'_V_carrier, discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl,
      Iso.refl_hom, Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
    exact congrArg _ (funext (fun i => rfl))
  map_comp {X Y Z} f g := by
    ext x
    refine PiTensorProduct.induction_on' x (fun r x => ?_) (fun x y hx hy => by
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy])
    simp only [Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod, _root_.map_smul,
      Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply]
    apply congrArg
    rw [objMap', objMap', objMap']
    change (mapToLinearEquiv' F (CategoryTheory.CategoryStruct.comp f g))
      ((PiTensorProduct.tprod k) x) =
      (mapToLinearEquiv' F g) ((mapToLinearEquiv' F f) ((PiTensorProduct.tprod k) x))
    rw [mapToLinearEquiv'_tprod, mapToLinearEquiv'_tprod]
    erw [mapToLinearEquiv'_tprod]
    refine congrArg _ (funext (fun i => ?_))
    simp only [discreteFunctorMapEqIso, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv,
      eqToIso.inv, LinearEquiv.ofLinear_apply]
    rw [discreteFun_hom_trans]
    apply congrArg
    rfl
  μ_natural_left := μ_natural_left F
  μ_natural_right := μ_natural_right F
  associativity := associativity F
  left_unitality := left_unitality F
  right_unitality := right_unitality F

variable {F F' : Discrete C ⥤ Rep k G} (η : F ⟶ F')

/-- The maps for a natural transformation between `obj' F` and `obj' F'`. -/
def mapApp' (X : OverColor C) : (obj' F).obj X ⟶ (obj' F').obj X where
  hom := PiTensorProduct.map (fun x => (η.app (Discrete.mk (X.hom x))).hom)
  comm M := by
    ext x : 2
    refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [Functor.id_obj, map_add, ModuleCat.coe_comp, Function.comp_apply]
      erw [hx, hy]
      rfl)
    intro r x
    simp only [CategoryTheory.Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod,
      _root_.map_smul, ModuleCat.coe_comp, Function.comp_apply]
    apply congrArg
    change (PiTensorProduct.map fun x => (η.app { as := X.hom x }).hom)
      ((((obj' F).obj X).ρ M) ((PiTensorProduct.tprod k) x)) =
      (((obj' F').obj X).ρ M) ((PiTensorProduct.map fun x =>
      (η.app { as := X.hom x }).hom) ((PiTensorProduct.tprod k) x))
    rw [PiTensorProduct.map_tprod]
    simp only [Functor.id_obj, obj']
    change (PiTensorProduct.map fun x => (η.app { as := X.hom x }).hom)
      (((objObj' F X).ρ M) ((PiTensorProduct.tprod k) x)) =
      ((objObj' F' X).ρ M) ((PiTensorProduct.tprod k) fun i => (η.app { as := X.hom i }).hom (x i))
    rw [objObj'_ρ_tprod, objObj'_ρ_tprod]
    erw [PiTensorProduct.map_tprod]
    apply congrArg
    funext i
    simpa using LinearMap.congr_fun ((η.app (Discrete.mk (X.hom i))).comm M) (x i)

lemma mapApp'_tprod (X : OverColor C) (p : (i : X.left) → F.obj (Discrete.mk (X.hom i))) :
    (mapApp' η X).hom (PiTensorProduct.tprod k p) =
    PiTensorProduct.tprod k fun i => (η.app (Discrete.mk (X.hom i))).hom (p i) := by
  change (mapApp' η X).hom (PiTensorProduct.tprod k p) = _
  simp only [mapApp']
  erw [PiTensorProduct.map_tprod]
  rfl

lemma mapApp'_naturality {X Y : OverColor C} (f : X ⟶ Y) :
    (obj' F).map f ≫ mapApp' η Y = mapApp' η X ≫ (obj' F').map f:= by
  ext x : 2
  refine PiTensorProduct.induction_on' x ?_ (by
      intro x y hx hy
      simp only [Functor.id_obj, map_add, ModuleCat.coe_comp, Function.comp_apply]
      rw [hx, hy])
  intro r x
  simp only [Action.comp_hom, Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
    ModuleCat.coe_comp, Function.comp_apply]
  apply congrArg
  simp only [obj', objObj'_V_carrier]
  change (mapApp' η Y).hom ((objMap' F f).hom ((PiTensorProduct.tprod k) x)) =
  (objMap' F' f).hom ((mapApp' η X).hom ((PiTensorProduct.tprod k) x))
  rw [mapApp'_tprod, objMap'_tprod]
  erw [mapApp'_tprod, objMap'_tprod]
  apply congrArg
  funext i
  simp only [discreteFunctorMapEqIso, Functor.mapIso_hom, eqToIso.hom, Functor.mapIso_inv,
    eqToIso.inv, LinearEquiv.ofLinear_apply]
  have hn := congrArg (fun f => f.hom)
    (η.naturality (eqToHom (Discrete.eqToIso.proof_1 (Hom.toEquiv_comp_inv_apply f i))))
  simpa [CategoryStruct.comp] using LinearMap.congr_fun hn (x ((Hom.toEquiv f).symm i))

lemma mapApp'_unit : (obj' F).ε ≫ mapApp' η (𝟙_ (OverColor C)) = (obj' F').ε := by
  ext x
  simp only [obj', ε, instMonoidalCategoryStruct_tensorUnit_left, Functor.id_obj,
    instMonoidalCategoryStruct_tensorUnit_hom, objObj'_V_carrier,
    Action.instMonoidalCategory_tensorUnit_V, CategoryStruct.comp, Action.Hom.comp_hom,
    Action.mkIso_hom_hom, LinearEquiv.toModuleIso_hom]
  rw [LinearMap.comp_apply]
  erw [PiTensorProduct.isEmptyEquiv_symm_apply, PiTensorProduct.isEmptyEquiv_symm_apply]
  simp only [map_smul]
  apply congrArg
  erw [mapApp'_tprod]
  apply congrArg
  funext i
  exact Empty.elim i

lemma mapApp'_tensor (X Y : OverColor C) :
    (obj' F).μ X Y ≫ mapApp' η (X ⊗ Y) =
    (mapApp' η X ⊗ mapApp' η Y) ≫ (obj' F').μ X Y := by
  ext1
  apply HepLean.PiTensorProduct.induction_tmul (fun p q => ?_)
  simp only [obj', objObj'_V_carrier, instMonoidalCategoryStruct_tensorObj_left,
    instMonoidalCategoryStruct_tensorObj_hom, Functor.id_obj, CategoryStruct.comp,
    Action.Hom.comp_hom, Action.instMonoidalCategory_tensorObj_V, LinearMap.coe_comp,
    Function.comp_apply, Action.instMonoidalCategory_tensorHom_hom]
  erw [μ_tmul_tprod]
  erw [mapApp'_tprod]
  change _ = (μ F' X Y).hom.hom
    ((mapApp' η X).hom (PiTensorProduct.tprod k p) ⊗ₜ[k]
    (mapApp' η Y).hom (PiTensorProduct.tprod k q))
  rw [mapApp'_tprod, mapApp'_tprod]
  erw [μ_tmul_tprod]
  apply congrArg
  funext i
  match i with
  | Sum.inr i => rfl
  | Sum.inl i => rfl

/-- Given a natural transformation between `F F' : Discrete C ⥤ Rep k G` the
  monoidal natural transformation between `obj' F` and `obj' F'`. -/
def map' : obj' F ⟶ obj' F' where
  app := mapApp' η
  naturality _ _ f := mapApp'_naturality η f
  unit := mapApp'_unit η
  tensor := mapApp'_tensor η

end
end lift

/-- The functor taking functors in `Discrete C ⥤ Rep k G` to monoidal functors in
  `MonoidalFunctor (OverColor C) (Rep k G)`, built on the PiTensorProduct. -/
noncomputable def lift : (Discrete C ⥤ Rep k G) ⥤ MonoidalFunctor (OverColor C) (Rep k G) where
  obj F := lift.obj' F
  map η := lift.map' η
  map_id F := by
    simp only [lift.map']
    refine MonoidalNatTrans.ext' (fun X => ?_)
    ext x : 2
    refine PiTensorProduct.induction_on' x ?_ (by
        intro x y hx hy
        simp only [Functor.id_obj, map_add, ModuleCat.coe_comp, Function.comp_apply]
        rw [hx, hy])
    intro r y
    simp only [Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul]
    apply congrArg
    erw [lift.mapApp'_tprod]
    rfl
  map_comp {F G H} η θ := by
    refine MonoidalNatTrans.ext' (fun X => ?_)
    ext x : 2
    refine PiTensorProduct.induction_on' x ?_ (by
        intro x y hx hy
        simp only [Functor.id_obj, map_add, ModuleCat.coe_comp, Function.comp_apply]
        rw [hx, hy])
    intro r y
    simp only [Functor.id_obj, PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul,
      MonoidalNatTrans.comp_toNatTrans, NatTrans.comp_app, Action.comp_hom, ModuleCat.coe_comp,
      Function.comp_apply]
    apply congrArg
    simp only [lift.map']
    erw [lift.mapApp'_tprod]
    change _ =
      (lift.mapApp' θ X).hom ((lift.mapApp' η X).hom ((PiTensorProduct.tprod k) y))
    rw [lift.mapApp'_tprod]
    erw [lift.mapApp'_tprod]
    rfl

namespace lift

lemma map_tprod (F : Discrete C ⥤ Rep k G) {X Y : OverColor C} (f : X ⟶ Y)
    (p : (i : X.left) → F.obj (Discrete.mk <| X.hom i)) :
    ((lift.obj F).map f).hom (PiTensorProduct.tprod k p) =
    PiTensorProduct.tprod k fun (i : Y.left) => discreteFunctorMapEqIso F
    (OverColor.Hom.toEquiv_comp_inv_apply f i) (p ((OverColor.Hom.toEquiv f).symm i)) := by
  simp only [lift, obj', objObj'_V_carrier, Functor.id_obj]
  erw [objMap'_tprod]

lemma obj_μ_tprod_tmul (F : Discrete C ⥤ Rep k G) (X Y : OverColor C)
    (p : (i : X.left) → (F.obj (Discrete.mk <| X.hom i)))
    (q : (i : Y.left) → F.obj (Discrete.mk <| Y.hom i)) :
    ((lift.obj F).μ X Y).hom (PiTensorProduct.tprod k p ⊗ₜ[k] PiTensorProduct.tprod k q) =
    (PiTensorProduct.tprod k) fun i =>
    discreteSumEquiv F i (HepLean.PiTensorProduct.elimPureTensor p q i) := by
  exact μ_tmul_tprod F p q

lemma μIso_inv_tprod (F : Discrete C ⥤ Rep k G) (X Y : OverColor C)
    (p : (i : (X ⊗ Y).left) → F.obj (Discrete.mk <| (X ⊗ Y).hom i)) :
    ((lift.obj F).μIso X Y).inv.hom (PiTensorProduct.tprod k p) =
    (PiTensorProduct.tprod k (fun i => p (Sum.inl i))) ⊗ₜ[k]
    (PiTensorProduct.tprod k (fun i => p (Sum.inr i))) := by
  change ((Action.forget _ _).mapIso ((lift.obj F).μIso X Y)).inv (PiTensorProduct.tprod k p) = _
  trans ((Action.forget _ _).mapIso ((lift.obj F).μIso X Y)).toLinearEquiv.symm
    (PiTensorProduct.tprod k p)
  · congr
  erw [← LinearEquiv.eq_symm_apply]
  change _ = ((lift.obj F).μ X Y).hom _
  erw [obj_μ_tprod_tmul]
  congr
  funext i
  match i with
  | Sum.inl i => rfl
  | Sum.inr i => rfl

end lift
/-- The natural inclusion of `Discrete C` into `OverColor C`. -/
def incl : Discrete C ⥤ OverColor C := Discrete.functor fun c =>
  OverColor.mk (fun (_ : Fin 1) => c)

/-- The forgetful map from `MonoidalFunctor (OverColor C) (Rep k G)` to `Discrete C ⥤ Rep k G`
  built on the inclusion `incl` and forgetting the monoidal structure. -/
def forget : MonoidalFunctor (OverColor C) (Rep k G) ⥤ (Discrete C ⥤ Rep k G) where
  obj F := Discrete.functor fun c => F.obj (incl.obj (Discrete.mk c))
  map η := Discrete.natTrans fun c => η.app (incl.obj c)

variable (F F' : Discrete C ⥤ Rep k G) (η : F ⟶ F')

noncomputable section

/--
The `forgetLiftAppV` function takes an object `c` of type `C` and returns a linear equivalence
between the vector space obtained by applying the lift of `F` and that obtained by applying
`F`.
--/
def forgetLiftAppV (c : C) : ((lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c))).V ≃ₗ[k]
    (F.obj (Discrete.mk c)).V :=
  (PiTensorProduct.subsingletonEquiv 0 :
    (⨂[k] (_ : Fin 1), (F.obj (Discrete.mk c))) ≃ₗ[k] F.obj (Discrete.mk c))

@[simp]
lemma forgetLiftAppV_symm_apply (c : C) (x : (F.obj (Discrete.mk c)).V) :
    (forgetLiftAppV F c).symm x = PiTensorProduct.tprod k (fun _ => x) := by
  simp only [forgetLiftAppV, Fin.isValue, Functor.id_obj]
  erw [PiTensorProduct.subsingletonEquiv_symm_apply]

/-- The `forgetLiftAppV` function takes an object `c` of type `C` and returns a isomorphism
between the objects obtained by applying the lift of `F` and that obtained by applying
`F`. -/
def forgetLiftApp (c : C) : (lift.obj F).obj (OverColor.mk (fun (_ : Fin 1) => c))
    ≅ F.obj (Discrete.mk c) :=
    Action.mkIso (forgetLiftAppV F c).toModuleIso
  (fun g => by
    refine LinearMap.ext (fun x => ?_)
    simp only [forgetLiftAppV, Fin.isValue, LinearEquiv.toModuleIso_hom]
    refine PiTensorProduct.induction_on' x (fun r x => ?_) <| fun x y hx hy => by
      simp only [CategoryTheory.Functor.id_obj, map_add, hx, ModuleCat.coe_comp,
        Function.comp_apply, hy]
    simp only [CategoryStruct.comp, Fin.isValue, Functor.id_obj,
      PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply]
    apply congrArg
    erw [PiTensorProduct.subsingletonEquiv_apply_tprod]
    simp only [lift, lift.obj', lift.objObj'_V_carrier, Fin.isValue]
    erw [lift.objObj'_ρ_tprod]
    erw [PiTensorProduct.subsingletonEquiv_apply_tprod]
    rfl)

informal_definition forgetLift where
  math :≈ "The natural isomorphism between `lift (C := C) ⋙ forget` and
    `Functor.id (Discrete C ⥤ Rep k G)`."
  deps :≈ [``forget, ``lift]

end
end OverColor
end IndexNotation
