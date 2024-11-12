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
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import HepLean.Lorentz.Weyl.Basic
import HepLean.Lorentz.ComplexVector.Basic
/-!

# Over color category.

## Color

The notion of color will plays a critical role of the formalisation of index notation used here.
The way to describe color is through examples.
Indices of real Lorentz tensors can either be up-colored or down-colored.
On the other hand, indices of Einstein tensors can just down-colored.
In the case of complex Lorentz tensors, indices can take one of six different colors,
corresponding to up and down, dotted and undotted weyl fermion indcies and up and down
Lorentz indices.

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

/-- If `m` and `n` are morphisms in `OverColor C`, they are equal if their underlying
  morphisms in `Over C` are equal. -/
lemma ext (m n : f ⟶ g) (h : m.hom = n.hom) : m = n := CategoryTheory.Iso.ext h

lemma ext_iff (m n : f ⟶ g) : (∀ x, m.hom.left x = n.hom.left x) ↔ m = n := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · apply ext
    ext x
    exact h x
  · rw [h]
    exact fun x => rfl

/-- Given a hom in `OverColor C` the underlying equivalence between types. -/
def toEquiv (m : f ⟶ g) : f.left ≃ g.left where
  toFun := m.hom.left
  invFun := m.inv.left
  left_inv := by
    simpa only [Over.comp_left] using congrFun (congrArg (fun x => x.left) m.hom_inv_id)
  right_inv := by
    simpa only [Over.comp_left] using congrFun (congrArg (fun x => x.left) m.inv_hom_id)

/-- The equivalence of types underlying the identity morphism is the reflexive equivalence. -/
@[simp]
lemma toEquiv_id (f : OverColor C) : toEquiv (𝟙 f) = Equiv.refl f.left := by
  rfl

/-- The function `toEquiv` obeys compositions. -/
@[simp]
lemma toEquiv_comp (m : f ⟶ g) (n : g ⟶ h) : toEquiv (m ≫ n) = (toEquiv m).trans (toEquiv n) := by
  rfl

lemma toEquiv_symm_apply (m : f ⟶ g) (i : g.left) :
    f.hom ((toEquiv m).symm i) = g.hom i := by
  simpa [toEquiv, types_comp] using congrFun m.inv.w i

lemma toEquiv_comp_hom (m : f ⟶ g) : g.hom ∘ (toEquiv m) = f.hom := by
  ext x
  simpa [types_comp, toEquiv] using congrFun m.hom.w x

lemma toEquiv_comp_inv_apply (m : f ⟶ g) (i : g.left) :
    f.hom ((OverColor.Hom.toEquiv m).symm i) = g.hom i := by
  simpa [toEquiv, types_comp] using congrFun m.inv.w i

lemma toEquiv_comp_apply (m : f ⟶ g) (i : f.left) :
    f.hom i = g.hom ((toEquiv m) i) := by
  simpa [toEquiv, types_comp] using (congrFun m.hom.w i).symm

/-- Given a morphism in `OverColor C`, the corresponding isomorphism. -/
def toIso (m : f ⟶ g) : f ≅ g := {
  hom := m,
  inv := m.symm,
  hom_inv_id := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    simp only [CategoryStruct.comp, Iso.self_symm_id, Iso.refl_hom, Over.id_left, types_id_apply]
    rfl,
  inv_hom_id := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    simp only [CategoryStruct.comp, Iso.symm_self_id, Iso.refl_hom, Over.id_left, types_id_apply]
    rfl}

end Hom

section monoidal

/-!

## The monoidal structure on `OverColor C`.

The category `OverColor C` can, through the disjoint union, be given the structure of a
symmetric monoidal category.

-/

/-- The category `OverColor C` carries an instance of a Monoidal category structure. -/
@[simps!]
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
      ext x
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl),
    inv := (Over.isoMk (Equiv.sumAssoc X.left Y.left Z.left).toIso (by
      ext x
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl)).symm,
    hom_inv_id := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl,
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
      rfl}
  rightUnitor X := {
    hom := Over.isoMk (Equiv.sumEmpty X.left Empty).toIso
    inv := (Over.isoMk (Equiv.sumEmpty X.left Empty).toIso).symm
    hom_inv_id := by
      apply CategoryTheory.Iso.ext
      erw [CategoryTheory.Iso.trans_hom]
      simp only [Functor.id_obj, Over.mk_left, Over.mk_hom, Iso.symm_hom, Iso.hom_inv_id]
      rfl,
    inv_hom_id := by
      rfl}

/-- The category `OverColor C` carries an instance of a Monoidal category. -/
instance (C : Type) : MonoidalCategory (OverColor C) where
    tensorHom_def f g := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => rfl
    tensor_id X Y := CategoryTheory.Iso.ext <| (Iso.eq_inv_comp _).mp rfl
    tensor_comp f1 f2 g1 g2 := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl
    whiskerLeft_id X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl
    id_whiskerRight X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl
    associator_naturality {X1 X2 X3 Y1 Y2 Y3} f1 f2 f3 :=
        CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl
    leftUnitor_naturality f :=
        CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => exact Empty.elim x
      | Sum.inr x => rfl
    rightUnitor_naturality f :=
        CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => exact Empty.elim x
    pentagon f g h i := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl (Sum.inl (Sum.inl x)) => rfl
      | Sum.inl (Sum.inl (Sum.inr x)) => rfl
      | Sum.inl (Sum.inr x) => rfl
      | Sum.inr x => rfl
    triangle f g := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl (Sum.inl x) => rfl
      | Sum.inl (Sum.inr x) => exact Empty.elim x
      | Sum.inr x => rfl

/-- The category `OverColor C` carries an instance of a braided category. -/
instance (C : Type) : BraidedCategory (OverColor C) where
  braiding f g := {
    hom := Over.isoMk (Equiv.sumComm f.left g.left).toIso
    inv := (Over.isoMk (Equiv.sumComm f.left g.left).toIso).symm
    hom_inv_id := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl,
    inv_hom_id := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
      match x with
      | Sum.inl x => rfl
      | Sum.inr x => rfl}
  braiding_naturality_right X Y1 Y2 f := CategoryTheory.Iso.ext <| Over.OverMorphism.ext
      <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
  braiding_naturality_left X f := CategoryTheory.Iso.ext <| Over.OverMorphism.ext
      <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
  hexagon_forward X1 X2 X3 := CategoryTheory.Iso.ext <| Over.OverMorphism.ext
      <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr x => rfl
  hexagon_reverse X1 X2 X3 := CategoryTheory.Iso.ext <| Over.OverMorphism.ext
      <| funext fun x => by
    match x with
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl
    | Sum.inl x => rfl

/-- The category `OverColor C` carries an instance of a symmetric monoidal category. -/
instance (C : Type) : SymmetricCategory (OverColor C) where
  toBraidedCategory := instBraidedCategory C
  symmetry X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl

end monoidal

/-- Make an object of `OverColor C` from a map `X → C`. -/
def mk (f : X → C) : OverColor C := Over.mk f

@[simp]
lemma mk_hom (f : X → C) : (mk f).hom = f := rfl
open MonoidalCategory

lemma Hom.fin_ext {n : ℕ} {f g : Fin n → C} (σ σ' : OverColor.mk f ⟶ OverColor.mk g)
    (h : ∀ (i : Fin n), σ.hom.left i = σ'.hom.left i) : σ = σ' := by
  apply Hom.ext
  ext i
  apply h

end OverColor

end IndexNotation
