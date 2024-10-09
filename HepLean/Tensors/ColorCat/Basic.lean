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
import HepLean.SpaceTime.WeylFermion.Basic
import HepLean.SpaceTime.LorentzVector.Complex
/-!

## Over category.

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
lemma toEquiv_id (f : OverColor C) : toEquiv (𝟙 f) = Equiv.refl f.left := by
  ext x
  simp [toEquiv]
  rfl

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

section monoidal

/-!

## The monoidal structure on `OverColor C`.

The category `OverColor C` can, through the disjoint union, be given the structure of a
symmetric monoidal category.

-/

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

instance (C : Type) : SymmetricCategory (OverColor C) where
  toBraidedCategory := instBraidedCategory C
  symmetry X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl

end monoidal

/-- Make an object of `OverColor C` from a map `X → C`. -/
def mk (f : X → C) : OverColor C := Over.mk f

open MonoidalCategory

/-- The monoidal functor from `OverColor C` to `OverColor D` constructed from a map
  `f : C → D`. -/
def map {C D : Type} (f : C → D) : MonoidalFunctor (OverColor C) (OverColor D) where
  toFunctor := Core.functorToCore (Core.inclusion (Over C) ⋙ (Over.map f))
  ε := Over.isoMk (Iso.refl _) (by
    ext x
    exact Empty.elim x)
  μ X Y := Over.isoMk (Iso.refl _) (by
    ext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl)
  μ_natural_left X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
  μ_natural_right X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
  associativity X Y Z := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr x => rfl
  left_unitality X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
  right_unitality X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl

/-- The tensor product on `OverColor C` as a monoidal functor. -/
def tensor : MonoidalFunctor (OverColor C × OverColor C) (OverColor C)  where
  toFunctor := MonoidalCategory.tensor (OverColor C)
  ε := Over.isoMk (Equiv.sumEmpty Empty Empty).symm.toIso (by
    ext x
    exact Empty.elim x)
  μ X Y := Over.isoMk (Equiv.sumSumSumComm X.1.left X.2.left Y.1.left Y.2.left).toIso (by
    ext x
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl)
  μ_natural_left X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl
  μ_natural_right X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl
  associativity X Y Z := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl (Sum.inl x)) => rfl
    | Sum.inl (Sum.inl (Sum.inr x)) => rfl
    | Sum.inl (Sum.inr (Sum.inl x)) => rfl
    | Sum.inl (Sum.inr (Sum.inr x)) => rfl
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl
  left_unitality X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => exact Empty.elim x
    | Sum.inr (Sum.inl x)=> rfl
    | Sum.inr (Sum.inr x)=> rfl
  right_unitality X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr x => exact Empty.elim x

/-!

## Useful equivalences.

-/

/-- The isomorphism between `c : X → C` and `c ∘ e.symm` as objects in `OverColor C` for an
  equivalence `e`. -/
def equivToIso {c : X → C} (e : X ≃ Y) : mk c ≅ mk (c ∘ e.symm) := {
  hom := Over.isoMk e.toIso ((Iso.eq_inv_comp e.toIso).mp rfl),
  inv := (Over.isoMk e.toIso ((Iso.eq_inv_comp e.toIso).mp rfl)).symm,
  hom_inv_id := by
    apply CategoryTheory.Iso.ext
    erw [CategoryTheory.Iso.trans_hom]
    simp only [Functor.id_obj, Over.mk_left, Over.mk_hom, Iso.symm_hom, Iso.hom_inv_id]
    rfl,
  inv_hom_id := by
    apply CategoryTheory.Iso.ext
    erw [CategoryTheory.Iso.trans_hom]
    simp only [Iso.symm_hom, Iso.inv_hom_id]
    rfl}

/-- The equivalence between `Fin n.succ` and `Fin 1 ⊕ Fin n` extracting the
  `i`th component. -/
def finExtractOne {n : ℕ} (i : Fin n.succ) : Fin n.succ ≃ Fin 1 ⊕ Fin n :=
  (finCongr (by omega : n.succ = i + 1 + (n - i))).trans <|
  finSumFinEquiv.symm.trans <|
  (Equiv.sumCongr (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin i) (Fin 1)))
    (Equiv.refl (Fin (n-i)))).trans <|
  (Equiv.sumAssoc (Fin 1) (Fin i) (Fin (n - i))).trans <|
  Equiv.sumCongr (Equiv.refl (Fin 1)) (finSumFinEquiv.trans (finCongr (by omega)))


end OverColor

end IndexNotation
