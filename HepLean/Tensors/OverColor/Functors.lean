/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.OverColor.Basic
/-!

## Functors related to the OverColor category

-/
namespace IndexNotation
namespace OverColor
open CategoryTheory
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
def tensor (C : Type)  : MonoidalFunctor (OverColor C × OverColor C) (OverColor C) where
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

def diag (C : Type) : MonoidalFunctor (OverColor C) (OverColor C × OverColor C) :=
  MonoidalFunctor.diag (OverColor C)

def const (C : Type) : MonoidalFunctor (OverColor C) (OverColor C) where
  toFunctor := (Functor.const (OverColor C)).obj (𝟙_ (OverColor C))
  ε := 𝟙 (𝟙_ (OverColor C))
  μ _ _:= (λ_  (𝟙_ (OverColor C))).hom
  μ_natural_left _ _ := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, MonoidalCategory.whiskerRight_id,
      Category.id_comp, Iso.hom_inv_id, Category.comp_id]
  μ_natural_right _ _ := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id,
      Category.id_comp, Category.comp_id]
  associativity X Y Z := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun i => by
    match i with
    | Sum.inl (Sum.inl i) => rfl
    | Sum.inl (Sum.inr i) => rfl
    | Sum.inr i => rfl
  left_unitality X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun i => by
    match i with
    | Sum.inl i => exact Empty.elim i
    | Sum.inr i => exact Empty.elim i
  right_unitality X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun i => by
    match i with
    | Sum.inl i => exact Empty.elim i
    | Sum.inr i => exact Empty.elim i

def contrPair (C : Type) (τ : C → C) : MonoidalFunctor (OverColor C) (OverColor C) :=
  OverColor.diag C
  ⊗⋙ (MonoidalFunctor.prod (MonoidalFunctor.id (OverColor C)) (OverColor.map τ))
  ⊗⋙ OverColor.tensor C
end OverColor
end IndexNotation
