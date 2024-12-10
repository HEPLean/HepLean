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
def map {C D : Type} (f : C → D) : Functor (OverColor C) (OverColor D) :=
  Core.functorToCore (Core.inclusion (Over C) ⋙ (Over.map f))

/-- The functor `map f` is lax-monoidal. -/
instance map_laxMonoidal {C D : Type} (f : C → D) : Functor.LaxMonoidal (map f) where
  ε' := Over.isoMk (Iso.refl _) (by
    ext x
    exact Empty.elim x)
  μ' := fun X Y => Over.isoMk (Iso.refl _) (by
    ext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl)
  μ'_natural_left X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    rfl
  μ'_natural_right X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    rfl
  associativity' X Y Z := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr x => rfl
  left_unitality' := fun X => CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl
  right_unitality' := fun X => CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl

/-- The functor `map f` is lax-monoidal. -/
noncomputable instance map_monoidal {C D : Type} (f : C → D) : Functor.Monoidal (map f) :=
  Functor.Monoidal.ofLaxMonoidal _

/-- The tensor product on `OverColor C` as a monoidal functor. -/
def tensor (C : Type) : Functor (OverColor C × OverColor C) (OverColor C) :=
  MonoidalCategory.tensor (OverColor C)

/-- The functor tensor is lax-monoidal. -/
instance tensor_laxMonoidal (C : Type) : Functor.LaxMonoidal (tensor C) where
  ε' := Over.isoMk (Equiv.sumEmpty Empty Empty).symm.toIso rfl
  μ' := fun X Y => Over.isoMk (Equiv.sumSumSumComm X.1.left X.2.left Y.1.left Y.2.left).toIso (by
    ext x
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl)
  μ'_natural_left X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl
  μ'_natural_right X Y := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl
  associativity' X Y Z := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl (Sum.inl x)) => rfl
    | Sum.inl (Sum.inl (Sum.inr x)) => rfl
    | Sum.inl (Sum.inr (Sum.inl x)) => rfl
    | Sum.inl (Sum.inr (Sum.inr x)) => rfl
    | Sum.inr (Sum.inl x) => rfl
    | Sum.inr (Sum.inr x) => rfl
  left_unitality' X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl x => exact Empty.elim x
    | Sum.inr (Sum.inl x)=> rfl
    | Sum.inr (Sum.inr x)=> rfl
  right_unitality' X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun x => by
    match x with
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr x) => rfl
    | Sum.inr x => exact Empty.elim x

/-- The functor tensor is monoidal. -/
noncomputable instance tensor_monoidal (C : Type) : Functor.Monoidal (tensor C) :=
  Functor.Monoidal.ofLaxMonoidal _

/-- The constant monoidal functor from `OverColor C` to itself landing on `𝟙_ (OverColor C)`. -/
def const (C : Type) : Functor (OverColor C) (OverColor C) :=
  (Functor.const (OverColor C)).obj (𝟙_ (OverColor C))

/-- The functor `const C` is lax monoidal. -/
instance const_laxMonoidal (C : Type) : Functor.LaxMonoidal (const C) where
  ε' := 𝟙 (𝟙_ (OverColor C))
  μ' := fun _ _ => (λ_ (𝟙_ (OverColor C))).hom
  μ'_natural_left := fun _ _ => by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, MonoidalCategory.whiskerRight_id,
      Category.id_comp, Iso.hom_inv_id, Category.comp_id, const]
  μ'_natural_right := fun _ _ => by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, MonoidalCategory.whiskerLeft_id,
      Category.id_comp, Category.comp_id, const]
  associativity' X Y Z := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun i =>
    match i with
    | Sum.inl (Sum.inl i) => rfl
    | Sum.inl (Sum.inr i) => rfl
    | Sum.inr i => rfl
  left_unitality' X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun i =>
    match i with
    | Sum.inl i => Empty.elim i
    | Sum.inr i => Empty.elim i
  right_unitality' X := CategoryTheory.Iso.ext <| Over.OverMorphism.ext <| funext fun i =>
    match i with
    | Sum.inl i => Empty.elim i
    | Sum.inr i => Empty.elim i

/-- The functor `const C` is monoidal. -/
noncomputable instance const_monoidal (C : Type) : Functor.Monoidal (const C) :=
  Functor.Monoidal.ofLaxMonoidal _

/-- The monoidal functor from `OverColor C` to `OverColor C` taking `f` to `f ⊗ τ_* f`. -/
def contrPair (C : Type) (τ : C → C) : Functor (OverColor C) (OverColor C) :=
  (Functor.diag (OverColor C))
  ⋙ (Functor.prod (Functor.id (OverColor C)) (OverColor.map τ))
  ⋙ (OverColor.tensor C)

/-- The functor `contrPair` is lax-monoidal. -/
instance contrPair_laxMonoidal (C : Type) (τ : C → C) : Functor.LaxMonoidal (contrPair C τ) :=
  Functor.LaxMonoidal.comp (Functor.diag (OverColor C)) ((𝟭 (OverColor C)).prod (map τ) ⋙ tensor C)

/-- The functor `contrPair` is monoidal. -/
noncomputable instance contrPair_monoidal (C : Type) (τ : C → C) :
    Functor.Monoidal (contrPair C τ) :=
  Functor.Monoidal.ofLaxMonoidal _

end OverColor
end IndexNotation
