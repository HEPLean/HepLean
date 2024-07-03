/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.GraphicalSpecies
import HepLean.SpaceTime.LorentzVector.Basic
/-!

# Lorentz Tensors

This file is currently a work-in-progress.

The aim is to define Lorentz tensors, and devlop a systematic way to manipulate them.

To manipulate them we will use the theory of modular operads
(see e.g. [Raynor][raynor2021graphical]).


-/

/-- A Lorentz Tensor defined by its coordinate map. -/
def LorentzTensor (d : ℕ) (X : FintypeCat) : Type :=
  (X → Fin 1 ⊕ Fin d) → ℝ

/-- An instance of a additive commutative monoid on `LorentzTensor`. -/
instance (d : ℕ) (X : FintypeCat)  : AddCommMonoid (LorentzTensor d X) := Pi.addCommMonoid

/-- An instance of a module on `LorentzVector`. -/
noncomputable instance (d : ℕ) (X : FintypeCat)  : Module ℝ (LorentzTensor d X) := Pi.module _ _ _

namespace LorentzTensor
open BigOperators
open elGr
open CategoryTheory

variable {d : ℕ} {X Y : FintypeCat}

/-- The map taking a list of `LorentzVector d` indexed by `X` to a ` LorentzTensor d X`. -/
def tmul (t : X → LorentzVector d) : LorentzTensor d X :=
  fun f => ∏ x, (t x) (f x)

/- An equivalence between `X → Fin 1 ⊕ Fin d` and `Y → Fin 1 ⊕ Fin d` given an isomorphism
  between `X` and `Y`. -/
def indexEquivOfIndexHom (f : X ≅ Y) : (X → Fin 1 ⊕ Fin d) ≃ (Y → Fin 1 ⊕ Fin d)  :=
  Equiv.piCongrLeft' _ (FintypeCat.equivEquivIso.symm f)

/-- Given an isomorphism of indexing sets, a linear equivalence on Lorentz tensors. -/
noncomputable def mapOfIndexHom (f : X ≅ Y) :  LorentzTensor d Y ≃ₗ[ℝ] LorentzTensor d X :=
  LinearEquiv.piCongrLeft' ℝ _ (indexEquivOfIndexHom f).symm

/-!

## Graphical species and Lorentz tensors

-/

/-- The graphical species defined by Lorentz tensors.

For this simple case, 𝓣 gets mapped to `PUnit`, if one wishes to include fermions etc,
then `PUnit` will change to account for the colouring of edges. -/
noncomputable def graphicalSpecies (d : ℕ) : GraphicalSpecies where
  obj x :=
    match x with
    | ⟨𝓣⟩ => PUnit
    | ⟨as f⟩ => LorentzTensor d f
  map {x y} f :=
    match x, y, f with
    | ⟨𝓣⟩, ⟨𝓣⟩, _ => 𝟙 PUnit
    | ⟨𝓣⟩, ⟨as x⟩, ⟨f⟩ => Empty.elim f
    | ⟨as f⟩, ⟨𝓣⟩, _ => fun _ => PUnit.unit
    | ⟨as f⟩, ⟨as g⟩, ⟨h⟩ => (mapOfIndexHom h).toEquiv.toFun
  map_id X := by
    match X with
    | ⟨𝓣⟩ => rfl
    | ⟨as f⟩ => rfl
  map_comp {x y z} f g := by
    match x, y, z, f, g with
    | ⟨𝓣⟩, ⟨𝓣⟩, ⟨𝓣⟩, _, _ => rfl
    | _, ⟨𝓣⟩, ⟨as _⟩, _, ⟨g⟩ => exact Empty.elim g
    | ⟨𝓣⟩, ⟨as _⟩, _, ⟨f⟩, _ =>  exact Empty.elim f
    | ⟨as x⟩, ⟨as y⟩, ⟨as z⟩, ⟨f⟩, ⟨g⟩ => rfl
    | ⟨as x⟩, ⟨𝓣⟩, ⟨𝓣⟩, _, _ => rfl
    | ⟨as x⟩, ⟨as y⟩, ⟨𝓣⟩, _, _ => rfl


end LorentzTensor
