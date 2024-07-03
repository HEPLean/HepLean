/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Tactic.FinCases
/-!

# Graphical species

We define the general notion of a graphical species.
This will be used to define contractions of Lorentz tensors.

## References

- [Raynor][raynor2021graphical]
- https://arxiv.org/pdf/1906.01144 (TODO: add to references)

-/

open CategoryTheory

/-- Finite types adjoined with a distinguished object. -/
inductive elGr where
  | 𝓣
  | as (f : FintypeCat)

namespace elGr

/-- The morphism sets between elements of `elGr`. -/
def Hom (a b : elGr) : Type :=
  match a, b with
  | 𝓣, 𝓣 => Fin 2
  | 𝓣, as f => f × Fin 2
  | as _, 𝓣 => Empty
  | as f, as g => f ≅ g

instance : OfNat (Hom 𝓣 𝓣) 0 := ⟨(0 : Fin 2)⟩

instance : OfNat (Hom 𝓣 𝓣) 1 := ⟨(1 : Fin 2)⟩


namespace Hom

/-- The identity morphism. -/
@[simp]
def id (a : elGr) : Hom a a :=
  match a with
  | 𝓣 => 0
  | as f => Iso.refl f

/-- The composition of two morphisms. -/
@[simp]
def comp {a b c : elGr} (f : Hom a b) (g : Hom b c) : Hom a c :=
  match a, b, c, f, g with
  | 𝓣, 𝓣, 𝓣, 0, 0 => 0
  | 𝓣, 𝓣, 𝓣, 0, 1 => 1
  | 𝓣, 𝓣, 𝓣, 1, 0 => 1
  | 𝓣, 𝓣, 𝓣, 1, 1 => 0
  | 𝓣, as _, 𝓣, _, g => Empty.elim g
  | 𝓣, 𝓣, as _fakeMod, 0, (g, 0) => (g, 0)
  | 𝓣, 𝓣, as _, 0, (g, 1) => (g, 1)
  | 𝓣, 𝓣, as _, 1, (g, 0) => (g, 1)
  | 𝓣, 𝓣, as _, 1, (g, 1) => (g, 0)
  | 𝓣, as _, as _, (f, 0), g => (g.hom f, 0)
  | 𝓣, as _, as _, (f, 1), g => (g.hom f, 1)
  | as _, as _, as _, f, g => f ≪≫ g

instance : Fintype (Hom 𝓣 𝓣) := Fin.fintype 2

end Hom

/-- The category of elementary graphs. -/
instance : Category elGr where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro X Y f
    match X, Y, f with
    | 𝓣, 𝓣, (0 : Fin 2) => rfl
    | 𝓣, 𝓣, (1 : Fin 2) => rfl
    | 𝓣, as y, (f, (0 : Fin 2)) => rfl
    | 𝓣, as y, (f, (1 : Fin 2)) => rfl
    | as x, as y, f => rfl
  comp_id := by
    intro X Y f
    match X, Y, f with
    | 𝓣, 𝓣, (0 : Fin 2) => rfl
    | 𝓣, 𝓣, (1 : Fin 2) => rfl
    | 𝓣, as y, (f, (0 : Fin 2)) => rfl
    | 𝓣, as y, (f, (1 : Fin 2)) => rfl
    | as x, as y, f => rfl
  assoc := by
    intro X Y Z W f g h
    match X, Y, Z, W, f, g, h with
    | _, _, as _, 𝓣, _, _, x => exact Empty.elim x
    | _, as _, 𝓣,  _, _, x, _ => exact Empty.elim x
    | as _, 𝓣, _,  _, x, _, _ => exact Empty.elim x
    | 𝓣, 𝓣, 𝓣, 𝓣, f, g, h =>
      simp only at g f h
      fin_cases g <;> fin_cases f <;> fin_cases h <;> rfl
    | 𝓣, 𝓣, 𝓣, as a, f, g, (h, hx) =>
      simp only at g f
      fin_cases g <;> fin_cases f <;> fin_cases hx <;> rfl
    | 𝓣, 𝓣, as b, as a, f, (g, hg), h =>
      simp only at g f
      fin_cases f <;> fin_cases hg <;>  rfl
    | 𝓣, as c, as b, as a, (f, hf ), g, h =>
      simp only at g f
      fin_cases hf  <;>  rfl
    | as d, as c, as b, as a, f, g, h =>
      simp only [Hom.comp, Iso.trans_assoc]

end elGr

/-- The category of graphical species. -/
abbrev  GraphicalSpecies := elGrᵒᵖ ⥤ Type
