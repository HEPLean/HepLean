/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Tactic.FinCases
import Mathlib.Data.PFun
import Mathlib.Data.Fintype.Sum
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Limits.Shapes.Types
import LeanCopilot
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

def ch {X : FintypeCat} (x : X) : Hom 𝓣 (as X) := (x, 0)

def τ : Hom 𝓣 𝓣 := 1

@[simp]
lemma τ_comp_self : τ ≫ τ = 𝟙 𝓣 := rfl

def coreFintypeIncl : Core FintypeCat ⥤ elGr where
  obj X := as X
  map f := f

noncomputable def fintypeCoprod (X Y : FintypeCat) : elGr := as (X ⨿ Y)

noncomputable def fintypeCoprodTerm (X : FintypeCat) : elGr := fintypeCoprod X (⊤_ FintypeCat)

example : CategoryTheory.Functor.ReflectsIsomorphisms FintypeCat.incl := by
  exact reflectsIsomorphisms_of_full_and_faithful FintypeCat.incl


def terminalLimitCone : Limits.LimitCone (Functor.empty (FintypeCat)) where
  cone :=
    { pt := FintypeCat.of PUnit
      π := (Functor.uniqueFromEmpty _).hom}
  isLimit := {
      lift := fun _ _ => PUnit.unit
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => by
        funext
        rfl}

noncomputable def isoToTerm : (⊤_ FintypeCat) ≅ FintypeCat.of PUnit :=
  CategoryTheory.Limits.limit.isoLimitCone terminalLimitCone

noncomputable def objTerm : (⊤_ FintypeCat) := isoToTerm.inv PUnit.unit

noncomputable def starObj (X : FintypeCat) : (X ⨿ (⊤_ FintypeCat) : FintypeCat)  :=
  (@Limits.coprod.inr _ _ X (⊤_ FintypeCat) _) objTerm

/- TODO: derive this from `CategoryTheory.Limits.coprod.functor`. -/
noncomputable def coprodCore : Core FintypeCat × Core FintypeCat ⥤ Core FintypeCat where
  obj  := fun (X, Y) => (X ⨿ Y : FintypeCat)
  map f :=  CategoryTheory.Limits.coprod.mapIso f.1 f.2
  map_id := by
    intro X
    simp [Limits.coprod.mapIso]
    trans
    · rfl
    · aesop_cat
  map_comp := by
    intro X Y Z f g
    simp_all only [prod_Hom, prod_comp]
    obtain ⟨fst, snd⟩ := X
    obtain ⟨fst_1, snd_1⟩ := Y
    obtain ⟨fst_2, snd_2⟩ := Z
    simp_all only
    dsimp [Limits.coprod.mapIso]
    congr
    · simp_all only [Limits.coprod.map_map]
    · simp_all only [Limits.coprod.map_map]
      apply Eq.refl


end elGr

open elGr

/-- The category of graphical species. -/
abbrev GraphicalSpecies := elGrᵒᵖ ⥤ Type

namespace GraphicalSpecies

variable (S : GraphicalSpecies)

abbrev colors := S.obj ⟨𝓣⟩

def MatchColours (X Y : FintypeCat) : Type :=
  Subtype fun (R : S.obj ⟨as (X ⨿ (⊤_ FintypeCat))⟩ × S.obj ⟨as (Y ⨿ (⊤_ FintypeCat))⟩) ↦
    S.map (Quiver.Hom.op $ ch (elGr.starObj X)) R.1 =
    S.map (Quiver.Hom.op $ τ ≫ ch (elGr.starObj Y)) R.2


/-- Given two finite types `X` and `Y`, the objects
  of `S.obj ⟨elGr.as X⟩ × S.obj ⟨elGr.as Y⟩` which on `x ∈ X` and `y ∈ Y` map to dual colors. -/
def MatchColor {X Y : FintypeCat} (x : X) (y : Y) : Type :=
  Subtype fun (R : S.obj ⟨elGr.as X⟩ × S.obj ⟨elGr.as Y⟩) ↦
    S.map (Quiver.Hom.op (ch x)) R.1 = S.map (Quiver.Hom.op (τ ≫ ch y)) R.2

/-- An element of `S.MatchColor y x ` given an element of `S.MatchColor x y`. -/
def matchColorSwap {X Y : FintypeCat} {x : X} {y : Y} (R : S.MatchColor x y) : S.MatchColor y x :=
  ⟨(R.val.2, R.val.1), by
    have hS := congrArg (S.map (Quiver.Hom.op τ)) R.2
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply] at hS
    rw [← op_comp, ← op_comp, ← Category.assoc] at hS
    simpa using hS.symm⟩

def matchColorCongrLeft {X Y Z : FintypeCat} (f : X ≅ Z) {x : X} {y : Y} (R : S.MatchColor (f.hom x) y) :
  S.MatchColor x y :=
  ⟨(S.map (Quiver.Hom.op $ Hom.as f) R.val.1, R.val.2), by
    rw [← R.2, ← FunctorToTypes.map_comp_apply,  ← op_comp]
    rfl⟩

def matchColorCongrRight {X Y Z : FintypeCat} (f : Y ≅ Z) {x : X} {y : Y} (R : S.MatchColor x (f.hom y)) :
  S.MatchColor x y :=
  ⟨(R.val.1, S.map (Quiver.Hom.op $ Hom.as f) R.val.2), by
    rw [R.2, ← FunctorToTypes.map_comp_apply,  ← op_comp]
    rfl⟩

def matchColorCongr {X Y Z W : FintypeCat} (f : X ≅ W) (g : Y ≅ Z) {x : X} {y : Y}
  (R : S.MatchColor (f.hom x) (g.hom y)) : S.MatchColor x y :=
  S.matchColorCongrLeft f (S.matchColorCongrRight g R)

def matchColorIndexCongrLeft {X Y : FintypeCat} {x x' : X} {y : Y}  (h : x = x') (R : S.MatchColor x y) :
  S.MatchColor x' y :=
  ⟨(R.val.1, R.val.2), by
    subst h
    exact R.2⟩

def MatchColorFin (X Y : FintypeCat) : Type :=
  @MatchColor S (FintypeCat.of $ X ⊕ Fin 1) (FintypeCat.of $ Y ⊕ Fin 1) (Sum.inr 0) (Sum.inr 0)

def matchColorFinCongrLeft {X Y Z  : FintypeCat} (f : X ≅ W) (R : S.MatchColorFin X Y) :
    S.MatchColorFin W Z := by

  let f' : FintypeCat.of (X ⊕ Fin 1) ≅ FintypeCat.of (W ⊕ Fin 1) :=
     FintypeCat.equivEquivIso $ Equiv.sumCongr (FintypeCat.equivEquivIso.symm f)
     (FintypeCat.equivEquivIso.symm (Iso.refl (Fin 1)))
  let x := @matchColorCongrLeft S _ (FintypeCat.of (Y ⊕ Fin 1))  _ f'  (Sum.inr 0) (Sum.inr 0) R

end GraphicalSpecies

structure MulGraphicalSpecies where
  toGraphicalSpecies : GraphicalSpecies
  mul : ∀ {X Y : FintypeCat},
    toGraphicalSpecies.MatchColorFin X Y → toGraphicalSpecies.obj
    ⟨elGr.as (FintypeCat.of (X ⊕ Y))⟩
  comm : ∀ {X Y : FintypeCat} {x : X} {y : Y} (R : toGraphicalSpecies.MatchColorFin X Y),
    mul R = toGraphicalSpecies.map (fintypeCoprodSwap X Y).op
      (mul (toGraphicalSpecies.matchColorSwap R))
  equivariance : ∀ {X Y Z W : FintypeCat} (f : X ≃ W) (g : Y ≃ Z) {x : X} {y : Y}
    (R : toGraphicalSpecies.MatchColor (f x) (g y)),
    toGraphicalSpecies.map (fintypeCoprodMap f g).op  (mul R) =
    mul (toGraphicalSpecies.matchColorCongr f g R)

namespace MulGraphicalSpecies

variable (S : MulGraphicalSpecies)

def obj := S.toGraphicalSpecies.obj

def map {X Y : elGrᵒᵖ} (f : X ⟶ Y) : S.obj X ⟶ S.obj Y := S.toGraphicalSpecies.map f

end MulGraphicalSpecies
