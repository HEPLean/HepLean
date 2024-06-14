/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Card
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Data.Fintype.Pi
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
/-!
# Feynman diagrams in Phi^4 theory

The aim of this file is to start building up the theory of Feynman diagrams in the context of
Phi^4 theory.

## References

- The approach taking to defining Feynman diagrams is based on:

Theo Johnson-Freyd (https://mathoverflow.net/users/78/theo-johnson-freyd), How to count symmetry
factors of Feynman diagrams? , URL (version: 2010-06-03): https://mathoverflow.net/q/26938

## TODO

- Develop a way to display Feynman diagrams.
- Define a connected diagram.
- Define the Feynman rules, and perform an example calculation.
- Determine an efficent way to calculate symmetry factors. Currently there is a method, but
it will not work for large diagrams as it scales factorially with the number of half-edges.

-/

namespace PhiFour
open CategoryTheory

/-- Edges in Φ^4  internal `0`.
  Here `Type` is the category in which half-edges live. In general `Type` will be e.g.
  `Type × Type` with more fields. -/
def edgeType : Fin 1 → Type
  | 0 => Fin 2

/-- Vertices in Φ^4, can either be `external` corresponding to `0`, or a `phi^4` interaction
corresponding to `1`. -/
def vertexType : Fin 2 → Type
  | 0 => Fin 1
  | 1 => Fin 4

/-- The type of vacuum Feynman diagrams for Phi-4 theory. -/
structure FeynmanDiagram where
  /-- The type of half edges in the Feynman diagram. Sometimes also called `flags`. -/
  𝓱𝓔 : Type
  /-- The type of edges in the Feynman diagram. -/
  𝓔 : Type
  /-- Maps each edge to a label. Labels `0` if it is an external edge,
    and labels `1` if an internal edge. -/
  𝓔Label : 𝓔 → Fin 1
  /-- Maps half-edges to edges. -/
  𝓱𝓔To𝓔 : 𝓱𝓔 → 𝓔
  /-- Requires that the fiber of the map `𝓱𝓔To𝓔` at `x ∈ 𝓔` agrees with the corresponding
  `edgeType`. -/
  𝓔Fiber : ∀ x,  CategoryTheory.IsIsomorphic (𝓱𝓔To𝓔 ⁻¹' {x} : Type) $ (edgeType ∘ 𝓔Label) x
  /-- The type of vertices in the Feynman diagram. -/
  𝓥 : Type
  /-- Maps each vertex to a label. In this case this map contains no information since
  there is only one type of vertex.. -/
  𝓥Label : 𝓥 → Fin 2
  /-- Maps half-edges to vertices. -/
  𝓱𝓔To𝓥 : 𝓱𝓔 → 𝓥
  /-- Requires that the fiber of the map `𝓱𝓔To𝓥` at `x ∈ 𝓥` agrees with the corresponding
    `vertexType`. -/
  𝓥Fiber : ∀ x,  CategoryTheory.IsIsomorphic (𝓱𝓔To𝓥 ⁻¹' {x} : Type) $ (vertexType ∘ 𝓥Label) x

namespace FeynmanDiagram

variable (F : FeynmanDiagram)

section Decidability
/-!

## Decidability

The aim of this section is to make it easy to prove the `𝓔Fiber` and `𝓥Fiber` conditions by
showing that they are decidable in cases when everything is finite and nice
(which in practice is always).

--/

lemma fiber_cond_edge_iff_exists {𝓱𝓔 𝓔 : Type} (𝓱𝓔To𝓔 : 𝓱𝓔 → 𝓔) (𝓔Label : 𝓔 → Fin 1) (x : 𝓔) :
    (CategoryTheory.IsIsomorphic (𝓱𝓔To𝓔 ⁻¹' {x} : Type) $ (edgeType ∘ 𝓔Label) x)
    ↔ ∃ (f : 𝓱𝓔To𝓔 ⁻¹' {x} → (edgeType ∘ 𝓔Label) x), Function.Bijective f :=
  Iff.intro
    (fun h ↦ match h with
            | ⟨f1, f2, h1, h2⟩ => ⟨f1, (isIso_iff_bijective f1).mp ⟨f2, h1, h2⟩⟩)
    (fun ⟨f1, hb⟩ ↦ match (isIso_iff_bijective f1).mpr hb with
                   | ⟨f2, h1, h2⟩ => ⟨f1, f2, h1, h2⟩)

lemma fiber_cond_vertex_iff_exists {𝓱𝓥 𝓥 : Type} (𝓱𝓥To𝓥 : 𝓱𝓥 → 𝓥) (𝓥Label : 𝓥 → Fin 2) (x : 𝓥) :
    (CategoryTheory.IsIsomorphic (𝓱𝓥To𝓥 ⁻¹' {x} : Type) $ (vertexType ∘ 𝓥Label) x)
    ↔ ∃ (f : 𝓱𝓥To𝓥 ⁻¹' {x} → (vertexType ∘ 𝓥Label) x), Function.Bijective f :=
  Iff.intro
    (fun h ↦ match h with
            | ⟨f1, f2, h1, h2⟩ => ⟨f1, (isIso_iff_bijective f1).mp ⟨f2, h1, h2⟩⟩)
    (fun ⟨f1, hb⟩ ↦ match (isIso_iff_bijective f1).mpr hb with
                   | ⟨f2, h1, h2⟩ => ⟨f1, f2, h1, h2⟩)

instance {𝓱𝓔 𝓔 : Type} [DecidableEq 𝓔] (𝓱𝓔To𝓔 : 𝓱𝓔 → 𝓔) (x : 𝓔):
    DecidablePred (fun y => y ∈  𝓱𝓔To𝓔 ⁻¹' {x}) := fun y =>
  match decEq (𝓱𝓔To𝓔 y) x with
  | isTrue h => isTrue h
  | isFalse h => isFalse h


instance {𝓱𝓔 𝓔 : Type} [DecidableEq 𝓱𝓔]  (𝓱𝓔To𝓔 : 𝓱𝓔 → 𝓔) (x : 𝓔) :
    DecidableEq $ (𝓱𝓔To𝓔 ⁻¹' {x}) := Subtype.instDecidableEq

instance edgeTypeFintype (x : Fin 1) : Fintype (edgeType x) :=
  match x with
  | 0 => Fin.fintype 2

instance edgeTypeDecidableEq (x : Fin 1) : DecidableEq (edgeType x) :=
  match x with
  | 0 => instDecidableEqFin 2

instance vertexTypeFintype (x : Fin 2) : Fintype (vertexType x) :=
  match x with
  | 0 => Fin.fintype 1
  | 1 => Fin.fintype 4

instance vertexTypeDecidableEq (x : Fin 2) : DecidableEq (vertexType x) :=
  match x with
  | 0 => instDecidableEqFin 1
  | 1 => instDecidableEqFin 4

instance {𝓔 : Type} (𝓔Label : 𝓔 → Fin 1) (x : 𝓔) :
    DecidableEq ((edgeType ∘ 𝓔Label) x) := edgeTypeDecidableEq (𝓔Label x)

instance {𝓔 : Type} (𝓔Label : 𝓔 → Fin 1) (x : 𝓔) :
    Fintype ((edgeType ∘ 𝓔Label) x) := edgeTypeFintype (𝓔Label x)

instance {𝓥 : Type} (𝓥Label : 𝓥 → Fin 2) (x : 𝓥) :
    DecidableEq ((vertexType ∘ 𝓥Label) x) := vertexTypeDecidableEq (𝓥Label x)

instance {𝓥 : Type} (𝓥Label : 𝓥 → Fin 2) (x : 𝓥) :
    Fintype ((vertexType ∘ 𝓥Label) x) := vertexTypeFintype (𝓥Label x)


instance {𝓱𝓔 𝓔 : Type}  [Fintype 𝓱𝓔] [DecidableEq 𝓱𝓔] [DecidableEq 𝓔]
    (𝓱𝓔To𝓔 : 𝓱𝓔 → 𝓔) (𝓔Label : 𝓔 → Fin 1) (x : 𝓔) :
    Decidable (CategoryTheory.IsIsomorphic (𝓱𝓔To𝓔 ⁻¹' {x} : Type) $ (edgeType ∘ 𝓔Label) x) :=
  decidable_of_decidable_of_iff (fiber_cond_edge_iff_exists 𝓱𝓔To𝓔 𝓔Label x).symm

instance {𝓱𝓥 𝓥 : Type}  [Fintype 𝓱𝓥] [DecidableEq 𝓱𝓥] [DecidableEq 𝓥]
    (𝓱𝓥To𝓥 : 𝓱𝓥 → 𝓥) (𝓥Label : 𝓥 → Fin 2) (x : 𝓥) :
    Decidable (CategoryTheory.IsIsomorphic (𝓱𝓥To𝓥 ⁻¹' {x} : Type) $ (vertexType ∘ 𝓥Label) x) :=
  decidable_of_decidable_of_iff (fiber_cond_vertex_iff_exists 𝓱𝓥To𝓥 𝓥Label x).symm

end Decidability

section Finiteness
/-!
## Finiteness

As defined above our Feynman diagrams can have non-finite Types of half-edges etc.
We define the class of those Feynman diagrams which are `finite` in the appropriate sense.
In practice, every Feynman diagram considered in the physics literature is `finite`.

-/

/-- A Feynman diagram is said to be finite if its type of half-edges, edges and vertices
are  finite and decidable. -/
class IsFiniteDiagram (F : FeynmanDiagram) where
  /-- The type `𝓔` is finite. -/
  𝓔Fintype : Fintype F.𝓔
  /-- The type `𝓔` is decidable. -/
  𝓔DecidableEq : DecidableEq F.𝓔
  /-- The type `𝓥` is finite. -/
  𝓥Fintype : Fintype F.𝓥
  /-- The type `𝓥` is decidable. -/
  𝓥DecidableEq : DecidableEq F.𝓥
  /-- The type `𝓱𝓔` is finite. -/
  𝓱𝓔Fintype : Fintype F.𝓱𝓔
  /-- The type `𝓱𝓔` is decidable. -/
  𝓱𝓔DecidableEq : DecidableEq F.𝓱𝓔

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : Fintype F.𝓔 :=
  IsFiniteDiagram.𝓔Fintype

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : DecidableEq F.𝓔 :=
  IsFiniteDiagram.𝓔DecidableEq

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : Fintype F.𝓥 :=
  IsFiniteDiagram.𝓥Fintype

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : DecidableEq F.𝓥 :=
  IsFiniteDiagram.𝓥DecidableEq

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : Fintype F.𝓱𝓔 :=
  IsFiniteDiagram.𝓱𝓔Fintype

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : DecidableEq F.𝓱𝓔 :=
  IsFiniteDiagram.𝓱𝓔DecidableEq

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : Decidable (Nonempty F.𝓥) :=
  decidable_of_iff _ Finset.univ_nonempty_iff

end Finiteness

section categoryOfFeynmanDiagrams
/-!

## The category of Feynman diagrams

Feynman diagrams, as defined above, form a category.
We will be able to use this category to define the symmetry factor of a Feynman diagram,
and the condition on whether a diagram is connected.

-/
/-- A morphism between two `FeynmanDiagram`.  -/
structure Hom (F1 F2 : FeynmanDiagram) where
  /-- A morphism between half-edges. -/
  𝓱𝓔 : F1.𝓱𝓔 ⟶ F2.𝓱𝓔
  /-- A morphism between edges. -/
  𝓔 : F1.𝓔 ⟶ F2.𝓔
  /-- A morphism between vertices. -/
  𝓥 : F1.𝓥 ⟶ F2.𝓥
  /-- The morphism between edges must respect the labels. -/
  𝓔Label : F1.𝓔Label = F2.𝓔Label ∘ 𝓔
  /-- The morphism between vertices must respect the labels. -/
  𝓥Label : F1.𝓥Label = F2.𝓥Label ∘ 𝓥
  /-- The morphism between edges and half-edges must commute with `𝓱𝓔To𝓔`. -/
  𝓱𝓔To𝓔 : 𝓔 ∘ F1.𝓱𝓔To𝓔 = F2.𝓱𝓔To𝓔 ∘ 𝓱𝓔
  /-- The morphism between vertices and half-edges must commute with `𝓱𝓔To𝓥`. -/
  𝓱𝓔To𝓥 : 𝓥 ∘ F1.𝓱𝓔To𝓥 = F2.𝓱𝓔To𝓥 ∘ 𝓱𝓔

namespace Hom

lemma ext {F1 F2 : FeynmanDiagram} {f g : Hom F1 F2} (h1 : f.𝓱𝓔 = g.𝓱𝓔)
    (h2 : f.𝓔 = g.𝓔) (h3 : f.𝓥 = g.𝓥) : f = g := by
  cases f; cases g
  simp_all only

/-- The identity morphism from a Feynman diagram to itself. -/
@[simps!]
def id (F : FeynmanDiagram) : Hom F F where
  𝓱𝓔 := 𝟙 F.𝓱𝓔
  𝓔 := 𝟙 F.𝓔
  𝓥 := 𝟙 F.𝓥
  𝓔Label := rfl
  𝓥Label := rfl
  𝓱𝓔To𝓔 := rfl
  𝓱𝓔To𝓥 := rfl

/-- Composition of morphisms between Feynman diagrams. -/
@[simps!]
def comp {F1 F2 F3 : FeynmanDiagram} (f : Hom F1 F2)  (g : Hom F2 F3) : Hom F1 F3 where
  𝓱𝓔 :=  f.𝓱𝓔 ≫ g.𝓱𝓔
  𝓔 := f.𝓔 ≫ g.𝓔
  𝓥 := f.𝓥 ≫ g.𝓥
  𝓔Label := by
    ext
    simp [f.𝓔Label, g.𝓔Label]
  𝓥Label := by
    ext x
    simp [f.𝓥Label, g.𝓥Label]
  𝓱𝓔To𝓔 := by
    rw [types_comp, types_comp, Function.comp.assoc]
    rw [f.𝓱𝓔To𝓔, ← Function.comp.assoc, g.𝓱𝓔To𝓔]
    rfl
  𝓱𝓔To𝓥 := by
    rw [types_comp, types_comp, Function.comp.assoc]
    rw [f.𝓱𝓔To𝓥, ← Function.comp.assoc, g.𝓱𝓔To𝓥]
    rfl

/-- The condition on a triplet of maps for them to form a morphism of Feynman diagrams. -/
def Cond {F1 F2 : FeynmanDiagram} (f𝓱𝓔 : F1.𝓱𝓔 → F2.𝓱𝓔) (f𝓔 : F1.𝓔 → F2.𝓔)
    (f𝓥 :  F1.𝓥 → F2.𝓥) : Prop :=
  F1.𝓔Label = F2.𝓔Label ∘ f𝓔 ∧  F1.𝓥Label = F2.𝓥Label ∘ f𝓥 ∧
   f𝓔 ∘ F1.𝓱𝓔To𝓔 = F2.𝓱𝓔To𝓔 ∘ f𝓱𝓔 ∧  f𝓥 ∘ F1.𝓱𝓔To𝓥 = F2.𝓱𝓔To𝓥 ∘ f𝓱𝓔

instance {F1 F2 : FeynmanDiagram} [IsFiniteDiagram F1] [IsFiniteDiagram F2]
    (f𝓱𝓔 : F1.𝓱𝓔 → F2.𝓱𝓔) (f𝓔 : F1.𝓔 → F2.𝓔) (f𝓥 :  F1.𝓥 → F2.𝓥) :
    Decidable (Cond f𝓱𝓔 f𝓔 f𝓥) :=
  @And.decidable _ _ _ $
  @And.decidable _ _ _ $
  @And.decidable _ _ _ _

end Hom

@[simps!]
instance : Category FeynmanDiagram where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp


/-- The functor from the category of Feynman diagrams to `Type` taking a feynman diagram
  to its set of half-edges. -/
def toHalfEdges : FeynmanDiagram ⥤ Type where
  obj F := F.𝓱𝓔
  map f := f.𝓱𝓔

/-- The functor from the category of Feynman diagrams to `Type` taking a feynman diagram
  to its set of edges. -/
def toEdges : FeynmanDiagram ⥤ Type where
  obj F := F.𝓔
  map f := f.𝓔

/-- The functor from the category of Feynman diagrams to `Type` taking a feynman diagram
  to its set of vertices. -/
def toVertices : FeynmanDiagram ⥤ Type where
  obj F := F.𝓥
  map f := f.𝓥

lemma 𝓱𝓔_bijective_of_isIso {F1 F2 : FeynmanDiagram} (f : F1 ⟶ F2) [IsIso f] :
    f.𝓱𝓔.Bijective :=
  (isIso_iff_bijective f.𝓱𝓔).mp $ Functor.map_isIso toHalfEdges f

lemma 𝓔_bijective_of_isIso {F1 F2 : FeynmanDiagram} (f : F1 ⟶ F2) [IsIso f] :
    f.𝓔.Bijective :=
  (isIso_iff_bijective f.𝓔).mp $ Functor.map_isIso toEdges f

lemma 𝓥_bijective_of_isIso {F1 F2 : FeynmanDiagram} (f : F1 ⟶ F2) [IsIso f] :
    f.𝓥.Bijective :=
  (isIso_iff_bijective f.𝓥).mp $ Functor.map_isIso toVertices f

/-- An isomorphism formed from an equivalence between the types of half-edges, edges and vertices
  satisfying the appropriate conditions. -/
def mkIso {F1 F2 : FeynmanDiagram} (f𝓱𝓔 : F1.𝓱𝓔 ≃ F2.𝓱𝓔)
    (f𝓔 : F1.𝓔 ≃ F2.𝓔) (f𝓥 : F1.𝓥 ≃ F2.𝓥)
    (h𝓔Label : F1.𝓔Label = F2.𝓔Label ∘ f𝓔)
    (h𝓥Label : F1.𝓥Label = F2.𝓥Label ∘ f𝓥)
    (h𝓱𝓔To𝓔 : f𝓔 ∘ F1.𝓱𝓔To𝓔 = F2.𝓱𝓔To𝓔 ∘ f𝓱𝓔)
    (h𝓱𝓔To𝓥 : f𝓥 ∘ F1.𝓱𝓔To𝓥 = F2.𝓱𝓔To𝓥 ∘ f𝓱𝓔) : F1 ≅ F2 where
  hom := Hom.mk f𝓱𝓔 f𝓔 f𝓥 h𝓔Label h𝓥Label h𝓱𝓔To𝓔 h𝓱𝓔To𝓥
  inv := Hom.mk f𝓱𝓔.symm f𝓔.symm f𝓥.symm
    (((Iso.eq_inv_comp f𝓔.toIso).mpr h𝓔Label.symm).trans (types_comp _ _))
    (((Iso.eq_inv_comp f𝓥.toIso).mpr h𝓥Label.symm).trans (types_comp _ _))
    ((Iso.comp_inv_eq f𝓔.toIso).mpr $ (Iso.eq_inv_comp f𝓱𝓔.toIso).mpr $
       (types_comp _ _).symm.trans (Eq.trans h𝓱𝓔To𝓔.symm (types_comp _ _)))
    ((Iso.comp_inv_eq f𝓥.toIso).mpr $ (Iso.eq_inv_comp f𝓱𝓔.toIso).mpr $
       (types_comp _ _).symm.trans (Eq.trans h𝓱𝓔To𝓥.symm (types_comp _ _)))
  hom_inv_id := by
    apply Hom.ext
    ext a
    simp only [instCategory_comp_𝓱𝓔, Equiv.symm_apply_apply, instCategory_id_𝓱𝓔]
    ext a
    simp only [instCategory_comp_𝓔, Equiv.symm_apply_apply, instCategory_id_𝓔]
    ext a
    simp only [instCategory_comp_𝓥, Equiv.symm_apply_apply, instCategory_id_𝓥]
  inv_hom_id := by
    apply Hom.ext
    ext a
    simp only [instCategory_comp_𝓱𝓔, Equiv.apply_symm_apply, instCategory_id_𝓱𝓔]
    ext a
    simp only [instCategory_comp_𝓔, Equiv.apply_symm_apply, instCategory_id_𝓔]
    ext a
    simp only [instCategory_comp_𝓥, Equiv.apply_symm_apply, instCategory_id_𝓥]

lemma isIso_of_bijections {F1 F2 : FeynmanDiagram} (f : F1 ⟶ F2)
    (h𝓱𝓔 : f.𝓱𝓔.Bijective) (h𝓔 : f.𝓔.Bijective) (h𝓥 : f.𝓥.Bijective) :
    IsIso f :=
  Iso.isIso_hom $ mkIso (Equiv.ofBijective f.𝓱𝓔 h𝓱𝓔) (Equiv.ofBijective f.𝓔 h𝓔)
    (Equiv.ofBijective f.𝓥 h𝓥) f.𝓔Label f.𝓥Label f.𝓱𝓔To𝓔 f.𝓱𝓔To𝓥


lemma isIso_iff_all_bijective {F1 F2 : FeynmanDiagram} (f : F1 ⟶ F2) :
    IsIso f ↔ f.𝓱𝓔.Bijective ∧ f.𝓔.Bijective ∧ f.𝓥.Bijective :=
  Iff.intro
    (fun _ ↦ ⟨𝓱𝓔_bijective_of_isIso f, 𝓔_bijective_of_isIso f, 𝓥_bijective_of_isIso f⟩)
    (fun ⟨h𝓱𝓔, h𝓔, h𝓥⟩ ↦ isIso_of_bijections f h𝓱𝓔 h𝓔 h𝓥)

/-- An equivalence between the isomorphism class of a Feynman diagram an
  permutations of the half-edges, edges and vertices satisfying the `Hom.cond`. -/
def isoEquivBijec {F : FeynmanDiagram} :
    (F ≅ F) ≃ {S : Equiv.Perm F.𝓱𝓔 × Equiv.Perm F.𝓔 × Equiv.Perm F.𝓥 //
      Hom.Cond S.1 S.2.1 S.2.2} where
  toFun f := ⟨⟨(toHalfEdges.mapIso f).toEquiv,
    (toEdges.mapIso f).toEquiv , (toVertices.mapIso f).toEquiv⟩,
    f.hom.𝓔Label, f.hom.𝓥Label, f.hom.𝓱𝓔To𝓔, f.hom.𝓱𝓔To𝓥⟩
  invFun S := mkIso S.1.1 S.1.2.1 S.1.2.2 S.2.1 S.2.2.1 S.2.2.2.1 S.2.2.2.2
  left_inv _ := rfl
  right_inv _ := rfl

instance {F : FeynmanDiagram} [IsFiniteDiagram F]  :
    Fintype (F ≅ F)  :=
  Fintype.ofEquiv _ isoEquivBijec.symm

end categoryOfFeynmanDiagrams

section symmetryFactors
/-!
## Symmetry factors

The symmetry factor of a Feynman diagram is the cardinality of the group of automorphisms of that
diagram. In this section we define symmetry factors for Feynman diagrams which are
finite.

-/

/-- The symmetry factor is the cardinality of the set of isomorphisms of the Feynman diagram. -/
def symmetryFactor (F : FeynmanDiagram) [IsFiniteDiagram F] : ℕ :=
  Fintype.card (F ≅ F)

end symmetryFactors

section connectedness
/-!

## Connectedness

Given a Feynman diagram we can create a simple graph based on the obvious adjacency relation.
A feynman diagram is connected if its simple graph is connected.

-/

/-- A relation on the vertices of Feynman diagrams. The proposition is true if the two
 vertices are not equal and are connected by a single edge. -/
@[simp]
def adjRelation (F : FeynmanDiagram) : F.𝓥 → F.𝓥 → Prop := fun x y =>
  x ≠ y ∧
  ∃ (a b : F.𝓱𝓔), F.𝓱𝓔To𝓔 a = F.𝓱𝓔To𝓔 b ∧ F.𝓱𝓔To𝓥 a = x ∧ F.𝓱𝓔To𝓥 b = y

/-- From a Feynman diagram the simple graph showing those vertices which are connected. -/
def toSimpleGraph (F : FeynmanDiagram) : SimpleGraph F.𝓥 where
  Adj := adjRelation F
  symm := by
    intro x y h
    apply And.intro (Ne.symm h.1)
    obtain ⟨a, b, hab⟩ := h.2
    exact ⟨b, a, ⟨hab.1.symm, hab.2.2, hab.2.1⟩⟩
  loopless := by
    intro x h
    simp at h

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : DecidableRel F.toSimpleGraph.Adj := fun _ _ =>
   And.decidable

instance {F : FeynmanDiagram} [IsFiniteDiagram F]  :
  Decidable (F.toSimpleGraph.Preconnected ∧ Nonempty F.𝓥) :=
  @And.decidable _ _ _ _

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : Decidable F.toSimpleGraph.Connected :=
  decidable_of_iff _ (SimpleGraph.connected_iff F.toSimpleGraph).symm

/-- We say a Feynman diagram is connected if its simple graph is connected. -/
def Connected (F : FeynmanDiagram) : Prop := F.toSimpleGraph.Connected

instance {F : FeynmanDiagram} [IsFiniteDiagram F] : Decidable (Connected F) :=
  PhiFour.FeynmanDiagram.instDecidableConnected𝓥ToSimpleGraphOfIsFiniteDiagram

end connectedness

section examples
/-!

## Examples

In this section we give examples of Feynman diagrams in Phi^4 theory.

Symmetry factors can be compared with e.g. those in
- https://arxiv.org/abs/0907.0859

-/

/-- The propagator
  - - - - - -

 -/
def propagator : FeynmanDiagram where
  𝓱𝓔 := Fin 2
  𝓔 := Fin 1
  𝓔Label  := ![0]
  𝓱𝓔To𝓔 := ![0, 0]
  𝓔Fiber := by decide
  𝓥 := Fin 2
  𝓥Label := ![0, 0]
  𝓱𝓔To𝓥 := ![0, 1]
  𝓥Fiber := by decide

instance : IsFiniteDiagram propagator where
  𝓔Fintype := Fin.fintype 1
  𝓔DecidableEq := instDecidableEqFin 1
  𝓥Fintype := Fin.fintype 2
  𝓥DecidableEq := instDecidableEqFin 2
  𝓱𝓔Fintype := Fin.fintype 2
  𝓱𝓔DecidableEq := instDecidableEqFin 2

lemma propagator_symmetryFactor : symmetryFactor propagator = 2 := by
  decide

/-- The figure 8 Feynman diagram
     _
   /    \
  /      \
  \      /
   \    /
    \  /
    /  \
   /    \
  \      /
   \ __ /  -/
@[simps!]
def figureEight : FeynmanDiagram where
  𝓱𝓔 := Fin 4
  𝓔 := Fin 2
  𝓔Label  := ![0, 0]
  𝓱𝓔To𝓔 := ![0, 0, 1, 1]
  𝓔Fiber := by decide
  𝓥 := Fin 1
  𝓥Label := ![1]
  𝓱𝓔To𝓥 := ![0, 0, 0, 0]
  𝓥Fiber := by decide

instance : IsFiniteDiagram figureEight where
  𝓔Fintype := Fin.fintype 2
  𝓔DecidableEq := instDecidableEqFin 2
  𝓥Fintype := Fin.fintype 1
  𝓥DecidableEq := instDecidableEqFin 1
  𝓱𝓔Fintype := Fin.fintype 4
  𝓱𝓔DecidableEq := instDecidableEqFin 4


lemma figureEight_connected : Connected figureEight := by
  decide

lemma figureEight_symmetryFactor : symmetryFactor figureEight = 8 := by
  decide

/-- The feynman diagram
        _ _ _ _ _
     /           \
    /             \
 - - - - - - - - - - - -
    \             /
     \ _ _ _ _ _/
-/
def diagram1 : FeynmanDiagram where
  𝓱𝓔 := Fin 10
  𝓔 := Fin 5
  𝓔Label  := ![0, 0, 0, 0, 0]
  𝓱𝓔To𝓔 := ![0, 0, 1, 1, 2, 2, 3, 3, 4, 4]
  𝓔Fiber := by decide
  𝓥 := Fin 4
  𝓥Label := ![0, 1, 1, 0]
  𝓱𝓔To𝓥 := ![0, 1, 1, 2, 1, 2, 1, 2, 2, 3]
  𝓥Fiber := by decide

/-- An example of a disconnected Feynman diagram. -/
def diagram2 : FeynmanDiagram where
  𝓱𝓔 := Fin 14
  𝓔 := Fin 7
  𝓔Label := ![0, 0, 0, 0, 0, 0, 0]
  𝓱𝓔To𝓔 := ![0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6]
  𝓔Fiber := by decide
  𝓥 := Fin 5
  𝓥Label := ![0, 0, 1, 1, 1]
  𝓱𝓔To𝓥 := ![0, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4]
  𝓥Fiber := by decide

instance : IsFiniteDiagram diagram2 where
  𝓔Fintype := Fin.fintype _
  𝓔DecidableEq := instDecidableEqFin _
  𝓥Fintype := Fin.fintype _
  𝓥DecidableEq := instDecidableEqFin _
  𝓱𝓔Fintype := Fin.fintype _
  𝓱𝓔DecidableEq := instDecidableEqFin _

lemma diagram2_not_connected : ¬ Connected diagram2 := by
  decide



end examples

end FeynmanDiagram

end PhiFour
