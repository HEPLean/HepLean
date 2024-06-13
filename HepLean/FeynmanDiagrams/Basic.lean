/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Card
import Mathlib.CategoryTheory.IsomorphismClasses
import LeanCopilot
/-!
# Feynman diagrams in Phi^4 theory

The aim of this file is to start building up the theory of Feynman diagrams in the context of
Phi^4 theory.

-/

namespace PhiFour

/-- The type of vacuum Feynman diagrams for Phi-4 theory. -/
structure VacuumFeynmanDiagram where
  HalfEdge : Type
  Edge : Type
  Vertex : Type
  𝓔 : HalfEdge → Edge
  𝓥 : HalfEdge → Vertex
  𝓔Fiber : ∀ x,  CategoryTheory.IsIsomorphic (𝓔 ⁻¹' {x} : Type) (Fin 2)
  𝓥Fiber : ∀ x,  CategoryTheory.IsIsomorphic (𝓥 ⁻¹' {x} : Type) (Fin 3)



namespace VacuumFeynmanDiagram

open CategoryTheory

variable (F G : VacuumFeynmanDiagram)

/-- The definition of a morphism between two `VacuumFeynmanDiagram`. -/
structure Hom where
  halfEdgeMap : F.HalfEdge ⟶ G.HalfEdge
  edgeMap : F.Edge ⟶ G.Edge
  vertexMap : F.Vertex ⟶ G.Vertex

namespace Hom

/-- The identity morphism for an object in `VacuumFeynmanDiagram`. -/
def id : Hom F F where
  halfEdgeMap := 𝟙 F.HalfEdge
  edgeMap := 𝟙 F.Edge
  vertexMap := 𝟙 F.Vertex

/-- The composition of morphisms between two `VacuumFeynmanDiagram`. -/
def comp {F G H : VacuumFeynmanDiagram} (f : Hom F G) (g : Hom G H) : Hom F H where
  halfEdgeMap := f.halfEdgeMap ≫ g.halfEdgeMap
  edgeMap := f.edgeMap ≫ g.edgeMap
  vertexMap := f.vertexMap ≫ g.vertexMap

end Hom

/-- `VacuumFeynmanDiagram` has the structure of a category. -/
instance : Category VacuumFeynmanDiagram where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- The functor from the category `VacuumFeynmanDiagram` to `Type` defined by
  mapping to the `Type` of half edges.  -/
def toHalfEdge : VacuumFeynmanDiagram ⥤ Type where
  obj F := F.HalfEdge
  map f := f.halfEdgeMap

@[simp]
lemma 𝓔_preimage_nonempty (x : F.Edge) : (F.𝓔 ⁻¹' {x}).Nonempty := by
  obtain ⟨_, f, _, _⟩ := F.𝓔Fiber x
  exact ⟨f 0,  Subtype.coe_prop (f 0)⟩

@[simp]
lemma 𝓥_preimage_nonempty (x : F.Vertex) : (F.𝓥 ⁻¹' {x}).Nonempty := by
  obtain ⟨_, f, _, _⟩ := F.𝓥Fiber x
  exact ⟨f 0,  Subtype.coe_prop (f 0)⟩

@[simp]
lemma 𝓔_surjective : Function.Surjective F.𝓔 := by
  exact fun x => F.𝓔_preimage_nonempty x

@[simp]
lemma 𝓥_surjective : Function.Surjective F.𝓥 := by
  exact fun x => F.𝓥_preimage_nonempty x


end VacuumFeynmanDiagram


end PhiFour
