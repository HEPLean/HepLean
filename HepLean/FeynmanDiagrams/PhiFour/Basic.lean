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
- Define the symmetry factor and compute for examples of Feynman diagrams.
- Define the Feynman rules, and perform an example calculation.

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

section examples
/-!

## Examples

In this section we give examples of Feynman diagrams in Phi^4 theory.


--/

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

/-- The feynman diagram
        _ _ _ _ _
     /           \
    /             \
 - - - - - - - - - - - -
    \             /
     \  _ _ _ _ _/
-/
def propagtor1 : FeynmanDiagram where
  𝓱𝓔 := Fin 10
  𝓔 := Fin 5
  𝓔Label  := ![0, 0, 0, 0, 0]
  𝓱𝓔To𝓔 := ![0, 0, 1, 1, 2, 2, 3, 3, 4, 4]
  𝓔Fiber := by decide
  𝓥 := Fin 4
  𝓥Label := ![0, 1, 1, 0]
  𝓱𝓔To𝓥 := ![0, 1, 1, 2, 1, 2, 1, 2, 2, 3]
  𝓥Fiber := by decide


end examples

end FeynmanDiagram

end PhiFour
