/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Card
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.Data.Fintype.Pi
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.SetTheory.Cardinal.Basic
/-!
# Feynman diagrams

Feynman diagrams are a graphical representation of the terms in the perturbation expansion of
a quantum field theory.


-/

open CategoryTheory
/-!

## The definition of Pre Feynman rules

We define the notion of a pre-Feynman rule, which specifies the possible
half-edges, edges and vertices in a diagram. It does not specify how to turn a diagram
into an algebraic expression.

## TODO
Prove that the `halfEdgeLimit` functor lands on limits of functors.

-/

/-- A `PreFeynmanRule` is a set of rules specifying the allowed half-edges,
  edges and vertices in a diagram. (It does not specify how to turn the diagram
  into an algebraic expression.) -/
structure PreFeynmanRule where
  /-- The type labelling the different half-edges. -/
  HalfEdgeLabel : Type
  /-- A type labelling the different types of edges. -/
  EdgeLabel : Type
  /-- A type labelling the different types of vertices. -/
  VertexLabel : Type
  /-- A function taking `EdgeLabels` to the half edges it contains. -/
  edgeLabelMap : EdgeLabel → CategoryTheory.Over HalfEdgeLabel
  /-- A function taking `VertexLabels` to the half edges it contains. -/
  vertexLabelMap : VertexLabel → CategoryTheory.Over HalfEdgeLabel

namespace PreFeynmanRule

variable (P : PreFeynmanRule)

/-- The functor from `Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)`
  to `Over (P.VertexLabel)` induced by projections on products. -/
@[simps!]
def toVertex {𝓔 𝓥 : Type} : Over (P.HalfEdgeLabel × 𝓔 × 𝓥) ⥤ Over 𝓥 :=
  Over.map <| Prod.snd ∘ Prod.snd

/-- The functor from `Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)`
  to `Over (P.EdgeLabel)` induced by projections on products. -/
@[simps!]
def toEdge {𝓔 𝓥 : Type} : Over (P.HalfEdgeLabel × 𝓔 × 𝓥) ⥤ Over 𝓔 :=
  Over.map <| Prod.fst ∘ Prod.snd

/-- The functor from `Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)`
  to `Over (P.HalfEdgeLabel)` induced by projections on products. -/
@[simps!]
def toHalfEdge {𝓔 𝓥 : Type}  : Over (P.HalfEdgeLabel × 𝓔 × 𝓥) ⥤ Over P.HalfEdgeLabel :=
  Over.map Prod.fst

/-- The functor from `Over P.VertexLabel` to `Type` induced by pull-back along insertion of
  `v : P.VertexLabel`. -/
@[simps!]
def preimageType' {𝓥 : Type} (v : 𝓥) : Over 𝓥 ⥤ Type where
  obj := fun f =>  f.hom ⁻¹' {v}
  map {f g} F := fun x =>
    ⟨F.left x.1, by
      have h := congrFun F.w x
      simp only [Functor.const_obj_obj, Functor.id_obj, Functor.id_map, types_comp_apply,
        CostructuredArrow.right_eq_id, Functor.const_obj_map, types_id_apply] at h
      simpa [h] using x.2⟩

/-- The functor from `Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)` to
  `Over P.HalfEdgeLabel` induced by pull-back along insertion of `v : P.VertexLabel`.  -/
def preimageVertex  {𝓔 𝓥 : Type} (v : 𝓥) :
    Over (P.HalfEdgeLabel × 𝓔 × 𝓥) ⥤ Over P.HalfEdgeLabel where
  obj f := Over.mk (fun x =>  Prod.fst (f.hom x.1) :
     (P.toVertex ⋙ preimageType' v).obj f ⟶ P.HalfEdgeLabel)
  map {f g} F := Over.homMk ((P.toVertex ⋙ preimageType' v).map F)
    (funext <| fun x => congrArg Prod.fst <| congrFun F.w x.1)

/-- The functor from `Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)` to
  `Over P.HalfEdgeLabel` induced by pull-back along insertion of `v : P.EdgeLabel`.  -/
def preimageEdge {𝓔 𝓥 : Type} (v : 𝓔) :
    Over (P.HalfEdgeLabel ×  𝓔 × 𝓥) ⥤ Over P.HalfEdgeLabel where
  obj f := Over.mk (fun x =>  Prod.fst (f.hom x.1) :
     (P.toEdge ⋙ preimageType' v).obj f ⟶ P.HalfEdgeLabel)
  map {f g} F := Over.homMk ((P.toEdge ⋙ preimageType' v).map F)
    (funext <| fun x => congrArg Prod.fst <| congrFun F.w x.1)

/-- The proposition on vertices which must be satisfied by an object
  `F : Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)` for it to be a Feynman diagram.
  This condition corresponds to the vertices of `F` having the correct half-edges associated
  with them. -/
def diagramVertexProp {𝓔 𝓥 : Type} (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥))
    (f : 𝓥 ⟶ P.VertexLabel) :=
  ∀ v, IsIsomorphic (P.vertexLabelMap (f v)) ((P.preimageVertex v).obj F)


/-- The proposition on edges which must be satisfied by an object
  `F : Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)` for it to be a Feynman diagram.
  This condition corresponds to the edges of `F` having the correct half-edges associated
  with them. -/
def diagramEdgeProp {𝓔 𝓥 : Type} (F : Over (P.HalfEdgeLabel  × 𝓔 × 𝓥))
    (f : 𝓔 ⟶ P.EdgeLabel) :=
  ∀ v, IsIsomorphic (P.edgeLabelMap (f v)) ((P.preimageEdge v).obj F)

/-- The proposition which must be satisfied by an object
  `F : Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)` for it to be a Feynman diagram. cs-/
def diagramProp {𝓔 𝓥 : Type} (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥))
  (f𝓔 : 𝓔 ⟶ P.EdgeLabel) (f𝓥 :  𝓥 ⟶ P.VertexLabel) :=
  diagramVertexProp P F f𝓥 ∧ diagramEdgeProp P F f𝓔

end PreFeynmanRule

/-!

## The definition of Feynman diagrams

We now define the type of Feynman diagrams for a given pre-Feynman rule.

-/

open PreFeynmanRule

/-- The type of Feynman diagrams given a `PreFeynmanRule`. -/
structure FeynmanDiagram (P : PreFeynmanRule) where
  /-- The type of edges in the Feynman diagram, labelled by their type. -/
  𝓔𝓞 : Over P.EdgeLabel
  /-- The type of vertices in the Feynman diagram, labelled by their type. -/
  𝓥𝓞 : Over P.VertexLabel
  /-- The type of half-edges in the Feynman diagram, labelled by their type, the edge it
  belongs to, and the vertex they belong to. -/
  𝓱𝓔To𝓔𝓥 : Over (P.HalfEdgeLabel × 𝓔𝓞.left × 𝓥𝓞.left)
  /-- Each edge has the correct type of half edges. -/
  𝓔Cond : P.diagramEdgeProp 𝓱𝓔 𝓔𝓞.hom
  /-- Each vertex has the correct sort of half edges. -/
  𝓥Cond : P.diagramVertexProp 𝓱𝓔 𝓥𝓞.hom

namespace FeynmanDiagram

variable {P : PreFeynmanRule} (F : FeynmanDiagram P)

/-- The type of edges. -/
def 𝓔 : Type := F.𝓔𝓞.left

/-- The type of vertices. -/
def 𝓥 : Type := F.𝓥𝓞.left

/-- The type of half-edges. -/
def 𝓱𝓔 : Type := F.𝓱𝓔To𝓔𝓥.left

/-- The object in Over P.HalfEdgeLabel generated by a Feynman diagram. -/
def 𝓱𝓔𝓞 : Over P.HalfEdgeLabel := P.toHalfEdge.obj F.𝓱𝓔To𝓔𝓥

/-- Given two maps `F.𝓔𝓞 ⟶ G.𝓔𝓞` and `F.𝓥𝓞 ⟶ G.𝓥𝓞` the corresponding map
  `P.HalfEdgeLabel × F.𝓔𝓞.left × F.𝓥𝓞.left →  P.HalfEdgeLabel × G.𝓔𝓞.left × G.𝓥𝓞.left`.  -/
def edgeVertexMap {F G : FeynmanDiagram P} (𝓔 : F.𝓔𝓞 ⟶ G.𝓔𝓞) (𝓥 : F.𝓥𝓞 ⟶ G.𝓥𝓞) :
    P.HalfEdgeLabel × F.𝓔𝓞.left × F.𝓥𝓞.left →  P.HalfEdgeLabel × G.𝓔𝓞.left × G.𝓥𝓞.left :=
  fun x => ⟨x.1, 𝓔.left x.2.1, 𝓥.left x.2.2⟩

/-- The functor of over-categories generated by `edgeVertexMap`. -/
def edgeVertexFunc {F G : FeynmanDiagram P} (𝓔 : F.𝓔𝓞 ⟶ G.𝓔𝓞) (𝓥 : F.𝓥𝓞 ⟶ G.𝓥𝓞) :
   Over (P.HalfEdgeLabel × F.𝓔𝓞.left × F.𝓥𝓞.left)
   ⥤ Over (P.HalfEdgeLabel × G.𝓔𝓞.left × G.𝓥𝓞.left) :=
  Over.map <| edgeVertexMap 𝓔 𝓥

/-- A morphism of Feynman diagrams. -/
structure Hom (F G : FeynmanDiagram P) where
  /-- The morphism of edge objects. -/
  𝓔 : F.𝓔𝓞 ⟶ G.𝓔𝓞
  /-- The morphism of vertex objects. -/
  𝓥 : F.𝓥𝓞 ⟶ G.𝓥𝓞
  /-- The morphism of half-edge objects. -/
  𝓱𝓔 : (edgeVertexFunc 𝓔 𝓥).obj F.𝓱𝓔To𝓔𝓥 ⟶ G.𝓱𝓔To𝓔𝓥

namespace Hom

/-- The identity morphism for a Feynman diagram. -/
def id (F : FeynmanDiagram P) : Hom F F where
  𝓔 := 𝟙 F.𝓔𝓞
  𝓥 := 𝟙 F.𝓥𝓞
  𝓱𝓔 := 𝟙 F.𝓱𝓔To𝓔𝓥

/-- The composition of two morphisms of Feynman diagrams. -/
def comp {F G H : FeynmanDiagram P} (f : Hom F G) (g : Hom G H) : Hom F H where
  𝓔 := f.𝓔 ≫ g.𝓔
  𝓥 := f.𝓥 ≫ g.𝓥
  𝓱𝓔 := (edgeVertexFunc g.𝓔 g.𝓥).map f.𝓱𝓔 ≫ g.𝓱𝓔

lemma ext {F G : FeynmanDiagram P} {f g : Hom F G} (h𝓔 : f.𝓔 = g.𝓔)
    (h𝓥 : f.𝓥 = g.𝓥) (h𝓱𝓔 : f.𝓱𝓔.left = g.𝓱𝓔.left) : f = g := by
  cases f
  cases g
  subst h𝓔 h𝓥
  simp_all only [mk.injEq, heq_eq_eq, true_and]
  ext a : 2
  simp_all only

end Hom

/-- Feynman diagrams form a category. -/
instance : Category (FeynmanDiagram P) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- The functor from Feynman diagrams to category over edge labels. -/
def toOverEdgeLabel : FeynmanDiagram P ⥤ Over P.EdgeLabel where
  obj F := F.𝓔𝓞
  map f := f.𝓔

/-- The functor from Feynman diagrams to category over vertex labels. -/
def toOverVertexLabel : FeynmanDiagram P ⥤ Over P.VertexLabel where
  obj F := F.𝓥𝓞
  map f := f.𝓥

/-- The functor from Feynman diagrams to category over half-edge labels. -/
def toOverHalfEdgeLabel : FeynmanDiagram P ⥤ Over P.HalfEdgeLabel where
  obj F := F.𝓱𝓔𝓞
  map f := P.toHalfEdge.map f.𝓱𝓔

/-- The type of isomorphisms of a Feynman diagram. -/
def symmetryType : Type := F ≅ F

/-- The symmetry factor can be defined as the cardinal of the symmetry type.
 In general this is not a finite number. -/
def symmetryFactor : Cardinal := Cardinal.mk (F.symmetryType)


end FeynmanDiagram
