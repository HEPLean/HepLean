/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.FinCases
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
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
  /-- The type labelling the different types of half-edges. -/
  HalfEdgeLabel : Type
  /-- A type labelling the different types of edges. -/
  EdgeLabel : Type
  /-- A type labelling the different types of vertices. -/
  VertexLabel : Type
  /-- A function taking `EdgeLabels` to the half edges it contains.
    This will usually land on `Fin 2 → _` -/
  edgeLabelMap : EdgeLabel → CategoryTheory.Over HalfEdgeLabel
  /-- A function taking `VertexLabels` to the half edges it contains.
    For example, if the vertex is of order-3 it will land on `Fin 3 → _`. -/
  vertexLabelMap : VertexLabel → CategoryTheory.Over HalfEdgeLabel

namespace PreFeynmanRule

variable (P : PreFeynmanRule)

/-- The functor from `Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)`
  to `Over (P.VertexLabel)` induced by projections on products. -/
def toVertex {𝓔 𝓥 : Type} : Over (P.HalfEdgeLabel × 𝓔 × 𝓥) ⥤ Over 𝓥 :=
  Over.map <| Prod.snd ∘ Prod.snd

/-- The functor from `Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)`
  to `Over (P.EdgeLabel)` induced by projections on products. -/
@[simps! obj_left obj_hom map_left map_right]
def toEdge {𝓔 𝓥 : Type} : Over (P.HalfEdgeLabel × 𝓔 × 𝓥) ⥤ Over 𝓔 :=
  Over.map <| Prod.fst ∘ Prod.snd

/-- The functor from `Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)`
  to `Over (P.HalfEdgeLabel)` induced by projections on products. -/
@[simps! obj_left obj_hom map_left map_right]
def toHalfEdge {𝓔 𝓥 : Type} : Over (P.HalfEdgeLabel × 𝓔 × 𝓥) ⥤ Over P.HalfEdgeLabel :=
  Over.map Prod.fst

/-- The functor from `Over P.VertexLabel` to `Type` induced by pull-back along insertion of
  `v : P.VertexLabel`. -/
@[simps!]
def preimageType' {𝓥 : Type} (v : 𝓥) : Over 𝓥 ⥤ Type where
  obj := fun f => f.hom ⁻¹' {v}
  map {f g} F := fun x =>
    ⟨F.left x.1, by
      have h := congrFun F.w x
      simp only [Functor.const_obj_obj, Functor.id_obj, Functor.id_map, types_comp_apply,
        CostructuredArrow.right_eq_id, Functor.const_obj_map, types_id_apply] at h
      simp only [Functor.id_obj, Functor.const_obj_obj, Set.mem_preimage, Set.mem_singleton_iff]
      obtain ⟨val, property⟩ := x
      simp_all only
      simp_all only [Functor.id_obj, Functor.const_obj_obj, Set.mem_preimage,
        Set.mem_singleton_iff]⟩

/-- The functor from `Over (P.HalfEdgeLabel × 𝓔 × 𝓥)` to
  `Over P.HalfEdgeLabel` induced by pull-back along insertion of `v : P.VertexLabel`.
  For a given vertex, it returns all half edges corresponding to that vertex. -/
def preimageVertex {𝓔 𝓥 : Type} (v : 𝓥) :
    Over (P.HalfEdgeLabel × 𝓔 × 𝓥) ⥤ Over P.HalfEdgeLabel where
  obj f := Over.mk (fun x => Prod.fst (f.hom x.1) :
      (P.toVertex ⋙ preimageType' v).obj f ⟶ P.HalfEdgeLabel)
  map {f g} F := Over.homMk ((P.toVertex ⋙ preimageType' v).map F)
    (funext <| fun x => congrArg Prod.fst <| congrFun F.w x.1)

/-- The functor from `Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)` to
  `Over P.HalfEdgeLabel` induced by pull-back along insertion of `v : P.EdgeLabel`.
  For a given edge, it returns all half edges corresponding to that edge. -/
def preimageEdge {𝓔 𝓥 : Type} (v : 𝓔) :
    Over (P.HalfEdgeLabel × 𝓔 × 𝓥) ⥤ Over P.HalfEdgeLabel where
  obj f := Over.mk (fun x => Prod.fst (f.hom x.1) :
      (P.toEdge ⋙ preimageType' v).obj f ⟶ P.HalfEdgeLabel)
  map {f g} F := Over.homMk ((P.toEdge ⋙ preimageType' v).map F)
    (funext <| fun x => congrArg Prod.fst <| congrFun F.w x.1)

/-!

## Finiteness of pre-Feynman rules

We define a class of `PreFeynmanRule` which have nice properties with regard to
decidability and finiteness.

In practice, every pre-Feynman rule considered in the physics literature satisfies these
properties.

-/

/-- A set of conditions on `PreFeynmanRule` for it to be considered finite. -/
class IsFinitePreFeynmanRule (P : PreFeynmanRule) where
  /-- The type of edge labels is decidable. -/
  edgeLabelDecidable : DecidableEq P.EdgeLabel
  /-- The type of vertex labels is decidable. -/
  vertexLabelDecidable : DecidableEq P.VertexLabel
  /-- The type of half-edge labels is decidable. -/
  halfEdgeLabelDecidable : DecidableEq P.HalfEdgeLabel
  /-- The type of half-edges associated with a vertex is finite. -/
  vertexMapFintype : ∀ v : P.VertexLabel, Fintype (P.vertexLabelMap v).left
  /-- The type of half-edges associated with a vertex is decidable. -/
  vertexMapDecidable : ∀ v : P.VertexLabel, DecidableEq (P.vertexLabelMap v).left
  /-- The type of half-edges associated with an edge is finite. -/
  edgeMapFintype : ∀ v : P.EdgeLabel, Fintype (P.edgeLabelMap v).left
  /-- The type of half-edges associated with an edge is decidable. -/
  edgeMapDecidable : ∀ v : P.EdgeLabel, DecidableEq (P.edgeLabelMap v).left

/-- If `P` is a finite pre feynman rule, then equality of edge labels of `P` is decidable. -/
instance preFeynmanRuleDecEq𝓔 (P : PreFeynmanRule) [IsFinitePreFeynmanRule P] :
    DecidableEq P.EdgeLabel :=
  IsFinitePreFeynmanRule.edgeLabelDecidable

/-- If `P` is a finite pre feynman rule, then equality of vertex labels of `P` is decidable. -/
instance preFeynmanRuleDecEq𝓥 (P : PreFeynmanRule) [IsFinitePreFeynmanRule P] :
    DecidableEq P.VertexLabel :=
  IsFinitePreFeynmanRule.vertexLabelDecidable

/-- If `P` is a finite pre feynman rule, then equality of half-edge labels of `P` is decidable. -/
instance preFeynmanRuleDecEq𝓱𝓔 (P : PreFeynmanRule) [IsFinitePreFeynmanRule P] :
    DecidableEq P.HalfEdgeLabel :=
  IsFinitePreFeynmanRule.halfEdgeLabelDecidable

/-- If `P` is a finite pre-feynman rule, then every vertex has a finite
  number of half-edges associated to it. -/
instance [IsFinitePreFeynmanRule P] (v : P.VertexLabel) : Fintype (P.vertexLabelMap v).left :=
  IsFinitePreFeynmanRule.vertexMapFintype v

/-- If `P` is a finite pre-feynman rule, then the indexing set of half-edges associated
  to a vertex is decidable. -/
instance [IsFinitePreFeynmanRule P] (v : P.VertexLabel) : DecidableEq (P.vertexLabelMap v).left :=
  IsFinitePreFeynmanRule.vertexMapDecidable v

/-- If `P` is a finite pre-feynman rule, then every edge has a finite
  number of half-edges associated to it. -/
instance [IsFinitePreFeynmanRule P] (v : P.EdgeLabel) : Fintype (P.edgeLabelMap v).left :=
  IsFinitePreFeynmanRule.edgeMapFintype v

/-- If `P` is a finite pre-feynman rule, then the indexing set of half-edges associated
  to an edge is decidable. -/
instance [IsFinitePreFeynmanRule P] (v : P.EdgeLabel) : DecidableEq (P.edgeLabelMap v).left :=
  IsFinitePreFeynmanRule.edgeMapDecidable v

/-- It is decidable to check whether a half edge of a diagram (an object in
  `Over (P.HalfEdgeLabel × 𝓔 × 𝓥)`) corresponds to a given vertex. -/
instance preimageVertexDecidablePred {𝓔 𝓥 : Type} [DecidableEq 𝓥] (v : 𝓥)
    (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥)) :
    DecidablePred fun x => x ∈ (P.toVertex.obj F).hom ⁻¹' {v} := fun y =>
  match decEq ((P.toVertex.obj F).hom y) v with
  | isTrue h => isTrue h
  | isFalse h => isFalse h

/-- It is decidable to check whether a half edge of a diagram (an object in
  `Over (P.HalfEdgeLabel × 𝓔 × 𝓥)`) corresponds to a given edge. -/
instance preimageEdgeDecidablePred {𝓔 𝓥 : Type} [DecidableEq 𝓔] (v : 𝓔)
    (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥)) :
    DecidablePred fun x => x ∈ (P.toEdge.obj F).hom ⁻¹' {v} := fun y =>
  match decEq ((P.toEdge.obj F).hom y) v with
  | isTrue h => isTrue h
  | isFalse h => isFalse h

/-- If `F` is an object in `Over (P.HalfEdgeLabel × 𝓔 × 𝓥)`, with a decidable source,
  then the object in `Over P.HalfEdgeLabel` formed by following the functor `preimageVertex`
  has a decidable source (since it is the same source). -/
instance preimageVertexDecidable {𝓔 𝓥 : Type} (v : 𝓥)
    (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥)) [DecidableEq F.left] :
    DecidableEq ((P.preimageVertex v).obj F).left := Subtype.instDecidableEq

/-- The half edges corresponding to a given edge has an indexing set which is decidable. -/
instance preimageEdgeDecidable {𝓔 𝓥 : Type} (v : 𝓔)
    (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥)) [DecidableEq F.left] :
    DecidableEq ((P.preimageEdge v).obj F).left := Subtype.instDecidableEq

/-- The half edges corresponding to a given vertex has an indexing set which is decidable. -/
instance preimageVertexFintype {𝓔 𝓥 : Type} [DecidableEq 𝓥]
    (v : 𝓥) (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥)) [h : Fintype F.left] :
    Fintype ((P.preimageVertex v).obj F).left := @Subtype.fintype _ _ _ h

/-- The half edges corresponding to a given edge has an indexing set which is finite. -/
instance preimageEdgeFintype {𝓔 𝓥 : Type} [DecidableEq 𝓔]
    (v : 𝓔) (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥)) [h : Fintype F.left] :
    Fintype ((P.preimageEdge v).obj F).left := @Subtype.fintype _ _ _ h

/-- The half edges corresponding to a given vertex has an indexing set which is finite. -/
instance preimageVertexMapFintype [IsFinitePreFeynmanRule P] {𝓔 𝓥 : Type}
    [DecidableEq 𝓥] (v : 𝓥) (f : 𝓥 ⟶ P.VertexLabel) (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥))
    [Fintype F.left] :
    Fintype ((P.vertexLabelMap (f v)).left → ((P.preimageVertex v).obj F).left) :=
  Pi.fintype

/-- Given an edge, there is a finite number of maps between the indexing set of the
  expected half-edges corresponding to that edges label, and the actual indexing
  set of half-edges corresponding to that edge. Given various finiteness conditions. -/
instance preimageEdgeMapFintype [IsFinitePreFeynmanRule P] {𝓔 𝓥 : Type}
    [DecidableEq 𝓔] (v : 𝓔) (f : 𝓔 ⟶ P.EdgeLabel) (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥))
    [Fintype F.left] :
    Fintype ((P.edgeLabelMap (f v)).left → ((P.preimageEdge v).obj F).left) :=
  Pi.fintype

/-!

## External and internal Vertices

We say a vertex Label is `external` if it has only one half-edge associated with it.
Otherwise, we say it is `internal`.

We will show that for `IsFinitePreFeynmanRule` the condition of been external is decidable.
-/

/-- A vertex is external if it has a single half-edge associated to it. -/
def External {P : PreFeynmanRule} (v : P.VertexLabel) : Prop :=
  IsIsomorphic (P.vertexLabelMap v).left (Fin 1)

lemma external_iff_exists_bijection {P : PreFeynmanRule} (v : P.VertexLabel) :
    External v ↔ ∃ (κ : (P.vertexLabelMap v).left → Fin 1), Function.Bijective κ := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨κ, κm1, h1, h2⟩ := h
    let f : (P.vertexLabelMap v).left ≅ (Fin 1) := ⟨κ, κm1, h1, h2⟩
    exact ⟨f.hom, (isIso_iff_bijective f.hom).mp $ Iso.isIso_hom f⟩
  · obtain ⟨κ, h1⟩ := h
    let f : (P.vertexLabelMap v).left ⟶ (Fin 1) := κ
    have ft : IsIso f := (isIso_iff_bijective κ).mpr h1
    obtain ⟨fm, hf1, hf2⟩ := ft
    exact ⟨f, fm, hf1, hf2⟩

/-- Whether or not a vertex is external is decidable. -/
instance externalDecidable [IsFinitePreFeynmanRule P] (v : P.VertexLabel) :
    Decidable (External v) :=
  decidable_of_decidable_of_iff (external_iff_exists_bijection v).symm

/-!

## Conditions to form a diagram.

-/

/-- The proposition on vertices which must be satisfied by an object
  `F : Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)` for it to be a Feynman diagram.
  This condition corresponds to the vertices of `F` having the correct half-edges associated
  with them. -/
def DiagramVertexProp {𝓔 𝓥 : Type} (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥))
    (f : 𝓥 ⟶ P.VertexLabel) :=
  ∀ v, IsIsomorphic (P.vertexLabelMap (f v)) ((P.preimageVertex v).obj F)

/-- The proposition on edges which must be satisfied by an object
  `F : Over (P.HalfEdgeLabel × P.EdgeLabel × P.VertexLabel)` for it to be a Feynman diagram.
  This condition corresponds to the edges of `F` having the correct half-edges associated
  with them. -/
def DiagramEdgeProp {𝓔 𝓥 : Type} (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥))
    (f : 𝓔 ⟶ P.EdgeLabel) :=
  ∀ v, IsIsomorphic (P.edgeLabelMap (f v)) ((P.preimageEdge v).obj F)

lemma diagramVertexProp_iff {𝓔 𝓥 : Type} (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥))
    (f : 𝓥 ⟶ P.VertexLabel) : P.DiagramVertexProp F f ↔
    ∀ v, ∃ (κ : (P.vertexLabelMap (f v)).left → ((P.preimageVertex v).obj F).left),
    Function.Bijective κ
    ∧ ((P.preimageVertex v).obj F).hom ∘ κ = (P.vertexLabelMap (f v)).hom := by
  refine Iff.intro (fun h v => ?_) (fun h v => ?_)
  · obtain ⟨κ, κm1, h1, h2⟩ := h v
    let f := (Over.forget P.HalfEdgeLabel).mapIso ⟨κ, κm1, h1, h2⟩
    exact ⟨f.hom, (isIso_iff_bijective f.hom).mp $ Iso.isIso_hom f, κ.w⟩
  · obtain ⟨κ, h1, h2⟩ := h v
    let f : (P.vertexLabelMap (f v)) ⟶ ((P.preimageVertex v).obj F) := Over.homMk κ h2
    have ft : IsIso ((Over.forget P.HalfEdgeLabel).map f) := (isIso_iff_bijective κ).mpr h1
    obtain ⟨fm, hf1, hf2⟩ := (isIso_of_reflects_iso _ (Over.forget P.HalfEdgeLabel) : IsIso f)
    exact ⟨f, fm, hf1, hf2⟩

lemma diagramEdgeProp_iff {𝓔 𝓥 : Type} (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥))
    (f : 𝓔 ⟶ P.EdgeLabel) : P.DiagramEdgeProp F f ↔
    ∀ v, ∃ (κ : (P.edgeLabelMap (f v)).left → ((P.preimageEdge v).obj F).left),
    Function.Bijective κ
    ∧ ((P.preimageEdge v).obj F).hom ∘ κ = (P.edgeLabelMap (f v)).hom := by
  refine Iff.intro (fun h v => ?_) (fun h v => ?_)
  · obtain ⟨κ, κm1, h1, h2⟩ := h v
    let f := (Over.forget P.HalfEdgeLabel).mapIso ⟨κ, κm1, h1, h2⟩
    exact ⟨f.hom, (isIso_iff_bijective f.hom).mp $ Iso.isIso_hom f, κ.w⟩
  · obtain ⟨κ, h1, h2⟩ := h v
    let f : (P.edgeLabelMap (f v)) ⟶ ((P.preimageEdge v).obj F) := Over.homMk κ h2
    have ft : IsIso ((Over.forget P.HalfEdgeLabel).map f) := (isIso_iff_bijective κ).mpr h1
    obtain ⟨fm, hf1, hf2⟩ := (isIso_of_reflects_iso _ (Over.forget P.HalfEdgeLabel) : IsIso f)
    exact ⟨f, fm, hf1, hf2⟩

/-- The proposition `DiagramVertexProp` is decidable given various decidability and finite
  conditions. -/
instance diagramVertexPropDecidable
    [IsFinitePreFeynmanRule P] {𝓔 𝓥 : Type} [Fintype 𝓥] [DecidableEq 𝓥]
    (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥)) [DecidableEq F.left] [Fintype F.left]
    (f : 𝓥 ⟶ P.VertexLabel) : Decidable (P.DiagramVertexProp F f) :=
  @decidable_of_decidable_of_iff _ _
    (@Fintype.decidableForallFintype _ _ (fun _ => @Fintype.decidableExistsFintype _ _
    (fun _ => @instDecidableAnd _ _ _ (@Fintype.decidablePiFintype _ _
    (fun _ => P.preFeynmanRuleDecEq𝓱𝓔) _ _ _)) _) _)
    (P.diagramVertexProp_iff F f).symm

/-- The proposition `DiagramEdgeProp` is decidable given various decidability and finite
  conditions. -/
instance diagramEdgePropDecidable
    [IsFinitePreFeynmanRule P] {𝓔 𝓥 : Type} [Fintype 𝓔] [DecidableEq 𝓔]
    (F : Over (P.HalfEdgeLabel × 𝓔 × 𝓥)) [DecidableEq F.left] [Fintype F.left]
    (f : 𝓔 ⟶ P.EdgeLabel) : Decidable (P.DiagramEdgeProp F f) :=
  @decidable_of_decidable_of_iff _ _
    (@Fintype.decidableForallFintype _ _ (fun _ => @Fintype.decidableExistsFintype _ _
    (fun _ => @instDecidableAnd _ _ _ (@Fintype.decidablePiFintype _ _
    (fun _ => P.preFeynmanRuleDecEq𝓱𝓔) _ _ _)) _) _)
    (P.diagramEdgeProp_iff F f).symm

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
  𝓔Cond : P.DiagramEdgeProp 𝓱𝓔To𝓔𝓥 𝓔𝓞.hom
  /-- Each vertex has the correct sort of half edges. -/
  𝓥Cond : P.DiagramVertexProp 𝓱𝓔To𝓔𝓥 𝓥𝓞.hom

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

/-- The map `F.𝓱𝓔 → F.𝓔` as an object in `Over F.𝓔 `. -/
def 𝓱𝓔To𝓔 : Over F.𝓔 := P.toEdge.obj F.𝓱𝓔To𝓔𝓥

/-- The map `F.𝓱𝓔 → F.𝓥` as an object in `Over F.𝓥 `. -/
def 𝓱𝓔To𝓥 : Over F.𝓥 := P.toVertex.obj F.𝓱𝓔To𝓔𝓥

/-!

## Making a Feynman diagram

-/

/-- The condition which must be satisfied by maps to form a Feynman diagram. -/
def Cond {𝓔 𝓥 𝓱𝓔 : Type} (𝓔𝓞 : 𝓔 → P.EdgeLabel) (𝓥𝓞 : 𝓥 → P.VertexLabel)
    (𝓱𝓔To𝓔𝓥 : 𝓱𝓔 → P.HalfEdgeLabel × 𝓔 × 𝓥) : Prop :=
  P.DiagramEdgeProp (Over.mk 𝓱𝓔To𝓔𝓥) 𝓔𝓞 ∧
  P.DiagramVertexProp (Over.mk 𝓱𝓔To𝓔𝓥) 𝓥𝓞

lemma cond_self : Cond F.𝓔𝓞.hom F.𝓥𝓞.hom F.𝓱𝓔To𝓔𝓥.hom :=
  ⟨F.𝓔Cond, F.𝓥Cond⟩

/-- `Cond` is decidable. -/
instance CondDecidable [IsFinitePreFeynmanRule P] {𝓔 𝓥 𝓱𝓔 : Type} (𝓔𝓞 : 𝓔 → P.EdgeLabel)
    (𝓥𝓞 : 𝓥 → P.VertexLabel)
    (𝓱𝓔To𝓔𝓥 : 𝓱𝓔 → P.HalfEdgeLabel × 𝓔 × 𝓥)
    [Fintype 𝓥] [DecidableEq 𝓥] [Fintype 𝓔] [DecidableEq 𝓔] [h : Fintype 𝓱𝓔] [DecidableEq 𝓱𝓔] :
    Decidable (Cond 𝓔𝓞 𝓥𝓞 𝓱𝓔To𝓔𝓥) :=
  @instDecidableAnd _ _
    (@diagramEdgePropDecidable P _ _ _ _ _ (Over.mk 𝓱𝓔To𝓔𝓥) _ h 𝓔𝓞)
    (@diagramVertexPropDecidable P _ _ _ _ _ (Over.mk 𝓱𝓔To𝓔𝓥) _ h 𝓥𝓞)

/-- Making a Feynman diagram from maps of edges, vertices and half-edges. -/
def mk' {𝓔 𝓥 𝓱𝓔 : Type} (𝓔𝓞 : 𝓔 → P.EdgeLabel) (𝓥𝓞 : 𝓥 → P.VertexLabel)
    (𝓱𝓔To𝓔𝓥 : 𝓱𝓔 → P.HalfEdgeLabel × 𝓔 × 𝓥)
    (C : Cond 𝓔𝓞 𝓥𝓞 𝓱𝓔To𝓔𝓥) : FeynmanDiagram P where
  𝓔𝓞 := Over.mk 𝓔𝓞
  𝓥𝓞 := Over.mk 𝓥𝓞
  𝓱𝓔To𝓔𝓥 := Over.mk 𝓱𝓔To𝓔𝓥
  𝓔Cond := C.1
  𝓥Cond := C.2

lemma mk'_self : mk' F.𝓔𝓞.hom F.𝓥𝓞.hom F.𝓱𝓔To𝓔𝓥.hom F.cond_self = F := rfl

/-!

## Finiteness of Feynman diagrams

As defined above our Feynman diagrams can have non-finite Types of half-edges etc.
We define the class of those Feynman diagrams which are `finite` in the appropriate sense.
In practice, every Feynman diagram considered in the physics literature is `finite`.

This finiteness condition will be used to prove certain `Types` are `Fintype`, and prove
that certain propositions are decidable.

-/

/-- A set of conditions on a Feynman diagram for it to be considered finite. -/
class IsFiniteDiagram (F : FeynmanDiagram P) where
  /-- The type of edges is finite. -/
  𝓔Fintype : Fintype F.𝓔
  /-- The type of edges is decidable. -/
  𝓔DecidableEq : DecidableEq F.𝓔
  /-- The type of vertices is finite. -/
  𝓥Fintype : Fintype F.𝓥
  /-- The type of vertices is decidable. -/
  𝓥DecidableEq : DecidableEq F.𝓥
  /-- The type of half-edges is finite. -/
  𝓱𝓔Fintype : Fintype F.𝓱𝓔
  /-- The type of half-edges is decidable. -/
  𝓱𝓔DecidableEq : DecidableEq F.𝓱𝓔

/-- The instance of a finite diagram given explicit finiteness and decidable conditions
  on the various maps making it up. -/
instance {𝓔 𝓥 𝓱𝓔 : Type} [h1 : Fintype 𝓔] [h2 : DecidableEq 𝓔]
    [h3 : Fintype 𝓥] [h4 : DecidableEq 𝓥] [h5 : Fintype 𝓱𝓔] [h6 : DecidableEq 𝓱𝓔]
    (𝓔𝓞 : 𝓔 → P.EdgeLabel) (𝓥𝓞 : 𝓥 → P.VertexLabel)
    (𝓱𝓔To𝓔𝓥 : 𝓱𝓔 → P.HalfEdgeLabel × 𝓔 × 𝓥) (C : Cond 𝓔𝓞 𝓥𝓞 𝓱𝓔To𝓔𝓥) :
    IsFiniteDiagram (mk' 𝓔𝓞 𝓥𝓞 𝓱𝓔To𝓔𝓥 C) :=
  ⟨h1, h2, h3, h4, h5, h6⟩

/-- If `F` is a finite Feynman diagram, then its edges are finite. -/
instance {F : FeynmanDiagram P} [IsFiniteDiagram F] : Fintype F.𝓔 :=
  IsFiniteDiagram.𝓔Fintype

/-- If `F` is a finite Feynman diagram, then its edges are decidable. -/
instance {F : FeynmanDiagram P} [IsFiniteDiagram F] : DecidableEq F.𝓔 :=
  IsFiniteDiagram.𝓔DecidableEq

/-- If `F` is a finite Feynman diagram, then its vertices are finite. -/
instance {F : FeynmanDiagram P} [IsFiniteDiagram F] : Fintype F.𝓥 :=
  IsFiniteDiagram.𝓥Fintype

/-- If `F` is a finite Feynman diagram, then its vertices are decidable. -/
instance {F : FeynmanDiagram P} [IsFiniteDiagram F] : DecidableEq F.𝓥 :=
  IsFiniteDiagram.𝓥DecidableEq

/-- If `F` is a finite Feynman diagram, then its half-edges are finite. -/
instance {F : FeynmanDiagram P} [IsFiniteDiagram F] : Fintype F.𝓱𝓔 :=
  IsFiniteDiagram.𝓱𝓔Fintype

/-- If `F` is a finite Feynman diagram, then its half-edges are decidable. -/
instance {F : FeynmanDiagram P} [IsFiniteDiagram F] : DecidableEq F.𝓱𝓔 :=
  IsFiniteDiagram.𝓱𝓔DecidableEq

/-- The proposition of whether the given an half-edge and an edge,
  the edge corresponding to the half edges is the given edge is decidable. -/
instance {F : FeynmanDiagram P} [IsFiniteDiagram F] (i : F.𝓱𝓔) (j : F.𝓔) :
    Decidable (F.𝓱𝓔To𝓔.hom i = j) := IsFiniteDiagram.𝓔DecidableEq (F.𝓱𝓔To𝓔.hom i) j

/-- For a finite feynman diagram, the type of half edge labels, edges and vertices
  is decidable. -/
instance fintypeProdHalfEdgeLabel𝓔𝓥 {F : FeynmanDiagram P} [IsFinitePreFeynmanRule P]
    [IsFiniteDiagram F] : DecidableEq (P.HalfEdgeLabel × F.𝓔 × F.𝓥) :=
  instDecidableEqProd

/-!

## Morphisms of Feynman diagrams

We define a morphism between Feynman diagrams, and properties thereof.
This will be used to define the category of Feynman diagrams.

-/

/-- Given two maps `F.𝓔 ⟶ G.𝓔` and `F.𝓥 ⟶ G.𝓥` the corresponding map
  `P.HalfEdgeLabel × F.𝓔 × F.𝓥 → P.HalfEdgeLabel × G.𝓔 × G.𝓥`. -/
@[simps!]
def edgeVertexMap {F G : FeynmanDiagram P} (𝓔 : F.𝓔 ⟶ G.𝓔) (𝓥 : F.𝓥 ⟶ G.𝓥) :
    P.HalfEdgeLabel × F.𝓔 × F.𝓥 → P.HalfEdgeLabel × G.𝓔 × G.𝓥 :=
  fun x => ⟨x.1, 𝓔 x.2.1, 𝓥 x.2.2⟩

/-- Given equivalences `F.𝓔 ≃ G.𝓔` and `F.𝓥 ≃ G.𝓥`, the induced equivalence between
  `P.HalfEdgeLabel × F.𝓔 × F.𝓥` and `P.HalfEdgeLabel × G.𝓔 × G.𝓥 ` -/
def edgeVertexEquiv {F G : FeynmanDiagram P} (𝓔 : F.𝓔 ≃ G.𝓔) (𝓥 : F.𝓥 ≃ G.𝓥) :
    P.HalfEdgeLabel × F.𝓔 × F.𝓥 ≃ P.HalfEdgeLabel × G.𝓔 × G.𝓥 where
  toFun := edgeVertexMap 𝓔.toFun 𝓥.toFun
  invFun := edgeVertexMap 𝓔.invFun 𝓥.invFun
  left_inv := by aesop_cat
  right_inv := by aesop_cat

/-- The functor of over-categories generated by `edgeVertexMap`. -/
@[simps! obj_left obj_hom map_left map_right]
def edgeVertexFunc {F G : FeynmanDiagram P} (𝓔 : F.𝓔 ⟶ G.𝓔) (𝓥 : F.𝓥 ⟶ G.𝓥) :
    Over (P.HalfEdgeLabel × F.𝓔 × F.𝓥) ⥤ Over (P.HalfEdgeLabel × G.𝓔 × G.𝓥) :=
  Over.map <| edgeVertexMap 𝓔 𝓥

/-- A morphism of Feynman diagrams. -/
structure Hom (F G : FeynmanDiagram P) where
  /-- The morphism of edge objects. -/
  𝓔𝓞 : F.𝓔𝓞 ⟶ G.𝓔𝓞
  /-- The morphism of vertex objects. -/
  𝓥𝓞 : F.𝓥𝓞 ⟶ G.𝓥𝓞
  /-- The morphism of half-edge objects. -/
  𝓱𝓔To𝓔𝓥 : (edgeVertexFunc 𝓔𝓞.left 𝓥𝓞.left).obj F.𝓱𝓔To𝓔𝓥 ⟶ G.𝓱𝓔To𝓔𝓥

namespace Hom
variable {F G : FeynmanDiagram P}
variable (f : Hom F G)

/-- The map `F.𝓔 → G.𝓔` induced by a homomorphism of Feynman diagrams. -/
@[simp]
def 𝓔 : F.𝓔 → G.𝓔 := f.𝓔𝓞.left

/-- The map `F.𝓥 → G.𝓥` induced by a homomorphism of Feynman diagrams. -/
@[simp]
def 𝓥 : F.𝓥 → G.𝓥 := f.𝓥𝓞.left

/-- The map `F.𝓱𝓔 → G.𝓱𝓔` induced by a homomorphism of Feynman diagrams. -/
@[simp]
def 𝓱𝓔 : F.𝓱𝓔 → G.𝓱𝓔 := f.𝓱𝓔To𝓔𝓥.left

/-- The morphism `F.𝓱𝓔𝓞 ⟶ G.𝓱𝓔𝓞` induced by a homomorphism of Feynman diagrams. -/
@[simp]
def 𝓱𝓔𝓞 : F.𝓱𝓔𝓞 ⟶ G.𝓱𝓔𝓞 := P.toHalfEdge.map f.𝓱𝓔To𝓔𝓥

/-- The identity morphism for a Feynman diagram. -/
def id (F : FeynmanDiagram P) : Hom F F where
  𝓔𝓞 := 𝟙 F.𝓔𝓞
  𝓥𝓞 := 𝟙 F.𝓥𝓞
  𝓱𝓔To𝓔𝓥 := 𝟙 F.𝓱𝓔To𝓔𝓥

/-- The composition of two morphisms of Feynman diagrams. -/
@[simps! 𝓔𝓞_left 𝓥𝓞_left 𝓱𝓔To𝓔𝓥_left]
def comp {F G H : FeynmanDiagram P} (f : Hom F G) (g : Hom G H) : Hom F H where
  𝓔𝓞 := f.𝓔𝓞 ≫ g.𝓔𝓞
  𝓥𝓞 := f.𝓥𝓞 ≫ g.𝓥𝓞
  𝓱𝓔To𝓔𝓥 := (edgeVertexFunc g.𝓔 g.𝓥).map f.𝓱𝓔To𝓔𝓥 ≫ g.𝓱𝓔To𝓔𝓥

lemma ext' {F G : FeynmanDiagram P} {f g : Hom F G} (h𝓔 : f.𝓔𝓞 = g.𝓔𝓞)
    (h𝓥 : f.𝓥𝓞 = g.𝓥𝓞) (h𝓱𝓔 : f.𝓱𝓔 = g.𝓱𝓔) : f = g := by
  cases f
  cases g
  subst h𝓔 h𝓥
  simp_all only [mk.injEq, heq_eq_eq, true_and]
  ext a : 2
  simp only [𝓱𝓔] at h𝓱𝓔
  exact congrFun h𝓱𝓔 a

lemma ext {F G : FeynmanDiagram P} {f g : Hom F G} (h𝓔 : f.𝓔 = g.𝓔)
    (h𝓥 : f.𝓥 = g.𝓥) (h𝓱𝓔 : f.𝓱𝓔 = g.𝓱𝓔) : f = g :=
  ext' (Over.OverMorphism.ext h𝓔) (Over.OverMorphism.ext h𝓥) h𝓱𝓔

/-- The condition on maps of edges, vertices and half-edges for it to be lifted to a
  morphism of Feynman diagrams. -/
def Cond {F G : FeynmanDiagram P} (𝓔 : F.𝓔 → G.𝓔) (𝓥 : F.𝓥 → G.𝓥) (𝓱𝓔 : F.𝓱𝓔 → G.𝓱𝓔) : Prop :=
  (∀ x, G.𝓔𝓞.hom (𝓔 x) = F.𝓔𝓞.hom x) ∧
  (∀ x, G.𝓥𝓞.hom (𝓥 x) = F.𝓥𝓞.hom x) ∧
  (∀ x, G.𝓱𝓔To𝓔𝓥.hom (𝓱𝓔 x) = edgeVertexMap 𝓔 𝓥 (F.𝓱𝓔To𝓔𝓥.hom x))

lemma cond_satisfied {F G : FeynmanDiagram P} (f : Hom F G) :
    Cond f.𝓔 f.𝓥 f.𝓱𝓔 :=
  ⟨fun x => congrFun f.𝓔𝓞.w x, fun x => congrFun f.𝓥𝓞.w x, fun x => congrFun f.𝓱𝓔To𝓔𝓥.w x⟩

lemma cond_symm {F G : FeynmanDiagram P} (𝓔 : F.𝓔 ≃ G.𝓔) (𝓥 : F.𝓥 ≃ G.𝓥) (𝓱𝓔 : F.𝓱𝓔 ≃ G.𝓱𝓔)
    (h : Cond 𝓔 𝓥 𝓱𝓔) : Cond 𝓔.symm 𝓥.symm 𝓱𝓔.symm := by
  refine ⟨?_, ?_, fun x => ?_⟩
  · simpa using fun x => (h.1 (𝓔.symm x)).symm
  · simpa using fun x => (h.2.1 (𝓥.symm x)).symm
  · have h1 := h.2.2 (𝓱𝓔.symm x)
    simp only [Functor.const_obj_obj, Equiv.apply_symm_apply] at h1
    exact (edgeVertexEquiv 𝓔 𝓥).apply_eq_iff_eq_symm_apply.mp (h1).symm

/-- If `𝓔` is a map between the edges of one finite Feynman diagram and another Feynman diagram,
  then deciding whether `𝓔` from a morphism in `Over P.EdgeLabel` between the edge
  maps is decidable. -/
instance {F G : FeynmanDiagram P} [IsFiniteDiagram F] [IsFinitePreFeynmanRule P]
    (𝓔 : F.𝓔 → G.𝓔) : Decidable (∀ x, G.𝓔𝓞.hom (𝓔 x) = F.𝓔𝓞.hom x) :=
  @Fintype.decidableForallFintype _ _ (fun _ => preFeynmanRuleDecEq𝓔 P _ _) _

/-- If `𝓥` is a map between the vertices of one finite Feynman diagram and another Feynman diagram,
  then deciding whether `𝓥` from a morphism in `Over P.VertexLabel` between the vertex
  maps is decidable. -/
instance {F G : FeynmanDiagram P} [IsFiniteDiagram F] [IsFinitePreFeynmanRule P]
    (𝓥 : F.𝓥 → G.𝓥) : Decidable (∀ x, G.𝓥𝓞.hom (𝓥 x) = F.𝓥𝓞.hom x) :=
  @Fintype.decidableForallFintype _ _ (fun _ => preFeynmanRuleDecEq𝓥 P _ _) _

/-- Given maps between parts of two Feynman diagrams, it is decidable to determine
  whether on mapping half-edges, the corresponding half-edge labels, edges and vertices
  are consistent. -/
instance {F G : FeynmanDiagram P} [IsFiniteDiagram F] [IsFiniteDiagram G] [IsFinitePreFeynmanRule P]
    (𝓔 : F.𝓔 → G.𝓔) (𝓥 : F.𝓥 → G.𝓥) (𝓱𝓔 : F.𝓱𝓔 → G.𝓱𝓔) :
    Decidable (∀ x, G.𝓱𝓔To𝓔𝓥.hom (𝓱𝓔 x) = edgeVertexMap 𝓔 𝓥 (F.𝓱𝓔To𝓔𝓥.hom x)) :=
  @Fintype.decidableForallFintype _ _ (fun _ => fintypeProdHalfEdgeLabel𝓔𝓥 _ _) _

/-- The condition on whether a map of maps of edges, vertices and half-edges can be
    lifted to a morphism of Feynman diagrams is decidable. -/
instance {F G : FeynmanDiagram P} [IsFiniteDiagram F] [IsFiniteDiagram G] [IsFinitePreFeynmanRule P]
    (𝓔 : F.𝓔 → G.𝓔) (𝓥 : F.𝓥 → G.𝓥) (𝓱𝓔 : F.𝓱𝓔 → G.𝓱𝓔) : Decidable (Cond 𝓔 𝓥 𝓱𝓔) :=
  instDecidableAnd

/-- Making a Feynman diagram from maps of edges, vertices and half-edges. -/
@[simps! 𝓔𝓞_left 𝓥𝓞_left 𝓱𝓔To𝓔𝓥_left]
def mk' {F G : FeynmanDiagram P} (𝓔 : F.𝓔 → G.𝓔) (𝓥 : F.𝓥 → G.𝓥) (𝓱𝓔 : F.𝓱𝓔 → G.𝓱𝓔)
    (C : Cond 𝓔 𝓥 𝓱𝓔) : Hom F G where
  𝓔𝓞 := Over.homMk 𝓔 $ funext C.1
  𝓥𝓞 := Over.homMk 𝓥 $ funext C.2.1
  𝓱𝓔To𝓔𝓥 := Over.homMk 𝓱𝓔 $ funext C.2.2

lemma mk'_self {F G : FeynmanDiagram P} (f : Hom F G) :
    mk' f.𝓔 f.𝓥 f.𝓱𝓔 f.cond_satisfied = f := rfl

end Hom

/-!

## The Category of Feynman diagrams

Feynman diagrams, as defined above, form a category.
We will be able to use this category to define the symmetry factor of a Feynman diagram,
and the condition on whether a diagram is connected.
-/

/-- Feynman diagrams form a category. -/
@[simps! id_𝓔𝓞_left id_𝓥𝓞_left id_𝓱𝓔To𝓔𝓥_left comp_𝓔𝓞_left comp_𝓥𝓞_left comp_𝓱𝓔To𝓔𝓥_left]
instance : Category (FeynmanDiagram P) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

/-- An isomorphism of Feynman diagrams from isomorphisms of edges, vertices and half-edges. -/
def mkIso {F G : FeynmanDiagram P} (𝓔 : F.𝓔 ≃ G.𝓔) (𝓥 : F.𝓥 ≃ G.𝓥) (𝓱𝓔 : F.𝓱𝓔 ≃ G.𝓱𝓔)
    (C : Hom.Cond 𝓔 𝓥 𝓱𝓔) : F ≅ G where
  hom := Hom.mk' 𝓔 𝓥 𝓱𝓔 C
  inv := Hom.mk' 𝓔.symm 𝓥.symm 𝓱𝓔.symm (Hom.cond_symm 𝓔 𝓥 𝓱𝓔 C)
  hom_inv_id := by
    apply Hom.ext
    all_goals
      aesop_cat
  inv_hom_id := by
    apply Hom.ext
    all_goals
      aesop_cat

/-- The functor from Feynman diagrams to category over edge labels. -/
def func𝓔𝓞 : FeynmanDiagram P ⥤ Over P.EdgeLabel where
  obj F := F.𝓔𝓞
  map f := f.𝓔𝓞

/-- The functor from Feynman diagrams to category over vertex labels. -/
def func𝓥𝓞 : FeynmanDiagram P ⥤ Over P.VertexLabel where
  obj F := F.𝓥𝓞
  map f := f.𝓥𝓞

/-- The functor from Feynman diagrams to category over half-edge labels. -/
def func𝓱𝓔𝓞 : FeynmanDiagram P ⥤ Over P.HalfEdgeLabel where
  obj F := F.𝓱𝓔𝓞
  map f := f.𝓱𝓔𝓞

/-- The functor from Feynman diagrams to `Type` landing on edges. -/
def func𝓔 : FeynmanDiagram P ⥤ Type where
  obj F := F.𝓔
  map f := f.𝓔

/-- The functor from Feynman diagrams to `Type` landing on vertices. -/
def func𝓥 : FeynmanDiagram P ⥤ Type where
  obj F := F.𝓥
  map f := f.𝓥

/-- The functor from Feynman diagrams to `Type` landing on half-edges. -/
def func𝓱𝓔 : FeynmanDiagram P ⥤ Type where
  obj F := F.𝓱𝓔
  map f := f.𝓱𝓔

section symmetryFactor
/-!
## Symmetry factors

The symmetry factor of a Feynman diagram is the cardinality of the group of automorphisms of that
diagram.

We show that the symmetry factor for a finite Feynman diagram is finite.

-/

/-- The type of isomorphisms of a Feynman diagram. -/
def SymmetryType : Type := F ≅ F

/-- An equivalence between `SymmetryType` and permutation of edges, vertices and half-edges
  satisfying `Hom.Cond`. -/
def symmetryTypeEquiv :
    F.SymmetryType ≃ {S : Equiv.Perm F.𝓔 × Equiv.Perm F.𝓥 × Equiv.Perm F.𝓱𝓔 //
      Hom.Cond S.1 S.2.1 S.2.2} where
  toFun f := ⟨⟨(func𝓔.mapIso f).toEquiv, (func𝓥.mapIso f).toEquiv,
    (func𝓱𝓔.mapIso f).toEquiv⟩, f.1.cond_satisfied⟩
  invFun S := mkIso S.1.1 S.1.2.1 S.1.2.2 S.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- For a finite Feynman diagram, the type of automorphisms of that Feynman diagram is finite. -/
instance [IsFinitePreFeynmanRule P] [IsFiniteDiagram F] : Fintype F.SymmetryType :=
  Fintype.ofEquiv _ F.symmetryTypeEquiv.symm

/-- The symmetry factor can be defined as the cardinal of the symmetry type.
  In general this is not a finite number. -/
@[simp]
def cardSymmetryFactor : Cardinal := Cardinal.mk (F.SymmetryType)

/-- The symmetry factor of a Finite Feynman diagram, as a natural number. -/
@[simp]
def symmetryFactor [IsFinitePreFeynmanRule P] [IsFiniteDiagram F] : ℕ :=
  (Fintype.card F.SymmetryType)

@[simp]
lemma symmetryFactor_eq_cardSymmetryFactor [IsFinitePreFeynmanRule P] [IsFiniteDiagram F] :
    F.symmetryFactor = F.cardSymmetryFactor := by
  simp only [symmetryFactor, cardSymmetryFactor, Cardinal.mk_fintype]

end symmetryFactor

section connectedness
/-!

## Connectedness

Given a Feynman diagram we can create a simple graph based on the obvious adjacency relation.
A feynman diagram is connected if its simple graph is connected.

## TODO

- Complete this section.

-/

/-- A relation on the vertices of Feynman diagrams. The proposition is true if the two
  vertices are not equal and are connected by a single edge.
  This is the adjacency relation. -/
@[simp]
def AdjRelation : F.𝓥 → F.𝓥 → Prop := fun x y =>
  x ≠ y ∧
  ∃ (a b : F.𝓱𝓔), ((F.𝓱𝓔To𝓔𝓥.hom a).2.1 = (F.𝓱𝓔To𝓔𝓥.hom b).2.1
  ∧ (F.𝓱𝓔To𝓔𝓥.hom a).2.2 = x ∧ (F.𝓱𝓔To𝓔𝓥.hom b).2.2 = y)

/-- The condition on whether two vertices are adjacent is decidable. -/
instance [IsFiniteDiagram F] : DecidableRel F.AdjRelation := fun _ _ =>
  @instDecidableAnd _ _ _ $
  @Fintype.decidableExistsFintype _ _ (fun _ => @Fintype.decidableExistsFintype _ _
  (fun _ => @instDecidableAnd _ _ (instDecidableEq𝓔OfIsFiniteDiagram _ _) $
    @instDecidableAnd _ _ (instDecidableEq𝓥OfIsFiniteDiagram _ _)
    (instDecidableEq𝓥OfIsFiniteDiagram _ _)) _) _

/-- From a Feynman diagram the simple graph showing those vertices which are connected. -/
def toSimpleGraph : SimpleGraph F.𝓥 where
  Adj := AdjRelation F
  symm := by
    intro x y h
    apply And.intro (Ne.symm h.1)
    obtain ⟨a, b, hab⟩ := h.2
    use b, a
    simp_all only [AdjRelation, ne_eq, and_self]
  loopless := by
    intro x h
    simp at h

/-- The adjacency relation for a simple graph created by a finite Feynman diagram
  is a decidable relation. -/
instance [IsFiniteDiagram F] : DecidableRel F.toSimpleGraph.Adj :=
  instDecidableRel𝓥AdjRelationOfIsFiniteDiagram F

/-- For a finite feynman diagram it is decidable whether it is preconnected and has
  the Feynman diagram has a non-empty type of vertices. -/
instance [IsFiniteDiagram F] :
  Decidable (F.toSimpleGraph.Preconnected ∧ Nonempty F.𝓥) :=
  @instDecidableAnd _ _ _ $ decidable_of_iff _ Finset.univ_nonempty_iff

/-- For a finite Feynman diagram it is decidable whether the simple graph corresponding to it
  is connected. -/
instance [IsFiniteDiagram F] : Decidable F.toSimpleGraph.Connected :=
  decidable_of_iff _ (SimpleGraph.connected_iff F.toSimpleGraph).symm

/-- A Feynman diagram is connected if its simple graph is connected. -/
def Connected : Prop := F.toSimpleGraph.Connected

/-- For a finite Feynman diagram it is decidable whether or not it is connected. -/
instance [IsFiniteDiagram F] : Decidable (Connected F) :=
  instDecidableConnected𝓥ToSimpleGraphOfIsFiniteDiagram F

end connectedness

end FeynmanDiagram
