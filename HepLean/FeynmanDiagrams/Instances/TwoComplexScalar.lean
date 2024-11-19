/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Basic
/-!

# Feynman rules for a two complex scalar fields

This file serves as a demonstration of a new approach to Feynman rules.

-/

namespace TwoComplexScalar
open CategoryTheory
open FeynmanDiagram
open PreFeynmanRule

/-- The colors of edges which one can associate with a vertex for a theory
  with two complex scalar fields. -/
inductive 𝓔 where
  /-- Corresponds to the first complex scalar field flowing out of a vertex. -/
  | complexScalarOut₁ : 𝓔
  /-- Corresponds to the first complex scalar field flowing into a vertex. -/
  | complexScalarIn₁ : 𝓔
  /-- Corresponds to the second complex scalar field flowing out of a vertex. -/
  | complexScalarOut₂ : 𝓔
  /-- Corresponds to the second complex scalar field flowing into a vertex. -/
  | complexScalarIn₂ : 𝓔

/-- The map taking each color to it's dual, specifying how we can contract edges. -/
def ξ : 𝓔 → 𝓔
  | 𝓔.complexScalarOut₁ => 𝓔.complexScalarIn₁
  | 𝓔.complexScalarIn₁ => 𝓔.complexScalarOut₁
  | 𝓔.complexScalarOut₂ => 𝓔.complexScalarIn₂
  | 𝓔.complexScalarIn₂ => 𝓔.complexScalarOut₂

/-- The function `ξ` is an involution. -/
lemma ξ_involutive : Function.Involutive ξ := by
  intro x
  match x with
  | 𝓔.complexScalarOut₁ => rfl
  | 𝓔.complexScalarIn₁ => rfl
  | 𝓔.complexScalarOut₂ => rfl
  | 𝓔.complexScalarIn₂ => rfl

/-- The vertices associated with two complex scalars.
  We call this type, the type of vertex colors. -/
inductive 𝓥 where
  | φ₁φ₁φ₂φ₂ : 𝓥
  | φ₁φ₁φ₁φ₁ : 𝓥
  | φ₂φ₂φ₂φ₂ : 𝓥

/-- To each vertex, the association of the number of edges. -/
def 𝓥NoEdges : 𝓥 → ℕ := fun _ => 4

/-- To each vertex, associates the indexing map of half-edges associated with that edge. -/
def 𝓥Edges (v : 𝓥) : Fin (𝓥NoEdges v) → 𝓔 :=
  match v with
  | 𝓥.φ₁φ₁φ₂φ₂ => fun i =>
    match i with
    | (0 : Fin 4)=> 𝓔.complexScalarOut₁
    | (1 : Fin 4) => 𝓔.complexScalarIn₁
    | (2 : Fin 4) => 𝓔.complexScalarOut₂
    | (3 : Fin 4) => 𝓔.complexScalarIn₂
  | 𝓥.φ₁φ₁φ₁φ₁ => fun i =>
    match i with
    | (0 : Fin 4)=> 𝓔.complexScalarOut₁
    | (1 : Fin 4) => 𝓔.complexScalarIn₁
    | (2 : Fin 4) => 𝓔.complexScalarOut₁
    | (3 : Fin 4) => 𝓔.complexScalarIn₁
  | 𝓥.φ₂φ₂φ₂φ₂ => fun i =>
    match i with
    | (0 : Fin 4)=> 𝓔.complexScalarOut₂
    | (1 : Fin 4) => 𝓔.complexScalarIn₂
    | (2 : Fin 4) => 𝓔.complexScalarOut₂
    | (3 : Fin 4) => 𝓔.complexScalarIn₂

/-- A Feynman tree is an similar to a Feynman diagram, except there is an
  order to edges etc. It has a node for each vertex of a Feynman diagram,
  the (disjoint) union of Feynman diagrams, and the joining of two half edges of
  a Feynman diagram.

  To each Feynman tree is associated a Feynman diagram. But more then
  one distinct Feynman tree can lead to the same Feynman diagram.  -/
inductive FeynmanTree : {n : ℕ} → (c : Fin n → 𝓔) → Type where
  | vertex (v : 𝓥) : FeynmanTree (𝓥Edges v)
  | union {n m : ℕ} {c : Fin n → 𝓔} {c1 : Fin m → 𝓔} (t : FeynmanTree c) (t1 : FeynmanTree c1) :
    FeynmanTree (Sum.elim c c1 ∘ finSumFinEquiv.symm)
  | join {n : ℕ} {c : Fin n.succ.succ → 𝓔} : (i : Fin n.succ.succ) →
    (j : Fin n.succ) → (h : c (i.succAbove j) = ξ (c i)) → FeynmanTree c →
    FeynmanTree (c ∘ i.succAbove ∘ j.succAbove)

namespace FeynmanTree

/-- The number of nodes in a feynman tree. -/
def size {n : ℕ} {c : Fin n → 𝓔} : FeynmanTree c → ℕ := fun
  | vertex _ => 1
  | union t1 t2 => t1.size + t2.size + 1
  | join _ _ _ t => t.size + 1

/-- The number of half-edges associated with a Feynman tree. -/
def numHalfEdges {n : ℕ} {c : Fin n → 𝓔} : FeynmanTree c → ℕ := fun
  | vertex v => 𝓥NoEdges v
  | union t1 t2 => t1.numHalfEdges + t2.numHalfEdges
  | join _ _ _ t => t.numHalfEdges

/-- The type of vertices of a Feynman tree. -/
def vertexType {n : ℕ} {c : Fin n → 𝓔} : FeynmanTree c → Type := fun
  | vertex v => Unit
  | union t1 t2 => Sum t1.vertexType t2.vertexType
  | join _ _ _ t => t.vertexType

/-- Maps `vertexType` to `𝓥` taking each vertex to it's vertex color. -/
def vertexTo𝓥 {n : ℕ} {c : Fin n → 𝓔} : (T : FeynmanTree c) → T.vertexType → 𝓥 := fun
  | vertex v => fun _ => v
  | union t1 t2 => Sum.elim t1.vertexTo𝓥 t2.vertexTo𝓥
  | join _ _ _ t => t.vertexTo𝓥

/-- The type of half edges of a tensor tree. -/
def halfEdgeType {n : ℕ} {c : Fin n → 𝓔} : FeynmanTree c → Type := fun
  | vertex v => Fin (𝓥NoEdges v)
  | union t1 t2 => Sum t1.halfEdgeType t2.halfEdgeType
  | join _ _ _ t => t.halfEdgeType

/-- The map taking each half-edge to it's associated vertex. -/
def halfEdgeToVertex {n : ℕ} {c : Fin n → 𝓔} : (T : FeynmanTree c) → T.halfEdgeType → T.vertexType := fun
  | vertex v => fun _ => ()
  | union t1 t2 => Sum.map t1.halfEdgeToVertex t2.halfEdgeToVertex
  | join _ _ _ t => t.halfEdgeToVertex

/-- The inclusion of external half-edges into all half-edges. -/
def inclExternalEdges {n : ℕ} {c : Fin n → 𝓔} : (T : FeynmanTree c) →
    Fin n → T.halfEdgeType := fun
  | vertex v => fun i => i
  | union t1 t2 => Sum.map t1.inclExternalEdges t2.inclExternalEdges ∘ finSumFinEquiv.symm
  | join i j _ t => t.inclExternalEdges ∘ i.succAbove ∘ j.succAbove

/-- The type of edges of a Feynman tree. -/
def edgeType {n : ℕ} {c : Fin n → 𝓔} : FeynmanTree c → Type := fun
  | vertex v => Empty
  | union t1 t2 => Sum t1.edgeType t2.edgeType
  | join _ _ _ t => Sum t.edgeType Unit

end FeynmanTree

end TwoComplexScalar
