/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Wick.Species
/-!
# Wick strings

Currently this file is only for an example of Wick strings, correpsonding to a
theory with two complex scalar fields. The concepts will however generalize.

A wick string is defined to be a sequence of input fields,
followed by a squence of vertices, followed by a sequence of output fields.

A wick string can be combined with an appropriate map to spacetime to produce a specific
term in the ring of operators. This has yet to be implemented.

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
@[nolint unusedArguments]
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

/-- A helper function for `WickString`. It is used to seperate incoming, vertex, and
  outgoing nodes. -/
inductive WickStringLast where
  | incoming : WickStringLast
  | vertex : WickStringLast
  | outgoing : WickStringLast
  | final : WickStringLast

open WickStringLast

/-- A wick string is a representation of a string of fields from a theory.
  E.g. `φ(x1) φ(x2) φ(y) φ(y) φ(y) φ(x3)`. The use of vertices in the Wick string
  allows us to identify which fields have the same space-time coordinate.

  Note: Fields are added to `c` from right to left - matching how we would write this on
  pen and paper. -/
inductive WickString : {ni : ℕ} → (i : Fin ni → 𝓔) → {n : ℕ} → (c : Fin n → 𝓔) →
  {no : ℕ} → (o : Fin no → 𝓔) → WickStringLast → Type where
  | empty : WickString Fin.elim0 Fin.elim0 Fin.elim0 incoming
  | incoming {n ni no : ℕ} {i : Fin ni → 𝓔} {c : Fin n → 𝓔}
      {o : Fin no → 𝓔} (w : WickString i c o incoming) (e : 𝓔) :
      WickString (Fin.cons e i) (Fin.cons e c) o incoming
  | endIncoming {n ni no : ℕ} {i : Fin ni → 𝓔} {c : Fin n → 𝓔}
      {o : Fin no → 𝓔} (w : WickString i c o incoming) : WickString i c o vertex
  | vertex {n ni no : ℕ} {i : Fin ni → 𝓔} {c : Fin n → 𝓔}
      {o : Fin no → 𝓔} (w : WickString i c o vertex) (v : 𝓥) :
      WickString i (Fin.append (𝓥Edges v) c) o vertex
  | endVertex {n ni no : ℕ} {i : Fin ni → 𝓔} {c : Fin n → 𝓔}
      {o : Fin no → 𝓔} (w : WickString i c o vertex) : WickString i c o outgoing
  | outgoing {n ni no : ℕ} {i : Fin ni → 𝓔} {c : Fin n → 𝓔}
      {o : Fin no → 𝓔} (w : WickString i c o outgoing) (e : 𝓔) :
      WickString i (Fin.cons e c) (Fin.cons e o) outgoing
  | endOutgoing {n ni no : ℕ} {i : Fin ni → 𝓔} {c : Fin n → 𝓔}
      {o : Fin no → 𝓔} (w : WickString i c o outgoing) : WickString i c o final

namespace WickString

/-- The number of nodes in a Wick string. This is used to help prove termination. -/
def size {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔} {no : ℕ} {o : Fin no → 𝓔}
    {f : WickStringLast} : WickString i c o f → ℕ := fun
  | empty => 0
  | incoming w e => size w + 1
  | endIncoming w => size w + 1
  | vertex w v => size w + 1
  | endVertex w => size w + 1
  | outgoing w e => size w + 1
  | endOutgoing w => size w + 1

/-- The number of vertices in a Wick string. This does NOT include external vertices. -/
def numVertex {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔} {no : ℕ} {o : Fin no → 𝓔}
    {f : WickStringLast} : WickString i c o f → ℕ := fun
  | empty => 0
  | incoming w e => numVertex w
  | endIncoming w => numVertex w
  | vertex w v => numVertex w + 1
  | endVertex w => numVertex w
  | outgoing w e => numVertex w
  | endOutgoing w => numVertex w

/-- The vertices present in a Wick string. This does NOT include external vertices. -/
def vertices {ni : ℕ} {i : Fin ni → 𝓔} {n : ℕ} {c : Fin n → 𝓔} {no : ℕ} {o : Fin no → 𝓔}
    {f : WickStringLast} : (w : WickString i c o f) → Fin w.numVertex → 𝓥 := fun
  | empty => Fin.elim0
  | incoming w e => vertices w
  | endIncoming w => vertices w
  | vertex w v => Fin.cons v (vertices w)
  | endVertex w => vertices w
  | outgoing w e => vertices w
  | endOutgoing w => vertices w

informal_definition fieldToVertex where
  math :≈ "A function which takes a field and returns the vertex it is associated with.
    This is a map from `Fin n` to `Fin w.numVertex`"
  deps :≈ [``WickString]

informal_definition exponentialPrefactor where
  math :≈ "The combinatorical prefactor from the expansion of the
    exponential associated with a Wick string."
  deps :≈ [``vertices, ``WickString]

informal_definition vertexPrefactor where
  math :≈ "The prefactor arising from the coefficent of vertices in the
    Lagrangian. This should not take account of the exponential prefactor."
  deps :≈ [``vertices, ``WickString]

informal_definition minNoLoops where
  math :≈ "The minimum number of loops a Feynman diagram based on a given Wick string can have.
    There should be a lemma proving this statement."
  deps :≈ [``WickString]

informal_definition LoopLevel where
  math :≈ "The type of Wick strings for fixed input and output which may permit a Feynman diagram
    which have a number of loops less than or equal to some number."
  deps :≈ [``minNoLoops, ``WickString]

informal_lemma loopLevel_fintype where
  math :≈ "The instance of a finite type on `LoopLevel`."
  deps :≈ [``LoopLevel]

end WickString

end TwoComplexScalar
