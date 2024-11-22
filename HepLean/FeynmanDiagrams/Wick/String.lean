/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Basic
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

inductive WickStringLast where
  | incoming : WickStringLast
  | vertex : WickStringLast
  | outgoing : WickStringLast
  | final : WickStringLast

open WickStringLast

/-- A wick string is a representation of a string of fields from a theory.
  E.g. `φ(x1) φ(x2) φ(y) φ(y) φ(y) φ(x3)`. The use of vertices in the Wick string
  allows us to identify which fields have the same space-time coordinate. -/
inductive WickString : {n : ℕ} → (c : Fin n → 𝓔) → WickStringLast → Type where
  | empty : WickString Fin.elim0 incoming
  | incoming {n : ℕ} {c : Fin n → 𝓔} (w : WickString c incoming) (e : 𝓔) :
      WickString (Fin.cons e c) incoming
  | endIncoming {n : ℕ} {c : Fin n → 𝓔} (w : WickString c incoming) : WickString c vertex
  | vertex {n : ℕ} {c : Fin n → 𝓔} (w : WickString c vertex) (v : 𝓥) :
      WickString (Fin.append (𝓥Edges v) c) vertex
  | endVertex {n : ℕ} {c : Fin n → 𝓔} (w : WickString c vertex) : WickString c outgoing
  | outgoing {n : ℕ} {c : Fin n → 𝓔} (w : WickString c outgoing) (e : 𝓔) :
      WickString (Fin.cons e c) outgoing
  | endOutgoing {n : ℕ} {c : Fin n → 𝓔} (w : WickString c outgoing) : WickString c final

end TwoComplexScalar
