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

end TwoComplexScalar
