/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Basic
import HepLean.Meta.Informal
/-!

# Wick Species

Note: There is very likely a much better name for what we here call a Wick Species.

A Wick Species is a structure containing the basic information needed to write wick contractions
for a theory, and calculate their corresponding Feynman diagrams.

-/

/-! TODO: There should be some sort of notion of a group action on a Wick Species. -/
namespace Wick

/-- The basic structure needed to write down Wick contractions for a theory and
  calculate the corresponding Feynman diagrams.

  WARNING: This definition is not yet complete.
   -/
structure Species where
  /-- The color of Field operators which appear in a theory. -/
  𝓕 : Type
  /-- The map taking a field operator to its dual operator. -/
  ξ : 𝓕 → 𝓕
  /-- The condition that `ξ` is an involution. -/
  ξ_involutive : Function.Involutive ξ
  /-- The color of vertices which appear in a theory. -/
  𝓥 : Type
  /-- The edges each vertex corresponds to. -/
  𝓥Fields : 𝓥 → Σ n, Fin n → 𝓕

end Wick
