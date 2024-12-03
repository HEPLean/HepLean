/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Species
/-!

# Feynman diagrams

This file currently contains a lighter implmentation of Feynman digrams than can be found in
`HepLean.PerturbationTheory.FeynmanDiagrams.Basic`. Eventually this will superseed that file.

The implmentation here is done in conjunction with Wicks species etc.

This file is currently a stub.
-/

informal_definition FeynmanDiagram where
  math :≈ "
    Let S be a WickSpecies
    A Feynman diagram contains the following data:
    - A type of vertices 𝓥 → S.𝓯 ⊕ S.𝓘.
    - A type of edges 𝓔 → S.𝓕.
    - A type of half-edges 𝓱𝓔 → 𝓔 × 𝓥 × S.𝓯.
    Subject to the following conditions:
    ...
  "
