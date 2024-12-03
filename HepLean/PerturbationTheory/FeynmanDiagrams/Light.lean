/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Contract
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
    - A type of edges ed : 𝓔 → S.𝓕.
    - A type of half-edges 𝓱𝓔 with maps `e : 𝓱𝓔 → 𝓔`, `v : 𝓱𝓔 → 𝓥` and `f : 𝓱𝓔 → S.𝓯`
    Subject to the following conditions:
    - `𝓱𝓔` is a double cover of `𝓔` through `e`. That is,
      for each edge `x : 𝓔` there exists an isomorphism between `i : Fin 2 → e⁻¹ 𝓱𝓔 {x}`.
    - These isomorphisms must satisfy `⟦f(i(0))⟧ = ⟦f(i(1))⟧ = ed(e)` and `f(i(0)) = S.ξ (f(i(1)))`.
    - For each vertex `ver : 𝓥` there exists an isomorphism between the object (roughly)
      `(𝓘Fields v).2` and the pullback of `v` along `ver`."
  deps :≈ [``Wick.Species]
