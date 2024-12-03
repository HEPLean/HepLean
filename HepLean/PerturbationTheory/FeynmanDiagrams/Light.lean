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

-/
/-! TODO: Remove this namespace-/
namespace LightFeynman

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

informal_definition _root_.Wick.Contract.toFeynmanDiagram where
  math :≈ "The Feynman diagram constructed from a complete Wick contraction."
  deps :≈ [``TwoComplexScalar.WickContract, ``FeynmanDiagram]

informal_lemma _root_.Wick.Contract.toFeynmanDiagram_surj where
  math :≈ "The map from Wick contractions to Feynman diagrams is surjective."
  physics :≈ "Every Feynman digram corresponds to some Wick contraction."
  deps :≈ [``TwoComplexScalar.WickContract, ``FeynmanDiagram]

informal_definition FeynmanDiagram.toSimpleGraph where
  math :≈ "The simple graph underlying a Feynman diagram."
  deps :≈ [``FeynmanDiagram]

informal_definition FeynmanDiagram.IsConnected where
  math :≈ "A Feynman diagram is connected if its underlying simple graph is connected."
  deps :≈ [``FeynmanDiagram]

informal_definition _root_.Wick.Contract.toFeynmanDiagram_isConnected_iff where
  math :≈ "The Feynman diagram corresponding to a Wick contraction is connected
    if and only if the Wick contraction is connected."
  deps :≈ [``TwoComplexScalar.WickContract.IsConnected, ``FeynmanDiagram.IsConnected]

/-! TODO: Define an equivalence relation on Wick contracts related to the their underlying tensors
  been equal after permutation. Show that two  Wick contractions are equal under this
  equivalence relation if and only if they have the same Feynman diagram. First step
  is to turn these statements into appropriate informal lemmas and definitions. -/

end LightFeynman
