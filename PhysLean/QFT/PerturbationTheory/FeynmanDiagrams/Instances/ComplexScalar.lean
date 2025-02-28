/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.QFT.PerturbationTheory.FeynmanDiagrams.Basic
/-!
# Feynman diagrams in a complex scalar field theory

-/

namespace PhiFour
open CategoryTheory
open FeynmanDiagram
open PreFeynmanRule

/-- The pre-Feynman rules for a complex scalar theory. -/
@[simps!]
def complexScalarFeynmanRules : PreFeynmanRule where
  /- There is 2 types of `half-edge`. -/
  HalfEdgeLabel := Fin 2
  /- There is only 1 type of `edge`. -/
  EdgeLabel := Fin 1
  /- There are two types of `vertex`, two external `0` and internal `1`. -/
  VertexLabel := Fin 3
  edgeLabelMap x :=
    match x with
    | 0 => Over.mk ![0, 1]
  vertexLabelMap x :=
    match x with
    | 0 => Over.mk ![0]
    | 1 => Over.mk ![1]
    | 2 => Over.mk ![0, 0, 1, 1]

/-- An instance allowing us to use integers for edge labels for complex scalar theory. -/
instance (a : ℕ) : OfNat complexScalarFeynmanRules.EdgeLabel a where
  ofNat := (a : Fin _)

/-- An instance allowing us to use integers for half-edge labels for complex scalar theory. -/
instance (a : ℕ) : OfNat complexScalarFeynmanRules.HalfEdgeLabel a where
  ofNat := (a : Fin _)

/-- An instance allowing us to use integers for vertex labels for complex scalar theory. -/
instance (a : ℕ) : OfNat complexScalarFeynmanRules.VertexLabel a where
  ofNat := (a : Fin _)

/-- The pre feynman rules for complex scalars are finite. -/
instance : IsFinitePreFeynmanRule complexScalarFeynmanRules where
  edgeLabelDecidable := instDecidableEqFin _
  vertexLabelDecidable := instDecidableEqFin _
  halfEdgeLabelDecidable := instDecidableEqFin _
  vertexMapFintype := fun v =>
    match v with
    | 0 => Fin.fintype _
    | 1 => Fin.fintype _
    | 2 => Fin.fintype _
  edgeMapFintype := fun v =>
    match v with
    | 0 => Fin.fintype _
  vertexMapDecidable := fun v =>
    match v with
    | 0 => instDecidableEqFin _
    | 1 => instDecidableEqFin _
    | 2 => instDecidableEqFin _
  edgeMapDecidable := fun v =>
    match v with
    | 0 => instDecidableEqFin _

end PhiFour
