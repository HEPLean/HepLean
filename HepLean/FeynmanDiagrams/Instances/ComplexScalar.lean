/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FeynmanDiagrams.Basic
/-!
# Feynman diagrams in a complex scalar field theory



-/


namespace PhiFour
open CategoryTheory
open FeynmanDiagram
open PreFeynmanRule

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

instance (a : ℕ) : OfNat complexScalarFeynmanRules.EdgeLabel a where
  ofNat := (a : Fin _)

instance (a : ℕ) : OfNat complexScalarFeynmanRules.HalfEdgeLabel a where
  ofNat := (a : Fin _)

instance (a : ℕ) : OfNat complexScalarFeynmanRules.VertexLabel a where
  ofNat := (a : Fin _)


instance : IsFinitePreFeynmanRule complexScalarFeynmanRules where
  edgeLabelDecidable :=  instDecidableEqFin _
  vertexLabelDecidable := instDecidableEqFin _
  halfEdgeLabelDecidable := instDecidableEqFin _
  vertexMapFintype := fun v =>
    match v with
    | 0 => Fin.fintype _
    | 1  => Fin.fintype _
    | 2  => Fin.fintype _
  edgeMapFintype := fun v =>
    match v with
    | 0 => Fin.fintype _
  vertexMapDecidable := fun v =>
    match v with
    | 0 => instDecidableEqFin _
    | 1  => instDecidableEqFin _
    | 2  => instDecidableEqFin _
  edgeMapDecidable := fun v =>
    match v with
    | 0 => instDecidableEqFin _





set_option maxRecDepth 1000 in
def loopProp : FeynmanDiagram complexScalarFeynmanRules :=
  mk' ![0, 0, 0] ![0, 2, 1] ![⟨0, 0, 0⟩, ⟨1, 0, 1⟩,
    ⟨0, 1, 1⟩, ⟨1, 1, 1⟩, ⟨0, 2, 1⟩, ⟨1, 2, 2⟩] (by decide)

instance : IsFiniteDiagram loopProp where
  𝓔Fintype := Fin.fintype _
  𝓔DecidableEq := instDecidableEqFin _
  𝓥Fintype := Fin.fintype _
  𝓥DecidableEq := instDecidableEqFin _
  𝓱𝓔Fintype := Fin.fintype _
  𝓱𝓔DecidableEq := instDecidableEqFin _

def prop : FeynmanDiagram complexScalarFeynmanRules :=
  mk' ![0] ![0, 1] ![⟨0, 0, 0⟩, ⟨1, 0, 1⟩] (by decide)

instance : IsFiniteDiagram prop where
  𝓔Fintype := Fin.fintype _
  𝓔DecidableEq := instDecidableEqFin _
  𝓥Fintype := Fin.fintype _
  𝓥DecidableEq := instDecidableEqFin _
  𝓱𝓔Fintype := Fin.fintype _
  𝓱𝓔DecidableEq := instDecidableEqFin _

lemma prop_symmetryFactor_eq_one : symmetryFactor prop = 1 := by decide



end PhiFour
