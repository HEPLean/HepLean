/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Informal.Basic
import HepLean.PerturbationTheory.Wick.Species
import Mathlib.Data.Fin.Tuple.Basic
/-!
# Wick strings

A wick string is defined to be a sequence of input fields,
followed by a squence of vertices, followed by a sequence of output fields.

A wick string can be combined with an appropriate map to spacetime to produce a specific
term in the ring of operators. This has yet to be implemented.

-/

namespace Wick

variable {S : Species}

/-- A helper function for `WickString`. It is used to seperate incoming, vertex, and
  outgoing nodes. -/
inductive WickStringLast where
  | incoming : WickStringLast
  | vertex : WickStringLast
  | outgoing : WickStringLast
  | final : WickStringLast

open WickStringLast

/-- A wick string is a representation of a string of fields from a theory.
  The use of vertices in the Wick string
  allows us to identify which fields have the same space-time coordinate.

  Note: Fields are added to `c` from right to left - matching how we would write this on
  pen and paper.

  The incoming and outgoing fields should be viewed as asymptotic fields.
  While the internal fields associated with vertices are fields at fixed space-time points.
  -/
inductive WickString : {ni : ℕ} → (i : Fin ni → S.𝓯) → {n : ℕ} → (c : Fin n → S.𝓯) →
  {no : ℕ} → (o : Fin no → S.𝓯) → WickStringLast → Type where
  | empty : WickString Fin.elim0 Fin.elim0 Fin.elim0 incoming
  | incoming {n ni no : ℕ} {i : Fin ni → S.𝓯} {c : Fin n → S.𝓯}
      {o : Fin no → S.𝓯} (w : WickString i c o incoming) (e : S.𝓯) :
      WickString (Fin.cons e i) (Fin.cons e c) o incoming
  | endIncoming {n ni no : ℕ} {i : Fin ni → S.𝓯} {c : Fin n → S.𝓯}
      {o : Fin no → S.𝓯} (w : WickString i c o incoming) : WickString i c o vertex
  | vertex {n ni no : ℕ} {i : Fin ni → S.𝓯} {c : Fin n → S.𝓯}
      {o : Fin no → S.𝓯} (w : WickString i c o vertex) (v : S.𝓘) :
      WickString i (Fin.append (S.𝓘Fields v).2 c) o vertex
  | endVertex {n ni no : ℕ} {i : Fin ni → S.𝓯} {c : Fin n → S.𝓯}
      {o : Fin no → S.𝓯} (w : WickString i c o vertex) : WickString i c o outgoing
  | outgoing {n ni no : ℕ} {i : Fin ni → S.𝓯} {c : Fin n → S.𝓯}
      {o : Fin no → S.𝓯} (w : WickString i c o outgoing) (e : S.𝓯) :
      WickString i (Fin.cons e c) (Fin.cons e o) outgoing
  | endOutgoing {n ni no : ℕ} {i : Fin ni → S.𝓯} {c : Fin n → S.𝓯}
      {o : Fin no → S.𝓯} (w : WickString i c o outgoing) : WickString i c o final

namespace WickString

/-- The number of nodes in a Wick string. This is used to help prove termination. -/
def size {ni : ℕ} {i : Fin ni → S.𝓯} {n : ℕ} {c : Fin n → S.𝓯} {no : ℕ} {o : Fin no → S.𝓯}
    {f : WickStringLast} : WickString i c o f → ℕ := fun
  | empty => 0
  | incoming w e => size w + 1
  | endIncoming w => size w + 1
  | vertex w v => size w + 1
  | endVertex w => size w + 1
  | outgoing w e => size w + 1
  | endOutgoing w => size w + 1

/-- The number of vertices in a Wick string. This does NOT include external vertices. -/
def numIntVertex {ni : ℕ} {i : Fin ni → S.𝓯} {n : ℕ} {c : Fin n → S.𝓯} {no : ℕ} {o : Fin no → S.𝓯}
    {f : WickStringLast} : WickString i c o f → ℕ := fun
  | empty => 0
  | incoming w e => numIntVertex w
  | endIncoming w => numIntVertex w
  | vertex w v => numIntVertex w + 1
  | endVertex w => numIntVertex w
  | outgoing w e => numIntVertex w
  | endOutgoing w => numIntVertex w

/-- The vertices present in a Wick string. This does NOT include external vertices. -/
def intVertex {ni : ℕ} {i : Fin ni → S.𝓯} {n : ℕ} {c : Fin n → S.𝓯} {no : ℕ} {o : Fin no → S.𝓯}
    {f : WickStringLast} : (w : WickString i c o f) → Fin w.numIntVertex → S.𝓘 := fun
  | empty => Fin.elim0
  | incoming w e => intVertex w
  | endIncoming w => intVertex w
  | vertex w v => Fin.cons v (intVertex w)
  | endVertex w => intVertex w
  | outgoing w e => intVertex w
  | endOutgoing w => intVertex w

informal_definition intExtVertex where
  math :≈ "The vertices present in a Wick string, including external vertices."
  deps :≈ [``WickString]

informal_definition fieldToIntExtVertex where
  math :≈ "A function which takes a field and returns the internal or
    external vertex it is associated with."
  deps :≈ [``WickString]

informal_definition exponentialPrefactor where
  math :≈ "The combinatorical prefactor from the expansion of the
    exponential associated with a Wick string."
  deps :≈ [``intVertex, ``WickString]

informal_definition vertexPrefactor where
  math :≈ "The prefactor arising from the coefficent of vertices in the
    Lagrangian. This should not take account of the exponential prefactor."
  deps :≈ [``intVertex, ``WickString]

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

end Wick
