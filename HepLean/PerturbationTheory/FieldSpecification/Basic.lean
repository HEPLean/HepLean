/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.RealVector.Basic
import HepLean.PerturbationTheory.FieldStatistics.ExchangeSign
import HepLean.SpaceTime.Basic
import HepLean.PerturbationTheory.FieldStatistics.OfFinset
import HepLean.Meta.Remark.Basic
/-!

# Field specification

In this module is the definition of a field specification.
A field specification is a structure consisting of a type of fields and a
the field statistics of each field.

From each field we can create three different types of `FieldOp`.
- Negative asymptotic states.
- Position states.
- Positive asymptotic states.

These states carry the same field statistic as the field they are derived from.

-/

remark fieldSpecification_intro := "The raw ingredients of a field theory are:
  - The specification of the fields.
  - Whether each field is a boson or a fermion.
  - Vertices present in the Lagrangian.
  - The coefficent of each vertex.

  We call the first two of these ingredients the `FieldSpecification` of the theory. "

/-- A field specification is a type, `Fields`, elements of which are fields
  present in a theory, and a map `statistics` from `Fields` to `FieldStatistic` which
  identifies each field as a boson or a fermion. -/
structure FieldSpecification where
  /-- The type of fields. This also includes anti-states. -/
  Fields : Type
  /-- The specification if a field is bosonic or fermionic. -/
  statistics : Fields → FieldStatistic

namespace FieldSpecification
variable (𝓕 : FieldSpecification)

/-- An incoming asymptotic state is a field and a momentum. -/
def IncomingAsymptotic : Type := 𝓕.Fields × Lorentz.Contr 4

/-- An outgoing asymptotic states is a field and a momentum. -/
def OutgoingAsymptotic : Type := 𝓕.Fields × Lorentz.Contr 4

/-- A position state is a field and a space-time position. -/
def PositionFieldOp : Type := 𝓕.Fields × SpaceTime

/-- The type FieldOp is the inductive type combining the asymptotic states and position states. -/
inductive FieldOp (𝓕 : FieldSpecification) where
  | inAsymp : 𝓕.IncomingAsymptotic → 𝓕.FieldOp
  | position : 𝓕.PositionFieldOp → 𝓕.FieldOp
  | outAsymp : 𝓕.OutgoingAsymptotic → 𝓕.FieldOp

/-- Taking a state to its underlying field. -/
def fieldOpToField : 𝓕.FieldOp → 𝓕.Fields
  | FieldOp.inAsymp φ => φ.1
  | FieldOp.position φ => φ.1
  | FieldOp.outAsymp φ => φ.1

/-- The bool on `FieldOp` which is true only for position states. -/
def statesIsPosition : 𝓕.FieldOp → Bool
  | FieldOp.position _ => true
  | _ => false

/-- The statistics associated to a state. -/
def statesStatistic : 𝓕.FieldOp → FieldStatistic := 𝓕.statistics ∘ 𝓕.fieldOpToField

/-- The field statistics associated with a state. -/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ => statesStatistic 𝓕 φ

/-- The field statistics associated with a list states. -/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ => FieldStatistic.ofList
    (statesStatistic 𝓕) φ

/-- The field statistic associated with a finite set-/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" "⟨" f ","a "⟩"=> FieldStatistic.ofFinset
    (statesStatistic 𝓕) f a

end FieldSpecification
