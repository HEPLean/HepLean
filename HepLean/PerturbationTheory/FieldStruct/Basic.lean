/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.RealVector.Basic
import HepLean.PerturbationTheory.FieldStatistics.Basic
import HepLean.SpaceTime.Basic
import HepLean.PerturbationTheory.FieldStatistics.OfFinset
/-!

# Field structures

-/

/-- A field structure is a type of fields plus a specification of the
  statistics (fermionic or bosonic) of each field. -/
structure FieldStruct where
  /-- The type of fields. This also includes anti-states. -/
  Fields : Type
  /-- The specification if a field is bosonic or fermionic. -/
  statistics : 𝓕 → FieldStatistic

namespace FieldStruct
variable (𝓕 : FieldStruct)

/-- Negative asymptotic states are specified by a field and a momentum. -/
def AsymptoticNegTime : Type := 𝓕.Fields × Lorentz.Contr 4

/-- Positive asymptotic states are specified by a field and a momentum. -/
def AsymptoticPosTime : Type := 𝓕.Fields × Lorentz.Contr 4

/-- States specified by a field and a space-time position. -/
def PositionStates : Type := 𝓕.Fields × SpaceTime

/-- The combination of asymptotic states and position states. -/
inductive States (𝓕 : FieldStruct) where
  | negAsymp : 𝓕.AsymptoticNegTime → 𝓕.States
  | position : 𝓕.PositionStates → 𝓕.States
  | posAsymp : 𝓕.AsymptoticPosTime → 𝓕.States

/-- Taking a state to its underlying field. -/
def statesToField : 𝓕.States → 𝓕.Fields
  | States.negAsymp φ => φ.1
  | States.position φ => φ.1
  | States.posAsymp φ => φ.1

/-- The statistics associated to a state. -/
def statesStatistic : 𝓕.States → FieldStatistic := 𝓕.statistics ∘ 𝓕.statesToField

/-- The field statistics associated with a state. -/
scoped[FieldStruct] notation  𝓕 "|>ₛ" φ => statesStatistic 𝓕 φ

/-- The field statistics associated with a list states. -/
scoped[FieldStruct] notation  𝓕 "|>ₛ" φ => FieldStatistic.ofList
    (statesStatistic 𝓕) φ

/-- The field statistic associated with a finite set-/
scoped[FieldStruct] notation  𝓕 "|>ₛ ⟨" f ","a "⟩"=> FieldStatistic.ofFinset
    (statesStatistic 𝓕) f a

end FieldStruct
