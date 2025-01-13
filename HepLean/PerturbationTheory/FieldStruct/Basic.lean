/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.OperatorMap
import HepLean.Mathematics.Fin.Involutions
import HepLean.Lorentz.RealVector.Basic
import HepLean.SpaceTime.Basic
/-!

# Field structures

-/

/-- A field structure is a type of fields plus a specification of the
  statistics (fermionic or bosonic) of each field. -/
structure FieldStruct where
  /-- The type of fields. -/
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

/-- Returns true if `timeOrder a b` is true if `a` has time greater then or equal to `b`.
  This will put the stats at the greatest time to left. -/
def timeOrder : 𝓕.States → 𝓕.States → Prop
  | States.posAsymp _, _ => True
  | States.position φ0, States.position φ1 => φ1.2 0 ≤ φ0.2 0
  | States.position _, States.negAsymp _ => True
  | States.position _, States.posAsymp _ => False
  | States.negAsymp _, States.posAsymp _ => False
  | States.negAsymp _, States.position _ => False
  | States.negAsymp _, States.negAsymp _ => True

/-- Time ordering is total. -/
instance : IsTotal 𝓕.States 𝓕.timeOrder where
  total a b := by
    cases a <;> cases b <;> simp [timeOrder]
    exact LinearOrder.le_total _ _

/-- Time ordering is transitive. -/
instance : IsTrans 𝓕.States 𝓕.timeOrder where
  trans a b c := by
    cases a <;> cases b <;> cases c <;> simp [timeOrder]
    exact fun h1 h2 => Preorder.le_trans _ _ _ h2 h1

end FieldStruct
