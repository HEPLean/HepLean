/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Matrix.ToLin
import HepLean.Meta.InformalDef
/-!
# The Standard Model

This file defines the basic properties of the standard model in particle physics.

-/
/-! TODO: Redefine the gauge group as a quotient of SU(3) x SU(2) x U(1) by a subgroup of ℤ₆. -/
universe v u
namespace StandardModel

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The global gauge group of the standard model. -/
abbrev GaugeGroup : Type :=
  specialUnitaryGroup (Fin 3) ℂ × specialUnitaryGroup (Fin 2) ℂ × unitary ℂ

end StandardModel
