/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.RepresentationTheory.Basic

universe v u
namespace StandardModel

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The space-time (TODO: Change to Minkowski.) -/
abbrev spaceTime := EuclideanSpace ℝ (Fin 4)

abbrev guageGroup : Type := specialUnitaryGroup (Fin 2) ℂ × unitary ℂ


end StandardModel
