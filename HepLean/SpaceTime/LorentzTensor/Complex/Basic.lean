/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Logic.Function.CompTypeclasses
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Data.Complex.Basic
/-!

# Complex Lorentz Tensors

In this file we define complex Lorentz tensors.

We implicitly follow the definition of a modular operad.
This will relation should be made explicit in the future.

## References

-- For modular operads see: [Raynor][raynor2021graphical]
-- For Van der Waerden notation see: [Dreiner et al.][Dreiner:2008tw]

-/

/-- The possible `color` of an index for a complex Lorentz tensor.
 There are four possiblities, specifying how the index transforms under `SL(2, C)`.
 This follows Van der Waerden notation. -/
inductive ComplexLorentzTensor.Color where
  | up : ComplexLorentzTensor.Color
  | down : ComplexLorentzTensor.Color
  | weylUp : ComplexLorentzTensor.Color
  | weylDown : ComplexLorentzTensor.Color
  | weylUpDot : ComplexLorentzTensor.Color
  | weylDownDot : ComplexLorentzTensor.Color

/-- To set of allowed index values associated to a color of index. -/
def ComplexLorentzTensor.ColorIndex (μ : ComplexLorentzTensor.Color) : Type :=
  match μ with
  | ComplexLorentzTensor.Color.up => Fin 1 ⊕ Fin 3
  | ComplexLorentzTensor.Color.down => Fin 1 ⊕ Fin 3
  | ComplexLorentzTensor.Color.weylUp => Fin 2
  | ComplexLorentzTensor.Color.weylDown => Fin 2
  | ComplexLorentzTensor.Color.weylUpDot => Fin 2
  | ComplexLorentzTensor.Color.weylDownDot => Fin 2

/-- The instance of a finite type on the set of allowed index values for a given color. -/
instance (μ : ComplexLorentzTensor.Color) : Fintype (ComplexLorentzTensor.ColorIndex μ) :=
  match μ with
  | ComplexLorentzTensor.Color.up => instFintypeSum (Fin 1) (Fin 3)
  | ComplexLorentzTensor.Color.down => instFintypeSum (Fin 1) (Fin 3)
  | ComplexLorentzTensor.Color.weylUp => Fin.fintype 2
  | ComplexLorentzTensor.Color.weylDown => Fin.fintype 2
  | ComplexLorentzTensor.Color.weylUpDot => Fin.fintype 2
  | ComplexLorentzTensor.Color.weylDownDot => Fin.fintype 2

/-- The color index set for each color has a decidable equality. -/
instance (μ : ComplexLorentzTensor.Color) : DecidableEq (ComplexLorentzTensor.ColorIndex μ) :=
  match μ with
  | ComplexLorentzTensor.Color.up => instDecidableEqSum
  | ComplexLorentzTensor.Color.down => instDecidableEqSum
  | ComplexLorentzTensor.Color.weylUp => instDecidableEqFin 2
  | ComplexLorentzTensor.Color.weylDown => instDecidableEqFin 2
  | ComplexLorentzTensor.Color.weylUpDot => instDecidableEqFin 2
  | ComplexLorentzTensor.Color.weylDownDot => instDecidableEqFin 2

/-- The set of all index values associated with a map from `X` to `ComplexLorentzTensor.Color`. -/
def ComplexLorentzTensor.IndexValue {X : Type}  (c : X → ComplexLorentzTensor.Color) : Type :=
  (x : X) → ComplexLorentzTensor.ColorIndex (c x)

/-- Complex lorentz tensors. -/
def ComplexLorentzTensor {X : Type} (c : X → ComplexLorentzTensor.Color) : Type :=
  ComplexLorentzTensor.IndexValue c → ℂ

/-- Complex Lorentz tensors form an additive commutative monoid. -/
instance {X : Type} (c : X → ComplexLorentzTensor.Color) :
  AddCommMonoid (ComplexLorentzTensor c) := Pi.addCommMonoid

/-- Complex Lorentz tensors form a module over the complex numbers. -/
instance {X : Type} (c : X → ComplexLorentzTensor.Color) :
  Module ℂ (ComplexLorentzTensor c) := Pi.module _ _ _

/-- Complex Lorentz tensors form an additive commutative group. -/
instance {X : Type} (c : X → ComplexLorentzTensor.Color) :
  AddCommGroup (ComplexLorentzTensor c) := Pi.addCommGroup

namespace ComplexLorentzTensor

/-- A map taking every color to its dual color. -/
def τ : Color → Color
  | Color.up => Color.down
  | Color.down => Color.up
  | Color.weylUp => Color.weylDown
  | Color.weylDown => Color.weylUp
  | Color.weylUpDot => Color.weylDownDot
  | Color.weylDownDot => Color.weylUpDot

/-- The map τ is an involution. -/
@[simp]
lemma τ_involutive : Function.Involutive τ := by
  intro x
  cases x <;> rfl

/-!

## Color index value

-/

/-- An equivalence of `ColorIndex` types given an equality of color. -/
def colorIndexCast {μ₁ μ₂ : Color} (h : μ₁ = μ₂) :
    ColorIndex μ₁ ≃ ColorIndex μ₂ := Equiv.cast (congrArg ColorIndex h)

@[simp]
lemma colorIndexCast_symm {μ₁ μ₂ : Color} (h : μ₁ = μ₂) :
    (colorIndexCast h).symm = colorIndexCast h.symm := by
  rfl

/-- The allowed index values of a color are equal to that of the dual color. -/
lemma colorIndex_eq_on_dual {μ ν : Color} (h : μ = τ ν) :
    ColorIndex μ = ColorIndex ν := by
  match μ, ν, h with
  | .up, .down, _ => rfl
  | .down, .up, _ => rfl
  | .weylUp, .weylDown, _ => rfl
  | .weylDown, .weylUp, _ => rfl
  | .weylUpDot, .weylDownDot, _ => rfl
  | .weylDownDot, .weylUpDot, _ => rfl

/-- An equivalence between the allowed index values of a color and a color dual to it. -/
def colorIndexDualCast {μ ν : Color} (h : μ = τ ν) : ColorIndex μ ≃ ColorIndex ν :=
  Equiv.cast (colorIndex_eq_on_dual h)

@[simp]
lemma colorIndexDualCast_symm {μ ν : Color} (h : μ = τ ν) : (colorIndexDualCast h).symm =
    colorIndexDualCast ((Function.Involutive.eq_iff τ_involutive).mp h.symm) := by
  rfl

@[simp]
lemma colorIndexDualCast_trans {μ ν ξ : Color} (h : μ = τ ν) (h' : ν = τ ξ) :
    (colorIndexDualCast h).trans (colorIndexDualCast h') =
    colorIndexCast (by rw [h, h', τ_involutive]) := by
  simp [colorIndexDualCast, colorIndexCast]


@[simp]
lemma colorIndexDualCast_trans_colorsIndexCast {μ ν ξ : Color} (h : μ = τ ν) (h' : ν = ξ) :
    (colorIndexDualCast h).trans (colorIndexCast h') =
    colorIndexDualCast (by rw [h, h']) := by
  simp [colorIndexDualCast, colorIndexCast]

@[simp]
lemma colorIndexCast_trans_colorsIndexDualCast {μ ν ξ : Color} (h : μ = ν) (h' : ν = τ ξ) :
    (colorIndexCast h).trans (colorIndexDualCast h')  =
    colorIndexDualCast (by rw [h, h']) := by
  simp [colorIndexDualCast, colorIndexCast]

end ComplexLorentzTensor
