/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalField.JetRep
public import PhyslibAlpha.Mathematics.MultisetAntidiagonal
/-!
# The derivative coefficients of a fibrewise representation

The base-point derivative coefficients of a fibrewise representation.

## i. Overview

Differentiating a transformed matter field involves derivatives of both the field and its gauge
transformation. This file extracts the transformation coefficients needed in that expansion. The
construction uses formal jets, represented by `SpaceTimeAlgebra ⊗[ℂ] V`, to retain spacetime
derivative data.

A representation is fibrewise when it commutes with multiplication by jets,
`rep U (χ • z) = χ • rep U z`, as an action at each spacetime point does, and every
`MatterField` has this property (`MatterField.repJet_smul`).

## ii. Key results

- `GaugeAlgebraRealization.repCoeff`, `GaugeAlgebraRealization.repDualCoeff` : the base-point
  derivative coefficients of a representation, and their transposes.
- `GaugeAlgebraRealization.repCoeff_zero_mul` : the zeroth coefficients are multiplicative.
- `JetComponentSpace.jetCoeffAt_jetCoeff` : the derivative coefficients of the gauge coefficient
  `jetCoeff rep U` are those of the representation.

## iii. Table of contents

- A. Derivative coefficients of a jet of endomorphisms
  - A.1. Iterated derivatives of a pure tensor
  - A.2. The coefficient at a multiset of directions
- B. The base-point coefficients of a representation

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct MvPowerSeries

/-!

## A. Derivative coefficients of a jet of endomorphisms

-/

section JetCoeffAt

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {G : Type} [Group G]

/-!

### A.1. Iterated derivatives of a pure tensor

-/

/-- The iterated formal derivative of a pure tensor `f ⊗ v` differentiates the jet-ring factor. -/
lemma jetIteratedDeriv_tmul (x : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) (v : V) :
    jetIteratedDeriv x (f ⊗ₜ[ℂ] v) = SpaceTimeAlgebra.iteratedPDeriv x f ⊗ₜ[ℂ] v := by
  induction x using Multiset.induction_on generalizing f with
  | empty => rw [jetIteratedDeriv_zero]; rfl
  | cons μ t ih =>
    rw [jetIteratedDeriv_cons, LinearMap.comp_apply, ih, jetDeriv_tmul,
      SpaceTimeAlgebra.iteratedPDeriv_cons, SpaceTimeAlgebra.iteratedPDeriv_pderiv]

namespace JetComponentSpace

/-!

### A.2. The coefficient at a multiset of directions

-/

/-- The base-point derivative coefficient indexed by `x` of a jet of endomorphisms of `V`. -/
noncomputable def jetCoeffAt (x : Multiset (Fin 1 ⊕ Fin 3)) :
    SpaceTimeAlgebra ⊗[ℂ] Module.End ℂ V →ₗ[ℂ] Module.End ℂ V :=
  jetEval ∘ₗ jetIteratedDeriv x

/-- On a pure tensor `f ⊗ T` the coefficient is the corresponding coefficient of `f` times `T`. -/
@[simp]
lemma jetCoeffAt_tmul (x : Multiset (Fin 1 ⊕ Fin 3)) (f : SpaceTimeAlgebra) (T : Module.End ℂ V) :
    jetCoeffAt x (f ⊗ₜ[ℂ] T)
      = constantCoeff (SpaceTimeAlgebra.iteratedPDeriv x f) • T := by
  rw [jetCoeffAt, LinearMap.comp_apply, jetIteratedDeriv_tmul, jetEval_tmul]

/-- At `v`, the coefficient of a jet of endomorphisms `c` is that of the `V`-valued jet `c v`. -/
lemma jetCoeffAt_apply (x : Multiset (Fin 1 ⊕ Fin 3))
    (c : SpaceTimeAlgebra ⊗[ℂ] Module.End ℂ V) (v : V) :
    jetCoeffAt x c v = jetEval (jetIteratedDeriv x (TensorProduct.lift
      ((LinearMap.llcomp ℂ V V (SpaceTimeAlgebra ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ SpaceTimeAlgebra V)) c v)) := by
  induction c using TensorProduct.inductionOn with
  | add c₁ c₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, h₁, h₂, map_add, LinearMap.add_apply, map_add,
      map_add]
  | tmul f T =>
    rw [jetCoeffAt_tmul, LinearMap.smul_apply,
      show TensorProduct.lift ((LinearMap.llcomp ℂ V V (SpaceTimeAlgebra ⊗[ℂ] V)).comp
        (TensorProduct.mk ℂ SpaceTimeAlgebra V)) (f ⊗ₜ[ℂ] T) v = f ⊗ₜ[ℂ] T v from rfl,
      jetIteratedDeriv_tmul, jetEval_tmul]

end JetComponentSpace

end JetCoeffAt

/-!

## B. The base-point coefficients of a representation

For a gauge jet `U` and a multiset `s` of directions, `repCoeff rep U s` is a linear map on the
value space `V`. To compute `repCoeff rep U s` on a value `v`, regard `v` as a constant jet, apply
`rep U`, differentiate in the directions recorded by `s`, and evaluate at the base point. The
result is a derivative value, with no division by the factorial `s!`.

The transposes `repDualCoeff`, which act on the complex covectors that label the components of
the field, play the role of `LocalGaugeData.adjointDualCoeff` for a general representation of the
jet gauge group. For a fibrewise representation the zeroth coefficients are multiplicative.

-/

namespace GaugeAlgebraRealization

section RepCoeff

variable {GJ : Type} [Group GJ]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The base-point derivative coefficient of `rep U` indexed by `x`, a complex-linear map on the
  value space. -/
noncomputable def repCoeff (rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V))
    (U : GJ) (x : Multiset (Fin 1 ⊕ Fin 3)) : V →ₗ[ℂ] V :=
  jetEval ∘ₗ jetIteratedDeriv x ∘ₗ rep U ∘ₗ jetOfConstant

/-- The transpose of `repCoeff`, acting on the complex dual index of a matter-field symbol. -/
noncomputable def repDualCoeff (rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V))
    (U : GJ) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ V :=
  (repCoeff rep U x).dualMap

/-- For a fibrewise representation, the base-point value of `rep U z` is the zeroth coefficient
  of `rep U` applied to the base-point value of `z`. -/
lemma jetEval_rep_of_smul (rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : GJ) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V), rep U
        (χ • z) = χ • rep U z)
    (U : GJ) (z : SpaceTimeAlgebra ⊗[ℂ] V) :
    jetEval (rep U z) = repCoeff rep U 0 (jetEval z) := by
  induction z using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]
  | tmul f v =>
    rw [show f ⊗ₜ[ℂ] v = f • jetOfConstant v from by
        rw [jetOfConstant_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      hlin, jetEval_smul, jetEval_smul, jetEval_jetOfConstant, map_smul]
    simp only [repCoeff, LinearMap.comp_apply, jetIteratedDeriv_zero, LinearMap.id_apply]

/-- The zeroth derivative coefficients of a fibrewise representation are multiplicative. -/
lemma repCoeff_zero_mul (rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : GJ) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V), rep U
        (χ • z) = χ • rep U z)
    (U W : GJ) : repCoeff rep (U * W) 0 = repCoeff rep U 0 ∘ₗ repCoeff rep W 0 := by
  refine LinearMap.ext fun v => ?_
  have h := jetEval_rep_of_smul rep hlin U (rep W (jetOfConstant v))
  simp only [repCoeff, LinearMap.comp_apply, jetIteratedDeriv_zero, LinearMap.id_apply, map_mul,
    Module.End.mul_apply] at h ⊢
  exact h

end RepCoeff

end GaugeAlgebraRealization

namespace JetComponentSpace

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {G : Type} [Group G]

/-- The derivative coefficients of the gauge coefficient `jetCoeff rep U` are those of `rep U`. -/
lemma jetCoeffAt_jetCoeff [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G (SpaceTimeAlgebra ⊗[ℂ] V)) (U : G)
    (x : Multiset (Fin 1 ⊕ Fin 3)) :
    jetCoeffAt x (jetCoeff rep U) = GaugeAlgebraRealization.repCoeff rep U x := by
  refine LinearMap.ext fun v => ?_
  rw [jetCoeffAt_apply, jetCoeff_spec]
  rfl

end JetComponentSpace
