/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.JetComponent.GaugeAction
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.CovariantDeriv
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.RepCoeff
/-!
# The transformation law of a derivative symbol

## i. Overview

`LocalGaugeData.TransformsIn` demands of a family of component functions that each
derivative symbol transform by the all-orders Leibniz convolution of the base-point Taylor
coefficients `GaugeAlgebraRealization.repDualCoeff` of the gauge jet. What the gauge action
on the jet component space is *built* from is `symbolAction`, the action of the coefficient
`jetCoeff rep U⁻¹ : SpaceTimeAlgebra ⊗ End V` through `SpaceTimeDerivAlgebraℂ.jetRingAction` on the
derivative label. This file identifies the two, for any group `G` acting fibrewise on the
jets of the field.

The bridge is `SpaceTimeDerivAlgebraℂ.jetRingAction_basis_multiset`, which puts the action of
a jet on a derivative monomial into the convolution form that `TransformsIn` wants. What
remains is to recognise the scalars it produces — the base-point Taylor coefficients of the
jet-ring factor of the gauge coefficient — as `GaugeAlgebraRealization.repCoeff`. That is done by
`jetCoeffAt`, the base-point Taylor coefficient of a jet of endomorphisms, which on the
gauge coefficient reproduces `repCoeff` because `jetCoeff` reproduces `rep U` on constant
jets (`jetCoeffAt_jetCoeff`, in
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.RepCoeff`).

The result, `repDual_basis_tmul`, is stated for an arbitrary fibrewise gauge action `rep`.
The conjugate half of the component space is the same construction at `repConj rep`, so it
is an instance of the same lemma rather than a second proof.

## ii. Key results

- `JetComponentSpace.symbolAction_basis_tmul` : a coefficient acts on a derivative monomial
  by the Leibniz convolution of its base-point Taylor coefficients.
- `JetComponentSpace.repDual_basis_tmul` : the transformation law of the derivative symbol
  `∂_s ψ_φ`, in the form demanded by `LocalGaugeData.TransformsIn`.

## iii. Table of contents

- A. The transformation law of a derivative symbol
  - A.1. Bookkeeping for transposes and multiset sums
  - A.2. The action of a coefficient on a derivative monomial
  - A.3. The gauge action on a derivative symbol

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct MvPowerSeries

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {G : Type} [Group G]

namespace JetComponentSpace

/-!

## A. The transformation law of a derivative symbol

-/

/-!

### A.1. Bookkeeping for transposes and multiset sums

-/

/-- The transpose is additive in the endomorphism. -/
private lemma dualMap_add_apply (A B : Module.End ℂ V) (φ : Module.Dual ℂ V) :
    (A + B).dualMap φ = A.dualMap φ + B.dualMap φ := by
  ext v
  simp

/-- The transpose is homogeneous in the endomorphism. -/
private lemma dualMap_smul_apply (c : ℂ) (T : Module.End ℂ V) (φ : Module.Dual ℂ V) :
    (c • T).dualMap φ = c • T.dualMap φ := by
  ext v
  simp

/-- A multiset sum in the derivative label distributes out of a pure symbol. -/
private lemma sum_tmul_right (m : Multiset SpaceTimeDerivAlgebraℂ) (w : Module.Dual ℂ V) :
    m.sum ⊗ₜ[ℂ] w = (m.map fun a => a ⊗ₜ[ℂ] w).sum := by
  rw [show m.sum ⊗ₜ[ℂ] w
      = ((TensorProduct.mk ℂ SpaceTimeDerivAlgebraℂ (Module.Dual ℂ V)).flip w) m.sum from rfl,
    map_multiset_sum]
  rfl

/-!

### A.2. The action of a coefficient on a derivative monomial

-/

/-- A coefficient acts on the derivative symbol `∂_s ψ_φ` by the all-orders Leibniz
  convolution of its base-point Taylor coefficients: each splitting `s = s₁ + s₂` of the
  derivative multiset contributes the Taylor coefficient at `s₁` acting on the target index
  of the lower symbol `∂_{s₂} ψ_φ`.

  This is `SpaceTimeDerivAlgebraℂ.jetRingAction_basis_multiset` in the derivative label,
  together with the identification of the scalars it produces as `jetCoeffAt`; both sides
  are additive in the coefficient, so it suffices to check it on a pure tensor. -/
lemma symbolAction_basis_tmul (c : SpaceTimeAlgebra ⊗[ℂ] Module.End ℂ V)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    symbolAction c (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ)
      = (s.antidiagonal.map fun p =>
          SpaceTimeDerivAlgebraℂ.basis p.2 ⊗ₜ[ℂ] (jetCoeffAt p.1 c).dualMap φ).sum := by
  induction c using TensorProduct.inductionOn with
  | add c₁ c₂ h₁ h₂ =>
    rw [map_add, LinearMap.add_apply, h₁, h₂, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    rw [map_add, dualMap_add_apply, TensorProduct.tmul_add]
  | tmul f T =>
    rw [symbolAction_tmul, TensorProduct.map_tmul,
      SpaceTimeDerivAlgebraℂ.jetRingAction_basis_multiset, sum_tmul_right, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    rw [Function.comp_apply, TensorProduct.smul_tmul, jetCoeffAt_tmul, dualMap_smul_apply]
    rfl

/-!

### A.3. The gauge action on a derivative symbol

-/

/-- The transformation law of the derivative symbol `∂_s ψ_φ` under the jet gauge group:
  the all-orders Leibniz convolution of the dual representation coefficients
  `GaugeAlgebraRealization.repDualCoeff` against lower symbols, with no inhomogeneous term. This is
  the identity the `LocalGaugeData.TransformsIn` obligations of a matter field rest on.

  Nothing here is special to the unconjugated half of the component space: the conjugate
  half is this lemma at `repConj rep`. -/
lemma repDual_basis_tmul [Module.Free ℂ V] [Module.Finite ℂ V]
    (rep : Representation ℂ G (SpaceTimeAlgebra ⊗[ℂ] V))
    (hlin : ∀ (U : G) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z)
    (U : G) (s : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    repDual rep hlin U (SpaceTimeDerivAlgebraℂ.basis s ⊗ₜ[ℂ] φ)
      = (s.antidiagonal.map fun p =>
          SpaceTimeDerivAlgebraℂ.basis p.2 ⊗ₜ[ℂ]
            GaugeAlgebraRealization.repDualCoeff rep U⁻¹ p.1 φ).sum := by
  rw [show repDual rep hlin U = symbolAction (jetCoeff rep U⁻¹) from rfl,
    symbolAction_basis_tmul]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => by
    rw [jetCoeffAt_jetCoeff, GaugeAlgebraRealization.repDualCoeff])

end JetComponentSpace
