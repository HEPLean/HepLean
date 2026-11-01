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

The base-point derivative coefficients of a fibrewise representation and their composition laws.

## i. Overview

Differentiating a transformed matter field involves derivatives of both the field and its gauge
transformation. This file extracts the transformation coefficients needed in that expansion. The
construction uses formal jets, represented by `SpaceTimeAlgebra ⊗[ℂ] V`, to retain spacetime
derivative data.

A representation is fibrewise when it commutes with multiplication by jets,
`rep U (χ • z) = χ • rep U z`, as an action at each spacetime point does, and every
`MatterField` has this property (`MatterField.repJet_smul`). For such a representation on a
finite-dimensional value space the coefficients satisfy the composition laws of section C, which
are the composition laws of the matter part of a species.

## ii. Key results

- `GaugeAlgebraRealization.repCoeff`, `GaugeAlgebraRealization.repDualCoeff` : the base-point
  derivative coefficients of a representation, and their transposes.
- `GaugeAlgebraRealization.repCoeff_zero_mul` : the zeroth coefficients are multiplicative.
- `GaugeAlgebraRealization.repCoeff_mul`, `GaugeAlgebraRealization.repDualCoeff_mul` : the
  coefficients of a product are the Leibniz convolution of those of the factors.
- `GaugeAlgebraRealization.repCoeff_one`, `GaugeAlgebraRealization.repDualCoeff_one` : the
  coefficients of the identity.
- `JetComponentSpace.jetCoeffAt_jetCoeff` : the derivative coefficients of the gauge coefficient
  `jetCoeff rep U` are those of the representation.
- `JetComponentSpace.jetCoeffAt_mul`, `JetComponentSpace.jetCoeff_mul` : the derivative
  coefficients of a product of jets of endomorphisms, and multiplicativity of the gauge
  coefficient.

## iii. Table of contents

- A. Derivative coefficients of a jet of endomorphisms
  - A.1. Iterated derivatives of a pure tensor
  - A.2. The coefficient at a multiset of directions
- B. The base-point coefficients of a representation
- C. Composition laws of the coefficients
  - C.1. Products
  - C.2. The identity

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
jet gauge group. For a fibrewise representation the zeroth coefficients are multiplicative, and
that of the identity is the identity (section C.2), so they form a representation of the jet
gauge group on the value space. Its contragredient is `U ↦ repDualCoeff rep U⁻¹ 0`.

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

/-!

## C. Composition laws of the coefficients

Because the coefficients are derivative values with no factorial division, a product obeys the
Leibniz rule of `SpaceTimeAlgebra.constantCoeff_iteratedPDeriv_mul`. The coefficients of a product
are therefore a Leibniz convolution of those of the factors, the sum over all ways of distributing
the derivative directions between the two factors (the splits in `Multiset.antidiagonal`), with
the multiplicities prescribed by the Leibniz rule. The dual coefficients compose in the reverse
order.

### C.1. Products

-/

/-- The derivative coefficients of a product of jets of endomorphisms are the Leibniz convolution of
  the derivative coefficients of the factors. -/
lemma jetCoeffAt_mul (x : Multiset (Fin 1 ⊕ Fin 3)) (c d : SpaceTimeAlgebra ⊗[ℂ] Module.End ℂ V) :
    jetCoeffAt x (c * d)
      = (x.antidiagonal.map fun p => jetCoeffAt p.1 c * jetCoeffAt p.2 d).sum := by
  -- `add_mul` and `mul_add` do not rewrite in `SpaceTimeAlgebra ⊗ End V`; the distributive
  -- laws are applied by `exact`.
  induction c using TensorProduct.inductionOn with
  | add c₁ c₂ h₁ h₂ =>
    have hd : (c₁ + c₂) * d = c₁ * d + c₂ * d := by exact Distrib.right_distrib c₁ c₂ d
    rw [hd, map_add, h₁, h₂, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
    rw [map_add, add_mul]
  | tmul f T =>
    induction d using TensorProduct.inductionOn with
    | add d₁ d₂ h₁ h₂ =>
      have hd : f ⊗ₜ[ℂ] T * (d₁ + d₂) = f ⊗ₜ[ℂ] T * d₁ + f ⊗ₜ[ℂ] T * d₂ := by
        exact Distrib.left_distrib _ d₁ d₂
      rw [hd, map_add, h₁, h₂, ← Multiset.sum_map_add]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
      rw [map_add, mul_add]
    | tmul g S =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, jetCoeffAt_tmul,
        SpaceTimeAlgebra.constantCoeff_iteratedPDeriv_mul, Multiset.sum_smul, Multiset.map_map]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
      rw [Function.comp_apply, jetCoeffAt_tmul, jetCoeffAt_tmul, smul_mul_smul_comm]

/-- The gauge coefficient of a fibrewise representation is multiplicative. -/
lemma jetCoeff_mul [Module.Free ℂ V] [Module.Finite ℂ V]
    {rep : Representation ℂ G (SpaceTimeAlgebra ⊗[ℂ] V)}
    (hlin : ∀ (U : G) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) (U W : G) :
    jetCoeff rep (U * W) = jetCoeff rep U * jetCoeff rep W :=
  lift_injective fun v => (jetCoeff_spec rep (U * W) v).trans
    (coeff_mul_of_smul_comm hlin (jetCoeff rep) (jetCoeff_spec rep) U W v).symm

end JetComponentSpace

namespace GaugeAlgebraRealization

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {G : Type} [Group G] {rep : Representation ℂ G (SpaceTimeAlgebra ⊗[ℂ] V)}

/-- The derivative coefficients of a fibrewise representation compose by Leibniz convolution. -/
lemma repCoeff_mul [Module.Free ℂ V] [Module.Finite ℂ V]
    (hlin : ∀ (U : G) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) (U W : G) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    repCoeff rep (U * W) x
      = (x.antidiagonal.map fun p => repCoeff rep U p.1 ∘ₗ repCoeff rep W p.2).sum := by
  rw [← JetComponentSpace.jetCoeffAt_jetCoeff, JetComponentSpace.jetCoeff_mul hlin,
    JetComponentSpace.jetCoeffAt_mul]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => ?_)
  rw [JetComponentSpace.jetCoeffAt_jetCoeff, JetComponentSpace.jetCoeffAt_jetCoeff]
  rfl

/-- The dual coefficients of a product compose by Leibniz convolution, in the reverse order. -/
lemma repDualCoeff_mul [Module.Free ℂ V] [Module.Finite ℂ V]
    (hlin : ∀ (U : G) (χ : SpaceTimeAlgebra) (z : SpaceTimeAlgebra ⊗[ℂ] V),
      rep U (χ • z) = χ • rep U z) (U W : G) (x : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    repDualCoeff rep (U * W) x φ
      = (x.antidiagonal.map fun p => repDualCoeff rep W p.2 (repDualCoeff rep U p.1 φ)).sum := by
  refine LinearMap.ext fun v => ?_
  simp only [repDualCoeff, repCoeff_mul hlin, LinearMap.dualMap_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, map_multiset_sum, Function.comp_apply,
    LinearMap.comp_apply]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ => rfl)

/-!

### C.2. The identity

-/

/-- At the identity the zeroth coefficient is the identity and the higher derivative
  coefficients vanish. -/
lemma repCoeff_one (x : Multiset (Fin 1 ⊕ Fin 3)) :
    repCoeff rep 1 x = if x = 0 then LinearMap.id else 0 := by
  refine LinearMap.ext fun v => ?_
  rw [repCoeff, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_one,
    Module.End.one_apply, jetOfConstant_apply, jetIteratedDeriv_tmul, jetEval_tmul,
    SpaceTimeAlgebra.constantCoeff_iteratedPDeriv, MvPowerSeries.coeff_one]
  by_cases hx : x = 0
  · subst hx
    simp
  · simp [hx]

/-- At the identity the zeroth dual coefficient is the identity and the higher derivative dual
  coefficients vanish. -/
lemma repDualCoeff_one (x : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    repDualCoeff rep 1 x φ = if x = 0 then φ else 0 := by
  rw [repDualCoeff, repCoeff_one]
  by_cases hx : x = 0
  · rw [ite_eq_left hx, ite_eq_left hx]
    exact LinearMap.ext fun v => rfl
  · rw [ite_eq_right hx, ite_eq_right hx]
    exact LinearMap.ext fun v => map_zero φ

end GaugeAlgebraRealization
