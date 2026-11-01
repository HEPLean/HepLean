/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.SpaceAndTime.SpaceTime.SpaceTimeDerivAlgebra
public import Mathlib.LinearAlgebra.Dual.Lemmas
/-!
# The gauge-boson field of a gauge theory

## i. Overview

The gauge bosons of a gauge theory with Lie algebra `𝔤` are jointly one bosonic field
valued in `Lorentz.CoVector ⊗[ℝ] 𝔤`: a spacetime covector with values in the gauge
algebra. Its components are the fields `A_μ^a`, but **no basis of the gauge algebra is
chosen**: the adjoint index is carried by an abstract covector `φ : Module.Dual ℝ 𝔤`
throughout.

This file is the target space alone — its linear structure, the Lorentz action, the
global gauge action, and the jet component space spanned by the component functions
`∂_s A_μ^φ`. The jet algebra built on it, and the actions and gradings it carries, are in
`Physlib.ClassicalFieldTheory.GaugeTheory.GaugeBoson.LocalGaugeFieldAlgebra`. For the Standard
Model, `𝔤` is `StandardModel.GaugeAlgebra`.

## ii. Key results

- `GaugeBoson` : the target space of the gauge-boson field.
- `GaugeBoson.repLorentzGroup` : the Lorentz action on the target space.
- `GaugeBoson.repValue` : the global gauge action on the target space, from a
  representation of the value group.
- `GaugeBoson.JetComponentSpace` : the span of the component functions `∂_s A_μ^φ`.
- `GaugeBoson.componentDual` : the covector picking out a spacetime and an adjoint index.
- `GaugeBoson.componentCovector` : the real covector on gauge-potential values reading the
  component `A_μ^a`.
- `GaugeBoson.repLorentzGroup_dual_componentCovector` : the component covectors transform as a
  Lorentz covector in their spacetime index.

## iii. Table of contents

- A. The target space of the gauge-boson field
  - A.1. Linear structure
  - A.2. The Lorentz action on the target space
  - A.3. The global gauge action on the target space
- B. The jet component space
  - B.1. The component covectors

## iv. References

* None.

-/

@[expose] public section

variable {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

open TensorProduct

/-!

## A. The target space of the gauge-boson field

-/

variable (𝔤) in
/-- The target vector space of the gauge-boson field: a spacetime covector
  with values in the gauge algebra. Its components are the fields `A_μ^a`; here the
  adjoint index is kept abstract, as the gauge-algebra factor. -/
@[ext]
structure GaugeBoson where
  /-- The underlying covector-valued gauge algebra element. -/
  val : Lorentz.CoVector ⊗[ℝ] 𝔤

namespace GaugeBoson

/-!

### A.1. Linear structure

-/

variable (𝔤) in
/-- Identifies a gauge boson with its underlying tensor-product value. -/
def valEquiv : (GaugeBoson 𝔤) ≃ Lorentz.CoVector ⊗[ℝ] 𝔤 where
  toFun := val
  invFun := fun m => ⟨m⟩

noncomputable instance : AddCommGroup (GaugeBoson 𝔤) := Equiv.addCommGroup (valEquiv 𝔤)

noncomputable instance : Module ℝ (GaugeBoson 𝔤) :=
  AddEquiv.module ℝ { valEquiv 𝔤 with map_add' _ _ := rfl }

variable (𝔤) in
/-- The linear identification with the underlying tensor product. -/
def valLinEquiv : (GaugeBoson 𝔤) ≃ₗ[ℝ] Lorentz.CoVector ⊗[ℝ] 𝔤 where
  toFun := val
  invFun := fun m => ⟨m⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp]
lemma valLinEquiv_apply (v : (GaugeBoson 𝔤)) : (valLinEquiv 𝔤) v = v.val := rfl

lemma valLinEquiv_symm_apply (m : Lorentz.CoVector ⊗[ℝ] 𝔤) :
    (valLinEquiv 𝔤).symm m = ⟨m⟩ := rfl

@[simp]
lemma val_add (v₁ v₂ : (GaugeBoson 𝔤)) : (v₁ + v₂).val = v₁.val + v₂.val := rfl

@[simp]
lemma val_smul (r : ℝ) (v : (GaugeBoson 𝔤)) : (r • v).val = r • v.val := rfl

variable [Module.Finite ℝ 𝔤] in
instance : Module.Finite ℝ (GaugeBoson 𝔤) :=
  Module.Finite.equiv (valLinEquiv 𝔤).symm

/-!

### A.2. The Lorentz action on the target space

-/

open Matrix MatrixGroups

variable (𝔤) in
/-- The Lorentz action on the gauge-boson target space: the covector action on the
  spacetime index, and the trivial action on the gauge-algebra factor. -/
noncomputable def repLorentzGroup : Representation ℝ SL(2,ℂ) (GaugeBoson 𝔤) where
  toFun Λ := (valLinEquiv 𝔤).symm.toLinearMap ∘ₗ
    TensorProduct.map (Lorentz.CoVector.sl2Rep Λ) LinearMap.id ∘ₗ
    (valLinEquiv 𝔤).toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [Module.End.one_eq_id]
  map_mul' Λ₁ Λ₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.End.mul_apply, LinearEquiv.apply_symm_apply, map_mul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
    rfl

/-!

### A.3. The global gauge action on the target space

-/

/-- The global gauge action on the gauge-boson target space: the adjoint action on the
  gauge-algebra factor, and the trivial action on the spacetime index. -/
noncomputable def repValue {G₀ : Type} [Monoid G₀] (ρ : Representation ℝ G₀ 𝔤) :
    Representation ℝ G₀ (GaugeBoson 𝔤) where
  toFun g := (valLinEquiv 𝔤).symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (ρ g) ∘ₗ
    (valLinEquiv 𝔤).toLinearMap
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [Module.End.one_eq_id]
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.End.mul_apply, LinearEquiv.apply_symm_apply, map_mul]
    congr 1
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp]
    rfl

/-!

## B. The jet component space

-/

variable (𝔤) in
/-- The jet component space of the gauge-boson field: the span of the component functions
  `∂_s A_μ^φ`. The `SpaceTimeDerivAlgebraℝ` factor carries the derivative label `s`, and the
  dual factor the spacetime and adjoint indices — the latter as an abstract covector on
  the gauge algebra, with no basis chosen. Unlike a matter field, the gauge boson is real,
  so there is no conjugate half. -/
abbrev JetComponentSpace : Type :=
  SpaceTimeDerivAlgebraℝ ⊗[ℝ] Module.Dual ℝ (GaugeBoson 𝔤)

/-!

### B.1. The component covectors

-/

variable (𝔤) in
/-- The covector on the gauge-boson target space pairing the spacetime index against a
  covector `ω` and the adjoint index against `φ`. -/
noncomputable def componentDual :
    Module.Dual ℝ Lorentz.CoVector →ₗ[ℝ]
      Module.Dual ℝ 𝔤 →ₗ[ℝ] Module.Dual ℝ (GaugeBoson 𝔤) where
  toFun ω := (Module.Dual.transpose (M := (GaugeBoson 𝔤)) (valLinEquiv 𝔤).toLinearMap).comp
    ((TensorProduct.dualDistrib ℝ Lorentz.CoVector 𝔤).comp
      (TensorProduct.mk ℝ (Module.Dual ℝ Lorentz.CoVector) (Module.Dual ℝ 𝔤) ω))
  map_add' ω₁ ω₂ := by
    refine LinearMap.ext fun φ => ?_
    simp
  map_smul' r ω := by
    refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      RingHom.id_apply, LinearMap.smul_apply]
    rw [← TensorProduct.smul_tmul', map_smul, map_smul]

@[simp]
lemma componentDual_apply_val_tmul (ω : Module.Dual ℝ Lorentz.CoVector)
    (φ : Module.Dual ℝ 𝔤) (v : Lorentz.CoVector) (a : 𝔤) :
    (componentDual 𝔤) ω φ ⟨v ⊗ₜ[ℝ] a⟩ = ω v * φ a := by
  simp [componentDual, Module.Dual.transpose_apply]

variable (𝔤) in
/-- **The component covector** of `A_μ^a`, a real linear functional on the values
  `CoVector ⊗ 𝔤` of the gauge potential. It selects the `μ`-th spacetime component and pairs the
  gauge-algebra value with the covector `a`. -/
noncomputable abbrev componentCovector (μ : Fin 1 ⊕ Fin 3) (a : Module.Dual ℝ 𝔤) :
    Module.Dual ℝ (GaugeBoson 𝔤) :=
  componentDual 𝔤 (Lorentz.CoVector.basis.dualBasis μ) a

/-- The contragredient Lorentz action passes through a component covector to its spacetime
  slot: the adjoint index is Lorentz-inert. -/
lemma repLorentzGroup_dual_componentDual (Λ : SL(2,ℂ))
    (ω : Module.Dual ℝ Lorentz.CoVector) (φ : Module.Dual ℝ 𝔤) :
    (GaugeBoson.repLorentzGroup 𝔤).dual Λ ((GaugeBoson.componentDual 𝔤) ω φ)
      = (GaugeBoson.componentDual 𝔤) (Lorentz.CoVector.sl2Rep.dual Λ ω) φ := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m⟩ := v
  induction m using TensorProduct.inductionOn with
  | tmul x a =>
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
      show (GaugeBoson.repLorentzGroup 𝔤) Λ⁻¹ (⟨x ⊗ₜ[ℝ] a⟩ : (GaugeBoson 𝔤))
        = ⟨(Lorentz.CoVector.sl2Rep Λ⁻¹ x) ⊗ₜ[ℝ] a⟩ from rfl,
      GaugeBoson.componentDual_apply_val_tmul, GaugeBoson.componentDual_apply_val_tmul,
      Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : (GaugeBoson 𝔤)) = (⟨m₁⟩ : (GaugeBoson 𝔤)) + ⟨m₂⟩ from rfl, map_add,
      map_add, h₁, h₂]

/-- **The component covectors transform as a Lorentz covector**. Under the contragredient
  action `A_μ^a` mixes into the `A_b^a` by the columns of the Lorentz matrix, with the adjoint
  index fixed. -/
lemma repLorentzGroup_dual_componentCovector (Λ : SL(2,ℂ)) (μ : Fin 1 ⊕ Fin 3)
    (a : Module.Dual ℝ 𝔤) :
    (repLorentzGroup 𝔤).dual Λ (componentCovector 𝔤 μ a)
      = ∑ b, (Lorentz.SL2C.toLorentzGroup Λ).1 b μ • componentCovector 𝔤 b a := by
  rw [repLorentzGroup_dual_componentDual, Lorentz.CoVector.sl2Rep_dual_dualBasis, map_sum,
    LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun b _ => by rw [map_smul, LinearMap.smul_apply]

end GaugeBoson
