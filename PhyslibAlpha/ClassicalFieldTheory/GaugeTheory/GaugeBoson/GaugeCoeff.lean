/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.GaugeBoson.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.AdjointCoeff
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalGaugeData.MaurerCartan
public import PhyslibAlpha.Mathematics.MultisetAntidiagonal

/-!
# The gauge-transformation coefficients of the gauge field

The adjoint transport and Maurer–Cartan coefficients of the gauge field and their composition laws.

## i. Overview

A jet of gauge transformations `U` acts on the gauge field by
`A_μ ↦ Ad_U A_μ + maurerCartan(U)_μ`. On the base-point derivative values of the field, with no
division by factorials, this action is a linear part plus an additive term independent of the
gauge field, both valued in the gauge-boson target space `CoVector ⊗ 𝔤`. The linear part is the
adjoint transport `GaugeBoson.adjointTransport`, and the additive term is the Maurer–Cartan
coefficient `LocalGaugeFieldAlgebra.mcBosonCoeff`.

This file holds these coefficients and their composition laws. They are used to build the gauge
action on the algebra of the gauge field.

## ii. Key results

- `GaugeBoson.adjointTransport` : the adjoint derivative coefficients on the target space.
- `GaugeBoson.adjointTransport_mul`, `GaugeBoson.adjointTransport_one` : its composition laws.
- `LocalGaugeFieldAlgebra.mcBosonCoeff` : the Maurer–Cartan derivative coefficients as gauge
  bosons.
- `LocalGaugeFieldAlgebra.mcBosonCoeff_mul` : the cocycle identity.
- `LocalGaugeFieldAlgebra.mcBosonCoeff_one` : the identity has no Maurer–Cartan term.
- `GaugeBoson.dualMap_adjointTransport_componentDual`,
  `LocalGaugeFieldAlgebra.componentDual_dualBasis_mcBosonCoeff` : both coefficients read in
  components.

## iii. Table of contents

- A. The adjoint transport
- B. The Maurer–Cartan coefficients

## iv. References

* None.

-/

@[expose] public section

variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

open TensorProduct MvPowerSeries

/-!

## A. The adjoint transport

At the derivative multiset `p`, the adjoint transport applies the adjoint derivative coefficient
`LocalGaugeData.adjointCoeff` to the gauge-algebra factor and the identity to the spacetime index.
The transport of a product is a Leibniz convolution of the transports of the factors, the sum over
all ways of distributing the derivative directions between the two factors (the splits in
`Multiset.antidiagonal`), with the multiplicities prescribed by the Leibniz rule.

-/

namespace GaugeBoson

variable (jets) in
/-- The adjoint transport on the gauge-boson target space at the derivative multiset `p`. -/
noncomputable def adjointTransport (U : GJ) (p : Multiset (Fin 1 ⊕ Fin 3)) :
    (GaugeBoson 𝔤) →ₗ[ℝ] (GaugeBoson 𝔤) :=
  (valLinEquiv 𝔤).symm.toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (jets.adjointCoeff U p) ∘ₗ
    (valLinEquiv 𝔤).toLinearMap

lemma adjointTransport_mk_tmul (U : GJ) (p : Multiset (Fin 1 ⊕ Fin 3))
    (v : Lorentz.CoVector) (a : 𝔤) :
    adjointTransport jets U p ⟨v ⊗ₜ[ℝ] a⟩ = ⟨v ⊗ₜ[ℝ] jets.adjointCoeff U p a⟩ := rfl

/-- At the identity the zeroth adjoint transport is the identity and the higher derivative
  transports vanish. -/
lemma adjointTransport_one (p : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointTransport jets 1 p = if p = 0 then LinearMap.id else 0 := by
  rw [adjointTransport, jets.adjointCoeff_one]
  rcases eq_or_ne p 0 with rfl | hp
  · rw [ite_eq_left rfl, ite_eq_left rfl, TensorProduct.map_id]
    refine LinearMap.ext fun v => ?_
    simp
  · rw [ite_eq_right hp, ite_eq_right hp]
    refine LinearMap.ext fun v => ?_
    rw [show TensorProduct.map (LinearMap.id (M := Lorentz.CoVector))
        (0 : 𝔤 →ₗ[ℝ] 𝔤) = 0 from by
      refine TensorProduct.ext' fun x a => ?_
      rw [TensorProduct.map_tmul, LinearMap.zero_apply, TensorProduct.tmul_zero]
      rfl]
    simp

/-- The adjoint transport of a product is the Leibniz convolution of the transports. -/
lemma adjointTransport_mul (U V : GJ) (p : Multiset (Fin 1 ⊕ Fin 3)) :
    adjointTransport jets (U * V) p
      = (p.antidiagonal.map fun r =>
          adjointTransport jets U r.1 ∘ₗ adjointTransport jets V r.2).sum := by
  refine LinearMap.ext fun v => ?_
  rw [Multiset.sum_linearMap_apply, Multiset.map_map]
  obtain ⟨m⟩ := v
  induction m using TensorProduct.inductionOn with
  | tmul x a =>
    apply (valLinEquiv 𝔤).injective
    rw [adjointTransport_mk_tmul, map_multiset_sum, Multiset.map_map, valLinEquiv_apply,
      show ((⟨x ⊗ₜ[ℝ] jets.adjointCoeff (U * V) p a⟩ : (GaugeBoson 𝔤))).val
        = x ⊗ₜ[ℝ] jets.adjointCoeff (U * V) p a from rfl,
      jets.adjointCoeff_mul, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.tmul_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.comp_apply, adjointTransport_mk_tmul,
      valLinEquiv_apply]
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : (GaugeBoson 𝔤)) = (⟨m₁⟩ : (GaugeBoson 𝔤)) + ⟨m₂⟩ from rfl, map_add, h₁,
      h₂, ← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
    exact (map_add _ _ _).symm

/-- The dual transport moves the adjoint index of a component covector and fixes its spacetime
  index. -/
lemma dualMap_adjointTransport_componentDual (U : GJ)
    (p : Multiset (Fin 1 ⊕ Fin 3)) (ω : Module.Dual ℝ Lorentz.CoVector)
    (φ : Module.Dual ℝ 𝔤) :
    (adjointTransport jets U p).dualMap ((componentDual 𝔤) ω φ)
      = (componentDual 𝔤) ω (φ ∘ₗ jets.adjointCoeff U p) := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m⟩ := v
  induction m using TensorProduct.inductionOn with
  | tmul x a =>
    rw [LinearMap.dualMap_apply, adjointTransport_mk_tmul,
      componentDual_apply_val_tmul, componentDual_apply_val_tmul]
    rfl
  | add m₁ m₂ h₁ h₂ =>
    rw [show (⟨m₁ + m₂⟩ : (GaugeBoson 𝔤)) = (⟨m₁⟩ : (GaugeBoson 𝔤)) + ⟨m₂⟩ from rfl, map_add,
      map_add, h₁, h₂]

end GaugeBoson

/-!

## B. The Maurer–Cartan coefficients

-/

namespace LocalGaugeFieldAlgebra

variable (jets) in
/-- The derivative coefficient of the Maurer–Cartan form of `U` at the derivative multiset `s`,
  valued in the gauge-field value space `CoVector ⊗ 𝔤`. -/
noncomputable def mcBosonCoeff (U : GJ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    (GaugeBoson 𝔤) :=
  ⟨∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
    jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ))⟩

/-- The identity has no Maurer–Cartan term. -/
@[simp]
lemma mcBosonCoeff_one (s : Multiset (Fin 1 ⊕ Fin 3)) : mcBosonCoeff jets 1 s = 0 := by
  rw [show (0 : (GaugeBoson 𝔤)) = ⟨0⟩ from rfl, mcBosonCoeff]
  congr 1
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [show jets.maurerCartan 1 μ = 0 from jets.maurerCartan_one μ, map_zero,
    map_zero, TensorProduct.tmul_zero]

/-- The Maurer–Cartan coefficients satisfy the cocycle identity, those of the second factor of a
  product being transported by the first. -/
lemma mcBosonCoeff_mul (U V : GJ) (s : Multiset (Fin 1 ⊕ Fin 3)) :
    mcBosonCoeff jets (U * V) s
      = mcBosonCoeff jets U s
        + (s.antidiagonal.map fun p =>
            GaugeBoson.adjointTransport jets U p.1 (mcBosonCoeff jets V p.2)).sum := by
  apply (GaugeBoson.valLinEquiv 𝔤).injective
  have hE : ∀ (W : GJ) (t : Multiset (Fin 1 ⊕ Fin 3)),
      (GaugeBoson.valLinEquiv 𝔤) (mcBosonCoeff jets W t)
        = ∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
            jets.evalLie (jets.iteratedDeriv t
              (jets.maurerCartan W μ)) := fun W t => rfl
  have hB : ∀ p q : Multiset (Fin 1 ⊕ Fin 3),
      (GaugeBoson.valLinEquiv 𝔤) (GaugeBoson.adjointTransport jets U p (mcBosonCoeff jets V q))
        = ∑ μ, Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
            jets.adjointCoeff U p (jets.evalLie
              (jets.iteratedDeriv q (jets.maurerCartan V μ))) := by
    intro p q
    rw [show (GaugeBoson.valLinEquiv 𝔤) (GaugeBoson.adjointTransport jets U p
      (mcBosonCoeff jets V q))
        = TensorProduct.map LinearMap.id (jets.adjointCoeff U p)
            ((GaugeBoson.valLinEquiv 𝔤) (mcBosonCoeff jets V q)) from by
        rw [GaugeBoson.adjointTransport]
        simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearEquiv.apply_symm_apply],
      hE, map_sum]
    exact Finset.sum_congr rfl fun μ _ => by
      rw [TensorProduct.map_tmul, LinearMap.id_apply]
  have hA : (GaugeBoson.valLinEquiv 𝔤) (mcBosonCoeff jets (U * V) s)
      = ∑ μ, (Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
          jets.evalLie (jets.iteratedDeriv s (jets.maurerCartan U μ))
        + (s.antidiagonal.map fun p =>
            Lorentz.CoVector.basis μ ⊗ₜ[ℝ]
              jets.adjointCoeff U p.1 (jets.evalLie
                (jets.iteratedDeriv p.2 (jets.maurerCartan V μ)))).sum) := by
    rw [hE]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [show jets.maurerCartan (U * V) μ
        = jets.maurerCartan U μ + jets.adjointJ U (jets.maurerCartan V μ) from
        jets.maurerCartan_cocycle U V μ,
      map_add, map_add,
      show jets.adjointJ U (jets.maurerCartan V μ)
        = jets.adjointJ U (jets.maurerCartan V μ) from rfl,
      jets.evalLie_iteratedDeriv_adjointJ, TensorProduct.tmul_add,
      Multiset.tmul_sum, Multiset.map_map]
    exact congrArg (fun z => _ + z)
      (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => rfl))
  rw [hA, Finset.sum_add_distrib, map_add, map_multiset_sum, Multiset.map_map, ← hE,
    ← Multiset.sum_map_finsetSum]
  congr 1

/-- The component covector at `μ` picks out the `μ`-th component of `mcBosonCoeff`. -/
lemma componentDual_dualBasis_mcBosonCoeff (W : GJ)
    (s : Multiset (Fin 1 ⊕ Fin 3)) (μ : Fin 1 ⊕ Fin 3) (φ : Module.Dual ℝ 𝔤) :
    (GaugeBoson.componentDual 𝔤) (Lorentz.CoVector.basis.dualBasis μ) φ (mcBosonCoeff jets W s)
      = φ (jets.evalLie (jets.iteratedDeriv s
          (jets.maurerCartan W μ))) := by
  have hsum : mcBosonCoeff jets W s
      = ∑ ν, (⟨Lorentz.CoVector.basis ν ⊗ₜ[ℝ]
          jets.evalLie (jets.iteratedDeriv s
            (jets.maurerCartan W ν))⟩ : (GaugeBoson 𝔤)) := by
    apply (GaugeBoson.valLinEquiv 𝔤).injective
    rw [map_sum]
    rfl
  rw [hsum, map_sum]
  rw [Finset.sum_congr rfl fun ν _ => GaugeBoson.componentDual_apply_val_tmul _ _ _ _]
  rw [Finset.sum_congr rfl fun ν _ => by
    rw [Module.Basis.dualBasis_apply_self, ite_mul, one_mul, zero_mul]]
  rw [Finset.sum_ite_eq' Finset.univ μ
    (fun ν => φ (jets.evalLie (jets.iteratedDeriv s
      (jets.maurerCartan W ν)))), ite_eq_left (Finset.mem_univ μ)]

end LocalGaugeFieldAlgebra
