/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction.Basic
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.CovariantDeriv
/-!
# The covariant derivative preserves the gauge tensors of a representation

## i. Overview

The covariant derivative `∇_ρ F = [∂_ρ F] + A_ρ · F` of a matter family is built from
an action `act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V` of the gauge algebra on the value space. For the
covariant derivative to transform covariantly, `act` must be the *infinitesimal action*
underlying the representation `rep` of the jet gauge group in which the family
transforms, `IsInfinitesimalActionOf` of
`PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.InfinitesimalAction.Basic`. This
file proves that under this compatibility, against a realization of the gauge field, the
covariant derivative preserves the gauge tensors, `TransformsIn.covDerivAction`.

Everything is stated over a supplied local-gauge-data package
`jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J`; nothing depends on the Standard Model choice of it.

## ii. Key results

- `LocalGaugeData.TransformsIn.covDerivAction` : the covariant derivative preserves
  `TransformsIn`.
- `LocalGaugeData.TransformsIn.covDerivIter` : so does every iterated covariant
  derivative.

## iii. Table of contents

- A. The covariant derivative preserves `TransformsIn`

## iv. References

* None.

-/

@[expose] public section

set_option linter.unusedSectionVars false

open Matrix MatrixGroups TensorProduct MvPowerSeries

variable {B : Type} [Ring B] [Algebra ℂ B]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [Module.Finite ℝ 𝔤]
variable {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

namespace LocalGaugeData

open GaugeAlgebraRealization

variable {repLorentz : Representation ℂ SL(2,ℂ) B}
variable {repGauge : Representation ℂ GJ B}
variable {A : Multiset (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → Module.Dual ℝ 𝔤 →ₗ[ℝ] B}
variable (h : GaugeAlgebraRealization jets B repGauge repLorentz)

/-!

## A. The covariant derivative preserves `TransformsIn`

-/

section MatterCovariance

variable {rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V)}
variable {act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V}
variable [FiniteDimensional ℂ V]

/-- The action of families against the dual representation coefficients: the
  antidiagonal convolution mixing the adjoint transport on the field slot with the
  representation transport on the matter slot — the family-level form of
  `IsInfinitesimalActionOf.repCoeff_act`, and the analogue of
  `bracketFam_adjointDualCoeff`. -/
lemma IsInfinitesimalActionOf.actionFam_repDualCoeff
    (h : IsInfinitesimalActionOf jets act rep) (U : GJ)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (f : Module.Dual ℝ 𝔤 →ₗ[ℝ] B)
    (g : Module.Dual ℂ V →ₗ[ℂ] B) (φ : Module.Dual ℂ V) :
    actionFam act f g (repDualCoeff rep U x φ) =
      (x.antidiagonal.map fun p =>
        actionFam act (f ∘ₗ jets.adjointDualCoeff U p.1)
          (g ∘ₗ repDualCoeff rep U p.2) φ).sum := by
  have hT : ∀ (c : 𝔤) (v : V), repCoeff rep U x (act c v) =
      (x.antidiagonal.map fun p =>
        act (jets.adjointCoeff U p.1 c) (repCoeff rep U p.2 v)).sum := by
    intro c v
    have h1 := LinearMap.congr_fun (h.repCoeff_act U x c) v
    simpa [Multiset.sum_linearMap_apply, Multiset.map_map, LinearMap.coe_comp,
      Function.comp_apply] using h1
  rw [show repDualCoeff rep U x = (repCoeff rep U x).dualMap from rfl,
    show actionFam act f g ((repCoeff rep U x).dualMap φ) =
      dualPairEquivC ((TensorProduct.map LinearMap.id (repCoeff rep U x))
        (tensorAction act (dualPairEquiv.symm f) (dualPairEquivC.symm g))) φ from
      (dualPairEquivC_map_right (repCoeff rep U x) _ φ).symm,
    ← tensorAction_map_right_antidiagonal act (jets.adjointCoeff U) (repCoeff rep U) x hT,
    map_multiset_sum, Multiset.map_map, Multiset.sum_linearMap_apply, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
  simp only [Function.comp_apply]
  rw [← symm_comp_right, ← symm_comp_right_C]
  rfl

omit [FiniteDimensional ℂ V] in
omit [Module.Finite ℝ 𝔤] in
/-- If `F` transforms in `rep`, so do its `κ ::ₘ s`-derived symbols, with the extra
  derivative traced through `IsInfinitesimalActionOf.repDualCoeff_cons`: the Leibniz
  splittings where `κ` stays a derivative, minus the convolution where `κ` hits the
  representation — `act` of the derived Maurer–Cartan form. -/
lemma TransformsIn.repGauge_cons
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : TransformsIn repGauge rep F)
    (hact : IsInfinitesimalActionOf jets act rep)
    (U : GJ) (κ : Fin 1 ⊕ Fin 3) (s : Multiset (Fin 1 ⊕ Fin 3))
    (φ : Module.Dual ℂ V) :
    repGauge U (F (κ ::ₘ s) φ) =
      (s.antidiagonal.map fun p =>
        F (κ ::ₘ p.2) (repDualCoeff rep U⁻¹ p.1 φ)).sum
      - (s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            F p.2 (repDualCoeff rep U⁻¹ q.2
              (φ ∘ₗ act (jets.evalLie (jets.iteratedDeriv q.1
                (jets.maurerCartan U⁻¹ κ)))))).sum).sum := by
  rw [hF U φ (κ ::ₘ s)]
  simp only [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add,
    Multiset.map_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
  have hsec : (Multiset.map (fun p =>
        F p.2 (repDualCoeff rep U⁻¹ (κ ::ₘ p.1) φ)) s.antidiagonal).sum =
      -(s.antidiagonal.map fun p =>
          (p.1.antidiagonal.map fun q =>
            F p.2 (repDualCoeff rep U⁻¹ q.2
              (φ ∘ₗ act (jets.evalLie (jets.iteratedDeriv q.1
                (jets.maurerCartan U⁻¹ κ)))))).sum).sum := by
    rw [← Multiset.sum_map_neg'']
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [hact.repDualCoeff_cons U⁻¹ κ p.1 φ, map_neg, map_multiset_sum, Multiset.map_map]
    exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => rfl))
  rw [hsec, sub_eq_add_neg]

set_option maxHeartbeats 2000000 in
/-- The all-orders gauge transformation of the derived action `A_ρ · F` for `F`
  transforming in `rep`: since `F` transforms homogeneously, only one cross-term
  convolution through `act` survives — the analogue of
  `TransformsInAdjoint.repGauge_bracketFamConv` with a matter field in the second
  slot. -/
lemma TransformsIn.repGauge_actionFamConv
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : TransformsIn repGauge rep F)
    (hact : IsInfinitesimalActionOf jets act rep)
    (U : GJ) (s : Multiset (Fin 1 ⊕ Fin 3)) (ρ : Fin 1 ⊕ Fin 3)
    (φ : Module.Dual ℂ V) :
    repGauge U (actionFamConv h.A act ρ F s φ) =
      (s.antidiagonal.map fun p =>
        actionFamConv h.A act ρ F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
          (p.2.antidiagonal.map fun r =>
            F r.2 (repDualCoeff rep U⁻¹ r.1
              (φ ∘ₗ act (jets.evalLie (jets.iteratedDeriv p.1
                (jets.maurerCartan U⁻¹ ρ)))))).sum).sum := by
  have hAlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℝ 𝔤),
      repGauge U (h.A u ρ ψ) =
        ((u.antidiagonal.map fun q => h.A q.2 ρ ∘ₗ jets.adjointDualCoeff U⁻¹ q.1).sum) ψ
        + algebraMap ℂ B (ψ (jets.evalLie
            (jets.iteratedDeriv u (jets.maurerCartan U⁻¹ ρ)))) := by
    intro u ψ
    rw [h.gauge_apply_deriv U u ρ ψ, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  have hFlaw : ∀ (u : Multiset (Fin 1 ⊕ Fin 3)) (ψ : Module.Dual ℂ V),
      repGauge U (F u ψ) =
        ((u.antidiagonal.map fun r => F r.2 ∘ₗ repDualCoeff rep U⁻¹ r.1).sum) ψ := by
    intro u ψ
    rw [hF U ψ u, Multiset.sum_linearMap_apply, Multiset.map_map]
    congr 1
  have hMa : (s.antidiagonal.map fun p =>
      actionFam act ((p.1.antidiagonal.map fun q =>
          h.A q.2 ρ ∘ₗ jets.adjointDualCoeff U⁻¹ q.1).sum)
        ((p.2.antidiagonal.map fun r =>
          F r.2 ∘ₗ repDualCoeff rep U⁻¹ r.1).sum) φ).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            actionFam act (h.A q.2 ρ ∘ₗ jets.adjointDualCoeff U⁻¹ q.1)
              (F r.2 ∘ₗ repDualCoeff rep U⁻¹ r.1) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [actionFam_sum_left, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun q hq => ?_)
    simp only [Function.comp_apply]
    rw [actionFam_sum_right, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply]
  have hMc : (s.antidiagonal.map fun p =>
      actionFamConv h.A act ρ F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        (p.1.antidiagonal.map fun q =>
          (p.2.antidiagonal.map fun r =>
            actionFam act (h.A r.1 ρ ∘ₗ jets.adjointDualCoeff U⁻¹ q.1)
              (F r.2 ∘ₗ repDualCoeff rep U⁻¹ q.2) φ).sum).sum).sum := by
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map,
      Multiset.map_congr rfl (fun r hr => by
        rw [Function.comp_apply,
          hact.actionFam_repDualCoeff U⁻¹ p.1 (h.A r.1 ρ) (F r.2) φ]),
      Multiset.sum_map_sum_map]
  have hM := hMa.trans ((Multiset.sum_antidiagonal_exchange s fun a b c d =>
      actionFam act (h.A b ρ ∘ₗ jets.adjointDualCoeff U⁻¹ a)
        (F d ∘ₗ repDualCoeff rep U⁻¹ c) φ).trans hMc.symm)
  have hCg : ∀ p : Multiset (Fin 1 ⊕ Fin 3) × Multiset (Fin 1 ⊕ Fin 3),
      ((p.2.antidiagonal.map fun r => F r.2 ∘ₗ repDualCoeff rep U⁻¹ r.1).sum)
        (φ ∘ₗ act (jets.evalLie
          (jets.iteratedDeriv p.1 (jets.maurerCartan U⁻¹ ρ)))) =
      (p.2.antidiagonal.map fun r =>
        F r.2 (repDualCoeff rep U⁻¹ r.1
          (φ ∘ₗ act (jets.evalLie (jets.iteratedDeriv p.1
            (jets.maurerCartan U⁻¹ ρ)))))).sum := by
    intro p
    rw [Multiset.sum_linearMap_apply, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun r hr => ?_)
    simp only [Function.comp_apply, LinearMap.coe_comp]
  rw [actionFamConv, Multiset.sum_linearMap_apply, Multiset.map_map, map_multiset_sum,
    Multiset.map_map,
    Multiset.map_congr rfl (fun p hp => by
      rw [Function.comp_apply, Function.comp_apply,
        repGauge_actionFam h U (hAlaw p.1) (hFlaw p.2) φ, hCg p]),
    Multiset.sum_map_add, hM]

set_option maxHeartbeats 2000000 in
/-- The covariant derivative preserves `TransformsIn`: if `F` transforms in the
  representation `rep` and `act` is the infinitesimal action underlying `rep`, then
  `∇_ρ F = [∂_ρ F] + A_ρ · F` transforms in `rep`. The single inhomogeneous
  convolution of `[∂_{ρ ::ₘ s} F]` cancels the single `act` cross-term convolution of
  `A_ρ · F` through the coassociativity of the antidiagonal — the matter-field
  analogue of `TransformsInAdjoint.covDerivAdjoint`. -/
lemma TransformsIn.covDerivAction
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : TransformsIn repGauge rep F)
    (hact : IsInfinitesimalActionOf jets act rep) (ρ : Fin 1 ⊕ Fin 3) :
    TransformsIn repGauge rep (GaugeAlgebraRealization.covDerivAction h.A act F ρ) := by
  intro U φ s
  have hL : repGauge U (GaugeAlgebraRealization.covDerivAction h.A act F ρ s φ) =
      repGauge U (F (ρ ::ₘ s) φ) + repGauge U (actionFamConv h.A act ρ F s φ) := by
    rw [GaugeAlgebraRealization.covDerivAction_apply, map_add]
  have hR : (s.antidiagonal.map fun p =>
      GaugeAlgebraRealization.covDerivAction h.A act F ρ p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum =
      (s.antidiagonal.map fun p =>
        F (ρ ::ₘ p.2) (repDualCoeff rep U⁻¹ p.1 φ)).sum
      + (s.antidiagonal.map fun p =>
        actionFamConv h.A act ρ F p.2 (repDualCoeff rep U⁻¹ p.1 φ)).sum := by
    rw [← Multiset.sum_map_add]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [GaugeAlgebraRealization.covDerivAction_apply]
  have hcancel : (s.antidiagonal.map fun p =>
      (p.1.antidiagonal.map fun q =>
        F p.2 (repDualCoeff rep U⁻¹ q.2
          (φ ∘ₗ act (jets.evalLie (jets.iteratedDeriv q.1
            (jets.maurerCartan U⁻¹ ρ)))))).sum).sum =
    (s.antidiagonal.map fun p =>
      (p.2.antidiagonal.map fun r =>
        F r.2 (repDualCoeff rep U⁻¹ r.1
          (φ ∘ₗ act (jets.evalLie (jets.iteratedDeriv p.1
            (jets.maurerCartan U⁻¹ ρ)))))).sum).sum :=
    Multiset.sum_antidiagonal_assoc s (fun a b c =>
      F c (repDualCoeff rep U⁻¹ b
        (φ ∘ₗ act (jets.evalLie (jets.iteratedDeriv a
          (jets.maurerCartan U⁻¹ ρ))))))
  rw [hL, hF.repGauge_cons hact U ρ s φ, hF.repGauge_actionFamConv h hact U s ρ φ,
    hR, hcancel]
  abel

/-- Every iterated covariant derivative preserves `TransformsIn`: if `F` transforms
  in `rep` and `act` is the infinitesimal action underlying `rep`, then
  `∇_{l 0} ⋯ ∇_{l (n-1)} F` transforms in `rep` — the recursion of
  `TransformsIn.covDerivAction` over the tuple of directions. -/
lemma TransformsIn.covDerivIter
    {F : Multiset (Fin 1 ⊕ Fin 3) → Module.Dual ℂ V →ₗ[ℂ] B}
    (hF : TransformsIn repGauge rep F)
    (hact : IsInfinitesimalActionOf jets act rep)
    (n : ℕ) (l : Fin n → (Fin 1 ⊕ Fin 3)) :
    TransformsIn repGauge rep (GaugeAlgebraRealization.covDerivIter h.A act F n l) := by
  induction n with
  | zero => exact hF
  | succ n ih =>
      exact TransformsIn.covDerivAction h (ih fun i => l i.succ) hact (l 0)

end MatterCovariance

end LocalGaugeData
