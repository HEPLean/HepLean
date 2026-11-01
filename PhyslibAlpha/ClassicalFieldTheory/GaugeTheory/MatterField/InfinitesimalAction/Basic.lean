/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.MatterField.TransformsIn
public import PhyslibAlpha.ClassicalFieldTheory.GaugeTheory.LocalField.JetRep
/-!
# The infinitesimal action underlying a matter representation

The identities relating a gauge-algebra action to the matter representation it underlies.

## i. Overview

A matter field carries an action `act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V` of the gauge algebra on its value
space as well as the representation `rep` of the jet gauge group on its jets. The structure
`IsInfinitesimalActionOf` asks that `act` be the infinitesimal action underlying `rep`, in the
form of two identities relating `act` to the derivative coefficients `repCoeff` of `rep`. These
identities are used to prove the transformation law of the covariant derivative,
`LocalGaugeData.TransformsIn.covDerivAction`. This file also shows that they pass to the conjugate
field.

## ii. Key results

- `LocalGaugeData.IsInfinitesimalActionOf` : `act` is the infinitesimal action underlying
  `rep`.
- `LocalGaugeData.IsInfinitesimalActionOf.conj` : the conjugate action underlies the
  conjugate representation.
- `GaugeAlgebraRealization.actionConj_comm_repConj` : conjugation preserves the commutation of
  the gauge action with a Lorentz action.

## iii. Table of contents

- A. The infinitesimal action underlying a representation
- B. The conjugate action and the conjugate representation

## iv. References

* None.

-/

@[expose] public section

open Matrix MatrixGroups TensorProduct MvPowerSeries

section InfinitesimalAction

variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {G₀ : Type} [Group G₀] {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {GJ : Type} [Group GJ] {𝔤J : Type} [LieRing 𝔤J] [LieAlgebra ℝ 𝔤J]
variable {jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J}

namespace LocalGaugeData

open GaugeAlgebraRealization

/-!

## A. The infinitesimal action underlying a representation

The first of the two identities relates an additional derivative of the representation to its
infinitesimal action and the Maurer–Cartan form. The second says that applying the infinitesimal
action of `c` and then transforming by `U` agrees with transforming by `U` and then acting with
the transformed gauge-algebra input `Ad_U c`, whose derivative coefficients are
`adjointCoeff U p c`. In both identities the Leibniz rule distributes the derivative directions
between the two factors, as a sum over the splits in `Multiset.antidiagonal`.

`IsInfinitesimalActionOf` records these identities as assumptions. The following lemma gives the
first identity on the dual space, where the labels of matter-field symbols live.

-/

/-- `act` is the infinitesimal action underlying `rep`, through two identities for the derivative
  coefficients of `rep`. -/
structure IsInfinitesimalActionOf (jets : LocalGaugeData G₀ 𝔤 GJ 𝔤J)
    (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V)
    (rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V)) : Prop where
  /-- The derivative coefficients satisfy the Leibniz identity determined by the Maurer–Cartan
    form. -/
  repCoeff_cons : ∀ (U : GJ) (μ : Fin 1 ⊕ Fin 3) (x : Multiset (Fin 1 ⊕ Fin 3)),
    repCoeff rep U (μ ::ₘ x) =
      -((x.antidiagonal.map fun p =>
        act (jets.evalLie (jets.iteratedDeriv p.1 (jets.maurerCartan U μ))) ∘ₗ
          repCoeff rep U p.2).sum)
  /-- The derivative coefficients of `rep U` intertwine `act` with the adjoint coefficients of
    `U`. -/
  repCoeff_act : ∀ (U : GJ) (x : Multiset (Fin 1 ⊕ Fin 3)) (c : 𝔤),
    repCoeff rep U x ∘ₗ act c =
      ((x.antidiagonal.map fun p =>
        act (jets.adjointCoeff U p.1 c) ∘ₗ repCoeff rep U p.2).sum)

/-- The dual coefficients `repDualCoeff` satisfy the Leibniz identity determined by the
  Maurer–Cartan form. -/
lemma IsInfinitesimalActionOf.repDualCoeff_cons
    {act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V}
    {rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V)}
    (h : IsInfinitesimalActionOf jets act rep) (U : GJ) (μ : Fin 1 ⊕ Fin 3)
    (x : Multiset (Fin 1 ⊕ Fin 3)) (φ : Module.Dual ℂ V) :
    repDualCoeff rep U (μ ::ₘ x) φ =
      -((x.antidiagonal.map fun p =>
        repDualCoeff rep U p.2 (φ ∘ₗ act (jets.evalLie
          (jets.iteratedDeriv p.1 (jets.maurerCartan U μ))))).sum) := by
  refine LinearMap.ext fun v => ?_
  have h1 := LinearMap.congr_fun (h.repCoeff_cons U μ x) v
  simp only [LinearMap.neg_apply, Multiset.sum_linearMap_apply, Multiset.map_map,
    Function.comp_apply, LinearMap.coe_comp] at h1
  simp only [repDualCoeff, LinearMap.dualMap_apply, LinearMap.neg_apply,
    Multiset.sum_linearMap_apply, Multiset.map_map, Function.comp_apply,
    LinearMap.coe_comp]
  rw [h1, map_neg, map_multiset_sum, Multiset.map_map]
  exact congrArg Neg.neg (congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => rfl))

/-!

## B. The conjugate action and the conjugate representation

A conjugate field takes values in the conjugate module `ConjModule V`, the same additive group as
`V` with complex scalar multiplication conjugated, and transforms in the conjugate
representation. Its infinitesimal action consists of the same maps, which remain complex-linear
for the conjugated scalars. The jets of the conjugate field are
identified with the conjugates of the jets by `conjJetEquiv`, which conjugates the jet-ring factor
by `star`. The derivative directions are real, so the derivative coefficients of the conjugate
representation are the conjugated coefficients, and both identities of `IsInfinitesimalActionOf`
pass to the conjugate. Conjugation also preserves the commutation of the infinitesimal action
with a Lorentz action.

-/

section ConjugateAction

/-- The conjugate of an infinitesimal action, the same maps on the conjugate module. -/
noncomputable def actionConj (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V) :
    𝔤 →ₗ[ℝ] ConjModule V →ₗ[ℂ] ConjModule V where
  toFun c := ConjModule.endConj (act c)
  map_add' c₁ c₂ := by rw [map_add, ConjModule.endConj_add]
  map_smul' r c := by rw [map_smul, ConjModule.endConj_real_smul, RingHom.id_apply]

@[simp]
lemma actionConj_apply (act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V) (c : 𝔤) :
    actionConj act c = ConjModule.endConj (act c) := rfl

/-- The identification of the conjugates of jets with the jets of the conjugate field, along which
  `JetComponentSpace.repConj` carries the conjugate representation. -/
noncomputable def conjJetEquiv :
    ConjModule (SpaceTimeAlgebra ⊗[ℂ] V) ≃ₗ[ℂ] SpaceTimeAlgebra ⊗[ℂ] ConjModule V :=
  (ConjModule.tensorEquiv (k := ℂ) (M := SpaceTimeAlgebra) (N := V)).symm.trans
    (TensorProduct.congr SpaceTimeAlgebra.starConjEquiv (LinearEquiv.refl ℂ (ConjModule V)))

lemma conjJetEquiv_conjEquiv_tmul (g : SpaceTimeAlgebra) (u : V) :
    conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) (g ⊗ₜ[ℂ] u))
      = star g ⊗ₜ[ℂ] conjEquiv (k := ℂ) (M := V) u := by
  rw [conjJetEquiv, LinearEquiv.trans_apply, ConjModule.tensorEquiv_symm_conjEquiv_tmul,
    TensorProduct.congr_tmul, SpaceTimeAlgebra.starConjEquiv_apply, LinearEquiv.refl_apply,
    LinearEquiv.symm_apply_apply]

section ConjugateRepresentation

variable {rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V)}
variable {act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V}

/-- The conjugate representation acts through `conjJetEquiv` by the original maps. -/
lemma repConj_conjJetEquiv (rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V))
    (U : GJ) (w : SpaceTimeAlgebra ⊗[ℂ] V) :
    JetComponentSpace.repConj rep U
        (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w))
      = conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) (rep U w)) := by
  show conjJetEquiv ((rep.conj U) (conjJetEquiv.symm
      (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w)))) = _
  rw [LinearEquiv.symm_apply_apply, Representation.conj_apply,
    LinearEquiv.symm_apply_apply]

/-- The derivative coefficients of the conjugate representation are the conjugated coefficients. -/
lemma repCoeff_repConj (rep : Representation ℂ GJ (SpaceTimeAlgebra ⊗[ℂ] V))
    (U : GJ) (x : Multiset (Fin 1 ⊕ Fin 3)) :
    repCoeff (JetComponentSpace.repConj rep) U x
      = ConjModule.endConj (repCoeff rep U x) := by
  have hE_tmul := conjJetEquiv_conjEquiv_tmul (V := V)
  -- conjugation intertwines the formal derivative
  have hderiv1 : ∀ (μ : Fin 1 ⊕ Fin 3) (w : SpaceTimeAlgebra ⊗[ℂ] V),
      jetDeriv μ (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w))
        = conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) (jetDeriv μ w)) := by
    intro μ w
    induction w using TensorProduct.inductionOn with
    | tmul g u =>
        rw [hE_tmul, jetDeriv_tmul, jetDeriv_tmul, hE_tmul, SpaceTimeAlgebra.pderiv_star]
    | add a b ha hb =>
        rw [map_add, map_add, map_add, ha, hb, map_add, map_add, map_add]
  have hderiv : ∀ (s : Multiset (Fin 1 ⊕ Fin 3)) (w : SpaceTimeAlgebra ⊗[ℂ] V),
      jetIteratedDeriv s (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w))
        = conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V)
            (jetIteratedDeriv s w)) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro w; rw [jetIteratedDeriv_zero]; rfl
    | cons μ t ih =>
        intro w
        rw [jetIteratedDeriv_cons, LinearMap.comp_apply, ih, hderiv1,
          jetIteratedDeriv_cons, LinearMap.comp_apply]
  -- conjugation intertwines the base-point evaluation
  have heval : ∀ w : SpaceTimeAlgebra ⊗[ℂ] V,
      jetEval (conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V) w))
        = conjEquiv (k := ℂ) (M := V) (jetEval w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul g u =>
        rw [hE_tmul, jetEval_tmul, jetEval_tmul, SpaceTimeAlgebra.constantCoeff_star,
          map_smulₛₗ, starRingEnd_apply]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add, map_add]
  refine LinearMap.ext fun v => ?_
  have hv : jetOfConstant v = conjJetEquiv (conjEquiv (k := ℂ) (M := SpaceTimeAlgebra ⊗[ℂ] V)
      (jetOfConstant ((conjEquiv (k := ℂ) (M := V)).symm v))) := by
    rw [jetOfConstant_apply, jetOfConstant_apply, hE_tmul, star_one,
      LinearEquiv.apply_symm_apply]
  show jetEval (jetIteratedDeriv x
    (JetComponentSpace.repConj rep U (jetOfConstant v))) = _
  rw [hv, repConj_conjJetEquiv, hderiv, heval]
  rfl

/-- If the zeroth derivative coefficient of `rep W` is the identity, so is that of its conjugate. -/
lemma repCoeff_repConj_zero_eq_id {W : GJ}
    (hrep : repCoeff rep W 0 = LinearMap.id) :
    repCoeff (JetComponentSpace.repConj rep) W 0 = LinearMap.id := by
  rw [repCoeff_repConj, hrep, ConjModule.endConj_id]

/-- The conjugate action is the infinitesimal action underlying the conjugate representation. -/
lemma IsInfinitesimalActionOf.conj (h : IsInfinitesimalActionOf jets act rep) :
    IsInfinitesimalActionOf jets (actionConj act) (JetComponentSpace.repConj rep) := by
  constructor
  · intro U μ x
    rw [repCoeff_repConj, h.repCoeff_cons U μ x, ConjModule.endConj_neg,
      ConjModule.endConj_multiset_sum, Multiset.map_map]
    refine congrArg Neg.neg (congrArg Multiset.sum
      (Multiset.map_congr rfl fun p hp => ?_))
    rw [Function.comp_apply, ConjModule.endConj_comp, repCoeff_repConj]
    rfl
  · intro U x c
    rw [repCoeff_repConj, show actionConj act c = ConjModule.endConj (act c) from rfl,
      ← ConjModule.endConj_comp, h.repCoeff_act U x c,
      ConjModule.endConj_multiset_sum, Multiset.map_map]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun p hp => ?_)
    rw [Function.comp_apply, ConjModule.endConj_comp, repCoeff_repConj]
    rfl

end ConjugateRepresentation

end ConjugateAction

end LocalGaugeData

end InfinitesimalAction

namespace GaugeAlgebraRealization

variable {𝔤 : Type} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable {act : 𝔤 →ₗ[ℝ] V →ₗ[ℂ] V}

/-- Conjugation preserves the commutation of the gauge action with a Lorentz action. -/
lemma actionConj_comm_repConj (rep : Representation ℂ SL(2,ℂ) V)
    (hcomm : ∀ (c : 𝔤) (Λ : SL(2,ℂ)) (v : V), act c (rep Λ v) = rep Λ (act c v))
    (c : 𝔤) (Λ : SL(2,ℂ)) (v : ConjModule V) :
    LocalGaugeData.actionConj act c (rep.conj Λ v) =
      rep.conj Λ (LocalGaugeData.actionConj act c v) :=
  congrArg (conjEquiv (k := ℂ) (M := V)) (hcomm c Λ _)

end GaugeAlgebraRealization
