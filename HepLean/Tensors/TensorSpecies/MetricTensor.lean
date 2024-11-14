/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.TensorSpecies.UnitTensor
import HepLean.Tensors.TensorSpecies.ContractLemmas
/-!

## Metrics in tensor trees

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin
open TensorProduct
noncomputable section

namespace TensorSpecies
open TensorTree

/-- The metric of a tensor species in a `PiTensorProduct`. -/
def metricTensor (S : TensorSpecies) (c : S.C) : S.F.obj (OverColor.mk ![c, c]) :=
  (OverColor.Discrete.pairIsoSep S.FD).hom.hom ((S.metric.app (Discrete.mk c)).hom (1 : S.k))

variable {S : TensorSpecies}

lemma pairIsoSep_inv_metricTensor (c : S.C) :
    (Discrete.pairIsoSep S.FD).inv.hom (S.metricTensor c) =
    (S.metric.app (Discrete.mk c)).hom (1 : S.k) := by
  simp [metricTensor]
  erw [Discrete.rep_iso_inv_hom_apply]

/-- Contraction of a metric tensor with a metric tensor gives the unit.
  Like `S.contr_metric` but with the braiding appearing on the side of the unit. -/
lemma contr_metric_braid_unit (c : S.C) :  (((S.FD.obj (Discrete.mk c)) ◁
    (λ_ (S.FD.obj (Discrete.mk (S.τ c)))).hom).hom
    (((S.FD.obj (Discrete.mk c)) ◁ ((S.contr.app (Discrete.mk c)) ▷
    (S.FD.obj (Discrete.mk (S.τ c))))).hom
    (((S.FD.obj (Discrete.mk c)) ◁ (α_ (S.FD.obj (Discrete.mk (c)))
      (S.FD.obj (Discrete.mk (S.τ c))) (S.FD.obj (Discrete.mk (S.τ c)))).inv).hom
    ((α_ (S.FD.obj (Discrete.mk (c))) (S.FD.obj (Discrete.mk (c)))
      (S.FD.obj (Discrete.mk (S.τ c)) ⊗ S.FD.obj (Discrete.mk (S.τ c)))).hom.hom
    (((OverColor.Discrete.pairIsoSep S.FD).inv.hom (S.metricTensor c) ⊗ₜ
    (OverColor.Discrete.pairIsoSep S.FD).inv.hom (S.metricTensor (S.τ c)))))))) =
    (β_ (S.FD.obj (Discrete.mk (S.τ c))) (S.FD.obj (Discrete.mk c))).hom.hom
      ((S.unit.app (Discrete.mk c)).hom (1 : S.k)) := by
  have hx : Function.Injective (β_ (S.FD.obj (Discrete.mk c)) (S.FD.obj (Discrete.mk (S.τ c))) ).hom.hom := by
    change  Function.Injective (β_ (S.FD.obj (Discrete.mk c)).V (S.FD.obj (Discrete.mk (S.τ c))).V ).hom
    exact (β_ (S.FD.obj (Discrete.mk c)).V (S.FD.obj (Discrete.mk (S.τ c))).V ).toLinearEquiv.toEquiv.injective
  apply hx
  rw [pairIsoSep_inv_metricTensor, pairIsoSep_inv_metricTensor]
  rw [S.contr_metric c]
  change  _ = (β_  (S.FD.obj { as := S.τ c }) (S.FD.obj { as := c })).inv.hom
    ((β_ (S.FD.obj { as := S.τ c }) (S.FD.obj { as := c })).hom.hom _)
  rw [Discrete.rep_iso_inv_hom_apply]

lemma metricTensor_contr_dual_metricTensor_perm_cond (c : S.C) : ∀ (x : Fin (Nat.succ 0).succ),
    ((Sum.elim ![c, c] ![S.τ c, S.τ c] ∘ ⇑finSumFinEquiv.symm) ∘ Fin.succAbove 1 ∘ Fin.succAbove 1) x =
    (![S.τ c, c] ∘ ⇑(finMapToEquiv ![1, 0] ![1, 0]).symm) x := by
  intro x
  fin_cases x
  · rfl
  · rfl

/-- The contraction of a metric tensor with its dual gives the unit. -/
lemma metricTensor_contr_dual_metricTensor_eq_unit (c : S.C) :
    {S.metricTensor c | μ ν ⊗ S.metricTensor (S.τ c) | ν ρ}ᵀ.tensor =
    (perm (OverColor.equivToHomEq (finMapToEquiv ![1, 0] ![1, 0])
      (metricTensor_contr_dual_metricTensor_perm_cond c)) {S.unitTensor c | μ ρ}ᵀ).tensor := by
  rw [contr_two_two_inner, contr_metric_braid_unit, Discrete.pairIsoSep_β]
  change (S.F.map _ ≫ S.F.map _ ).hom _ = _
  rw [← S.F.map_comp]
  rfl

end TensorSpecies

end
