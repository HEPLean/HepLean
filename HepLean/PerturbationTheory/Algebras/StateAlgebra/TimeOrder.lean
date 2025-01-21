/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.TimeOrder
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Time ordering on the state algebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
noncomputable section

namespace StateAlgebra

open FieldStatistic

/-- The linear map on the free state algebra defined as the map taking
  a list of states to the time-ordered list of states multiplied by
  the sign corresponding to the number of fermionic-fermionic
  exchanges done in ordering. -/
def timeOrder : StateAlgebra 𝓕 →ₗ[ℂ] StateAlgebra 𝓕 :=
  Basis.constr ofListBasis ℂ fun φs =>
  timeOrderSign φs • ofList (timeOrderList φs)

lemma timeOrder_ofList (φs : List 𝓕.States) :
    timeOrder (ofList φs) = timeOrderSign φs • ofList (timeOrderList φs) := by
  rw [← ofListBasis_eq_ofList]
  simp only [timeOrder, Basis.constr_basis]

lemma timeOrder_ofList_nil : timeOrder (𝓕 := 𝓕) (ofList []) = 1 := by
  rw [timeOrder_ofList]
  simp [timeOrderSign, Wick.koszulSign, timeOrderList]

@[simp]
lemma timeOrder_ofList_singleton (φ : 𝓕.States) : timeOrder (ofList [φ]) = ofList [φ] := by
  simp [timeOrder_ofList, timeOrderSign, timeOrderList]

lemma timeOrder_ofState_ofState_ordered {φ ψ : 𝓕.States} (h : timeOrderRel φ ψ) :
    timeOrder (ofState φ * ofState ψ) = ofState φ * ofState ψ := by
  rw [← ofList_singleton, ← ofList_singleton, ← ofList_append, timeOrder_ofList]
  simp only [List.singleton_append]
  rw [timeOrderSign_pair_ordered h, timeOrderList_pair_ordered h]
  simp

lemma timeOrder_ofState_ofState_not_ordered {φ ψ : 𝓕.States} (h :¬ timeOrderRel φ ψ) :
    timeOrder (ofState φ * ofState ψ) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • ofState ψ * ofState φ := by
  rw [← ofList_singleton, ← ofList_singleton, ← ofList_append, timeOrder_ofList]
  simp only [List.singleton_append, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [timeOrderSign_pair_not_ordered h, timeOrderList_pair_not_ordered h]
  simp [← ofList_append]

lemma timeOrder_ofState_ofState_not_ordered_eq_timeOrder {φ ψ : 𝓕.States} (h :¬ timeOrderRel φ ψ) :
    timeOrder (ofState φ * ofState ψ) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • timeOrder (ofState ψ * ofState φ) := by
  rw [timeOrder_ofState_ofState_not_ordered h]
  rw [timeOrder_ofState_ofState_ordered]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc]
  have hx := IsTotal.total (r := timeOrderRel) ψ φ
  simp_all

lemma timeOrder_eq_maxTimeField_mul (φ : 𝓕.States) (φs : List 𝓕.States) :
    timeOrder (ofList (φ :: φs)) =
    𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ (φ :: φs).take (maxTimeFieldPos φ φs)) •
    ofState (maxTimeField φ φs) * timeOrder (ofList (eraseMaxTimeField φ φs)) := by
  rw [timeOrder_ofList, timeOrderList_eq_maxTimeField_timeOrderList]
  rw [ofList_cons, timeOrder_ofList]
  simp only [instCommGroup.eq_1, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  congr
  rw [timerOrderSign_of_eraseMaxTimeField, mul_assoc]
  simp

end StateAlgebra
end
end FieldSpecification
