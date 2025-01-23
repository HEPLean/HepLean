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
open HepLean.List

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

/-- In the state algebra time, ordering obeys `T(φ₀φ₁…φₙ) = s * φᵢ * T(φ₀φ₁…φᵢ₋₁φᵢ₊₁…φₙ)` where `φᵢ` is the state
  which has maximum time and `s` is the exchange sign of `φᵢ` and `φ₀φ₁…φᵢ₋₁`. -/
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

/-- In the state algebra time, ordering obeys `T(φ₀φ₁…φₙ) = s * φᵢ * T(φ₀φ₁…φᵢ₋₁φᵢ₊₁…φₙ)` where `φᵢ` is the state
  which has maximum time and `s` is the exchange sign of `φᵢ` and `φ₀φ₁…φᵢ₋₁`.
  Here `s` is written using finite sets. -/
lemma timeOrder_eq_maxTimeField_mul_finset (φ : 𝓕.States) (φs : List 𝓕.States) :
    timeOrder (ofList (φ :: φs)) = 𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ ⟨(eraseMaxTimeField φ φs).get,
      (Finset.filter (fun x =>
        (maxTimeFieldPosFin φ φs).succAbove x < maxTimeFieldPosFin φ φs) Finset.univ)⟩) •
    StateAlgebra.ofState (maxTimeField φ φs) * timeOrder (ofList (eraseMaxTimeField φ φs)) := by
  rw [timeOrder_eq_maxTimeField_mul]
  congr 3
  apply FieldStatistic.ofList_perm
  nth_rewrite 1 [← List.finRange_map_get (φ :: φs)]
  simp only [List.length_cons, eraseMaxTimeField, insertionSortDropMinPos]
  rw [eraseIdx_get, ← List.map_take, ← List.map_map]
  refine List.Perm.map (φ :: φs).get ?_
  apply (List.perm_ext_iff_of_nodup _ _).mpr
  · intro i
    simp only [List.length_cons, maxTimeFieldPos, mem_take_finrange, Fin.val_fin_lt, List.mem_map,
      Finset.mem_sort, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    refine Iff.intro (fun hi => ?_) (fun h => ?_)
    · have h2 := (maxTimeFieldPosFin φ φs).2
      simp only [eraseMaxTimeField, insertionSortDropMinPos, List.length_cons, Nat.succ_eq_add_one,
        maxTimeFieldPosFin, insertionSortMinPosFin] at h2
      use ⟨i, by omega⟩
      apply And.intro
      · simp only [Fin.succAbove, List.length_cons, Fin.castSucc_mk, maxTimeFieldPosFin,
        insertionSortMinPosFin, Nat.succ_eq_add_one, Fin.mk_lt_mk, Fin.val_fin_lt, Fin.succ_mk]
        rw [Fin.lt_def]
        split
        · simp only [Fin.val_fin_lt]
          omega
        · omega
      · simp only [Fin.succAbove, List.length_cons, Fin.castSucc_mk, Fin.succ_mk, Fin.ext_iff,
        Fin.coe_cast]
        split
        · simp
        · simp_all [Fin.lt_def]
    · obtain ⟨j, h1, h2⟩ := h
      subst h2
      simp only [Fin.lt_def, Fin.coe_cast]
      exact h1
  · exact List.Sublist.nodup (List.take_sublist _ _) <|
      List.nodup_finRange (φs.length + 1)
  · refine List.Nodup.map ?_ ?_
    · refine Function.Injective.comp ?hf.hg Fin.succAbove_right_injective
      exact Fin.cast_injective (eraseIdx_length (φ :: φs) (insertionSortMinPos timeOrderRel φ φs))
    · exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2)
        (Finset.filter (fun x => (maxTimeFieldPosFin φ φs).succAbove x < maxTimeFieldPosFin φ φs)
          Finset.univ)

end StateAlgebra
end
end FieldSpecification
