/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.Sign
import HepLean.PerturbationTheory.Algebras.OperatorAlgebra.TimeContraction
/-!

# Time contractions


-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)
open HepLean.List


/-!

## Time contract.

-/


noncomputable def timeContract (𝓞 : 𝓕.OperatorAlgebra) {φs : List 𝓕.States}
    (c : ContractionsNat φs.length) :
    Subalgebra.center ℂ 𝓞.A :=
  ∏ (a : c.1), ⟨𝓞.timeContract (φs.get (c.fstFieldOfContract a)) (φs.get (c.sndFieldOfContract a)),
     𝓞.timeContract_mem_center _ _⟩

@[simp]
lemma timeContract_insertList_none (𝓞 : 𝓕.OperatorAlgebra) (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) :
    (c.insertList φ φs i none).timeContract 𝓞 = c.timeContract 𝓞 := by
  rw [timeContract, insertList_none_prod_contractions]
  congr
  ext a
  simp

lemma timeConract_insertList_some (𝓞 : 𝓕.OperatorAlgebra) (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) (j : c.uncontracted) :
    (c.insertList φ φs i (some j)).timeContract 𝓞 =
    (if i < i.succAbove j then
      ⟨𝓞.timeContract φ φs[j.1], 𝓞.timeContract_mem_center _ _⟩
    else ⟨𝓞.timeContract φs[j.1] φ , 𝓞.timeContract_mem_center _ _⟩)
     * c.timeContract 𝓞 := by
  rw [timeContract, insertList_some_prod_contractions]
  congr 1
  · simp
    split
    · simp
    · simp
  · congr
    ext a
    simp

open FieldStatistic

lemma timeConract_insertList_some_eq_mul_contractMemList_lt
    (𝓞 : 𝓕.OperatorAlgebra) (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) (k : c.uncontracted)
    (ht : 𝓕.timeOrderProp φ φs[k.1]) (hik : i < i.succAbove k):
    (c.insertList φ φs i (some k)).timeContract 𝓞 =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (c.uncontracted.filter (fun x => x < k))⟩)
    • (𝓞.contractMemList φ (List.map φs.get c.uncontractedList)
    ((uncontractedStatesEquiv φs c) (some k)) * c.timeContract 𝓞):= by
  rw [timeConract_insertList_some]
  simp [OperatorAlgebra.contractMemList, uncontractedStatesEquiv]
  · simp [hik]
    rw [𝓞.timeContract_of_timeOrderProp ]
    trans (1 :  ℂ) •  (𝓞.crAnF ((CrAnAlgebra.superCommute (CrAnAlgebra.anPart (StateAlgebra.ofState φ))) (CrAnAlgebra.ofState φs[k.1])) *
    ↑(timeContract 𝓞 c))
    · simp
    simp only [smul_smul]
    congr
    have h1 : ofList 𝓕.statesStatistic (List.take (↑(c.uncontractedFinEquiv.symm k)) (List.map φs.get c.uncontractedList))
        = (𝓕 |>ₛ ⟨φs.get, (Finset.filter (fun x =>  x < k) c.uncontracted)⟩) := by
      simp [ofFinset]
      congr
      rw [← List.map_take]
      congr
      rw [take_uncontractedFinEquiv_symm]
      rw [filter_uncontractedList]
    rw [h1]
    simp
    · exact ht

lemma timeConract_insertList_some_eq_mul_contractMemList_not_lt
    (𝓞 : 𝓕.OperatorAlgebra) (φ : 𝓕.States) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (i : Fin φs.length.succ) (k : c.uncontracted)
    (ht : ¬ 𝓕.timeOrderProp φs[k.1] φ) (hik : ¬ i < i.succAbove k):
    (c.insertList φ φs i (some k)).timeContract 𝓞 =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (c.uncontracted.filter (fun x => x ≤ k))⟩)
    • (𝓞.contractMemList φ (List.map φs.get c.uncontractedList)
    ((uncontractedStatesEquiv φs c) (some k)) * c.timeContract 𝓞):= by
  rw [timeConract_insertList_some]
  simp [OperatorAlgebra.contractMemList, uncontractedStatesEquiv]
  simp [hik]
  rw [𝓞.timeContract_of_not_timeOrderProp, 𝓞.timeContract_of_timeOrderProp ]
  simp [smul_smul]
  congr
  have h1 : ofList 𝓕.statesStatistic (List.take (↑(c.uncontractedFinEquiv.symm k)) (List.map φs.get c.uncontractedList))
        = (𝓕 |>ₛ ⟨φs.get, (Finset.filter (fun x =>  x < k) c.uncontracted)⟩) := by
      simp [ofFinset]
      congr
      rw [← List.map_take]
      congr
      rw [take_uncontractedFinEquiv_symm]
      rw [filter_uncontractedList]
  rw [h1]
  trans (pairedSign (𝓕.statesStatistic φ)) (𝓕 |>ₛ ⟨φs.get, {k.1}⟩)
  · rw [pairedSign_symm]
    rw [ofFinset_singleton]
    simp
  rw [← map_mul]
  congr
  rw [ofFinset_union]
  congr
  ext a
  simp
  apply Iff.intro
  · intro h
    subst h
    simp
  · intro h
    have h1 := h.1
    rcases h1 with h1 | h1
    · have h2' := h.2 h1.1 h1.2 h1.1
      omega
    · have h2' := h.2 h1.1 (by omega) h1.1
      omega
  have ht := IsTotal.total (r := timeOrderProp) φs[k.1] φ
  simp_all
  exact ht

lemma timeContract_of_not_isGradedObeying (𝓞 : 𝓕.OperatorAlgebra) (φs : List 𝓕.States)
    (c : ContractionsNat φs.length) (h : ¬ IsGradedObeying φs c) :
    c.timeContract 𝓞 = 0 := by
  rw [timeContract]
  simp [IsGradedObeying] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨ha, ha2⟩ := ha
  apply Finset.prod_eq_zero (i := ⟨a, ha⟩)
  simp
  apply Subtype.eq
  simp
  rw [OperatorAlgebra.timeContract_zero_of_diff_grade]
  simp [ha2]


end ContractionsNat

end FieldStruct
