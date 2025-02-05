/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.Sign.Basic
import HepLean.PerturbationTheory.FieldOpAlgebra.TimeContraction
/-!

# Time contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra
/-- Given a Wick contraction `φsΛ` associated with a list `φs`, the
  product of all time-contractions of pairs of contracted elements in `φs`,
  as a member of the center of `𝓞.A`. -/
noncomputable def timeContract {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) :
    Subalgebra.center ℂ 𝓕.FieldOpAlgebra :=
  ∏ (a : φsΛ.1), ⟨FieldOpAlgebra.timeContract
    (φs.get (φsΛ.fstFieldOfContract a)) (φs.get (φsΛ.sndFieldOfContract a)),
    timeContract_mem_center _ _⟩

/-- For `φsΛ` a Wick contraction for `φs`, the time contraction `(φsΛ ↩Λ φ i none).timeContract 𝓞`
  is equal to `φsΛ.timeContract 𝓞`.

This result follows from the fact that `timeContract` only depends on contracted pairs,
and `(φsΛ ↩Λ φ i none)` has the 'same' contracted pairs as `φsΛ`. -/
@[simp]
lemma timeContract_insertAndContract_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    (φsΛ ↩Λ φ i none).timeContract = φsΛ.timeContract := by
  rw [timeContract, insertAndContract_none_prod_contractions]
  congr
  ext a
  simp

/-- For `φsΛ` a Wick contraction for `φs = φ₀…φₙ`, the time contraction
  `(φsΛ ↩Λ φ i (some j)).timeContract 𝓞` is equal to the multiple of
- the time contraction of `φ` with `φⱼ` if `i < i.succAbove j` else
    `φⱼ` with `φ`.
- `φsΛ.timeContract 𝓞`.
This follows from the fact that `(φsΛ ↩Λ φ i (some j))` has one more contracted pair than `φsΛ`,
corresponding to `φ` contracted with `φⱼ`. The order depends on whether we insert `φ` before
or after `φⱼ`. -/
lemma timeContract_insertAndContract_some
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    (φsΛ ↩Λ φ i (some j)).timeContract =
    (if i < i.succAbove j then
      ⟨FieldOpAlgebra.timeContract φ φs[j.1], timeContract_mem_center _ _⟩
    else ⟨FieldOpAlgebra.timeContract φs[j.1] φ, timeContract_mem_center _ _⟩) *
    φsΛ.timeContract := by
  rw [timeContract, insertAndContract_some_prod_contractions]
  congr 1
  · simp only [Nat.succ_eq_add_one, insertAndContract_fstFieldOfContract_some_incl, finCongr_apply,
    List.get_eq_getElem, insertAndContract_sndFieldOfContract_some_incl, Fin.getElem_fin]
    split
    · simp
    · simp
  · congr
    ext a
    simp

@[simp]
lemma timeContract_empty (φs : List 𝓕.FieldOp) :
    (@empty φs.length).timeContract = 1 := by
  rw [timeContract, empty]
  simp

open FieldStatistic

lemma timeContract_insertAndContract_some_eq_mul_contractStateAtIndex_lt
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (ht : 𝓕.timeOrderRel φ φs[k.1]) (hik : i < i.succAbove k) :
    (φsΛ ↩Λ φ i (some k)).timeContract =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (φsΛ.uncontracted.filter (fun x => x < k))⟩)
    • (contractStateAtIndex φ [φsΛ]ᵘᶜ ((uncontractedFieldOpEquiv φs φsΛ) (some k)) *
      φsΛ.timeContract) := by
  rw [timeContract_insertAndContract_some]
  simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, instCommGroup.eq_1,
    contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
    Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply, Fin.coe_cast,
    List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem,
    Algebra.smul_mul_assoc, uncontractedListGet]
  · simp only [hik, ↓reduceIte, MulMemClass.coe_mul]
    rw [timeContract_of_timeOrderRel]
    trans (1 : ℂ) • ((superCommute (anPart φ)) (ofFieldOp φs[k.1]) * ↑φsΛ.timeContract)
    · simp
    simp only [smul_smul]
    congr 1
    have h1 : ofList 𝓕.statesStatistic (List.take (↑(φsΛ.uncontractedIndexEquiv.symm k))
        (List.map φs.get φsΛ.uncontractedList))
        = (𝓕 |>ₛ ⟨φs.get, (Finset.filter (fun x => x < k) φsΛ.uncontracted)⟩) := by
      simp only [ofFinset]
      congr
      rw [← List.map_take]
      congr
      rw [take_uncontractedIndexEquiv_symm]
      rw [filter_uncontractedList]
    rw [h1]
    simp only [exchangeSign_mul_self]
    · exact ht

lemma timeContract_insertAndContract_some_eq_mul_contractStateAtIndex_not_lt
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (ht : ¬ 𝓕.timeOrderRel φs[k.1] φ) (hik : ¬ i < i.succAbove k) :
    (φsΛ ↩Λ φ i (some k)).timeContract =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (φsΛ.uncontracted.filter (fun x => x ≤ k))⟩)
    • (contractStateAtIndex φ [φsΛ]ᵘᶜ
      ((uncontractedFieldOpEquiv φs φsΛ) (some k)) * φsΛ.timeContract) := by
  rw [timeContract_insertAndContract_some]
  simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, instCommGroup.eq_1,
    contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
    Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply, Fin.coe_cast,
    List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem,
    Algebra.smul_mul_assoc, uncontractedListGet]
  simp only [hik, ↓reduceIte, MulMemClass.coe_mul]
  rw [timeContract_of_not_timeOrderRel, timeContract_of_timeOrderRel]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc, smul_smul]
  congr
  have h1 : ofList 𝓕.statesStatistic (List.take (↑(φsΛ.uncontractedIndexEquiv.symm k))
      (List.map φs.get φsΛ.uncontractedList))
      = (𝓕 |>ₛ ⟨φs.get, (Finset.filter (fun x => x < k) φsΛ.uncontracted)⟩) := by
    simp only [ofFinset]
    congr
    rw [← List.map_take]
    congr
    rw [take_uncontractedIndexEquiv_symm, filter_uncontractedList]
  rw [h1]
  trans 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, {k.1}⟩)
  · rw [exchangeSign_symm, ofFinset_singleton]
    simp
  rw [← map_mul]
  congr
  rw [ofFinset_union]
  congr
  ext a
  simp only [Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter,
    Finset.mem_inter, not_and, not_lt, and_imp]
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
  have ht := IsTotal.total (r := timeOrderRel) φs[k.1] φ
  simp_all only [Fin.getElem_fin, Nat.succ_eq_add_one, not_lt, false_or]
  exact ht

lemma timeContract_of_not_gradingCompliant (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (h : ¬ GradingCompliant φs φsΛ) :
    φsΛ.timeContract = 0 := by
  rw [timeContract]
  simp only [GradingCompliant, Fin.getElem_fin, Subtype.forall, not_forall] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨ha, ha2⟩ := ha
  apply Finset.prod_eq_zero (i := ⟨a, ha⟩)
  simp only [Finset.univ_eq_attach, Finset.mem_attach]
  apply Subtype.eq
  simp only [List.get_eq_getElem, ZeroMemClass.coe_zero]
  rw [timeContract_zero_of_diff_grade]
  simp [ha2]

end WickContraction
