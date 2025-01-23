/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
/-!

# Wick's theorem

This file contrains the time-dependent version of Wick's theorem
for lists of fields containing both fermions and bosons.

Wick's theorem is related to Isserlis' theorem in mathematics.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification} {𝓞 : 𝓕.ProtoOperatorAlgebra}
open CrAnAlgebra
open StateAlgebra
open ProtoOperatorAlgebra
open HepLean.List
open WickContraction
open FieldStatistic

lemma insertList_none_normalOrder (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (c : WickContraction φs.length) :
    𝓞.crAnF (normalOrder (ofStateList (List.map (φs.insertIdx i φ).get
      (c.insertList φ φs i none).uncontractedList)))
    = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, c.uncontracted.filter (fun x => i.succAbove x < i)⟩) •
    𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (c.uncontractedList.map φs.get) φ none))) := by
  simp only [Nat.succ_eq_add_one, instCommGroup.eq_1, optionEraseZ]
  rw [crAnF_ofState_normalOrder_insert φ (c.uncontractedList.map φs.get)
    ⟨(c.uncontractedListOrderPos i), by simp⟩, smul_smul]
  trans (1 : ℂ) • 𝓞.crAnF (normalOrder (ofStateList
    (List.map (List.insertIdx (↑i) φ φs).get (insertList φ φs c i none).uncontractedList)))
  · simp
  congr 1
  simp only [instCommGroup.eq_1]
  rw [← List.map_take, take_uncontractedListOrderPos_eq_filter]
  have h1 : (𝓕 |>ₛ List.map φs.get (List.filter (fun x => decide (↑x < i.1)) c.uncontractedList))
        = 𝓕 |>ₛ ⟨φs.get, (c.uncontracted.filter (fun x => x.val < i.1))⟩ := by
      simp only [Nat.succ_eq_add_one, ofFinset]
      congr
      rw [uncontractedList_eq_sort]
      have hdup : (List.filter (fun x => decide (x.1 < i.1))
          (Finset.sort (fun x1 x2 => x1 ≤ x2) c.uncontracted)).Nodup := by
        exact List.Nodup.filter _ (Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) c.uncontracted)
      have hsort : (List.filter (fun x => decide (x.1 < i.1))
          (Finset.sort (fun x1 x2 => x1 ≤ x2) c.uncontracted)).Sorted (· ≤ ·) := by
        exact List.Sorted.filter _ (Finset.sort_sorted (fun x1 x2 => x1 ≤ x2) c.uncontracted)
      rw [← (List.toFinset_sort (· ≤ ·) hdup).mpr hsort]
      congr
      ext a
      simp
  rw [h1]
  simp only [Nat.succ_eq_add_one]
  have h2 : (Finset.filter (fun x => x.1 < i.1) c.uncontracted) =
    (Finset.filter (fun x => i.succAbove x < i) c.uncontracted) := by
    ext a
    simp only [Nat.succ_eq_add_one, Finset.mem_filter, and_congr_right_iff]
    intro ha
    simp only [Fin.succAbove]
    split
    · apply Iff.intro
      · intro h
        omega
      · intro h
        rename_i h
        rw [Fin.lt_def] at h
        simp only [Fin.coe_castSucc] at h
        omega
    · apply Iff.intro
      · intro h
        rename_i h'
        rw [Fin.lt_def]
        simp only [Fin.val_succ]
        rw [Fin.lt_def] at h'
        simp only [Fin.coe_castSucc, not_lt] at h'
        omega
      · intro h
        rename_i h
        rw [Fin.lt_def] at h
        simp only [Fin.val_succ] at h
        omega
  rw [h2]
  simp only [exchangeSign_mul_self]
  congr
  simp only [Nat.succ_eq_add_one]
  rw [insertList_uncontractedList_none_map]

lemma insertList_some_normalOrder (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (c : WickContraction φs.length) (k : c.uncontracted) :
    𝓞.crAnF (normalOrder (ofStateList (List.map (φs.insertIdx i φ).get
    (c.insertList φ φs i (some k)).uncontractedList)))
    = 𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (c.uncontractedList.map φs.get) φ
    ((uncontractedStatesEquiv φs c) k)))) := by
  simp only [Nat.succ_eq_add_one, insertList, optionEraseZ, uncontractedStatesEquiv,
    Equiv.optionCongr_apply, Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply,
    Fin.coe_cast]
  congr
  rw [congr_uncontractedList]
  erw [uncontractedList_extractEquiv_symm_some]
  simp only [Fin.coe_succAboveEmb, List.map_eraseIdx, List.map_map]
  congr
  conv_rhs => rw [get_eq_insertIdx_succAbove φ φs i]

lemma sign_timeContract_normalOrder_insertList_none (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (c : WickContraction φs.length) :
    (c.insertList φ φs i none).sign • (c.insertList φ φs i none).timeContract 𝓞
    * 𝓞.crAnF (normalOrder (ofStateList (List.map (φs.insertIdx i φ).get
      (c.insertList φ φs i none).uncontractedList))) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun k => i.succAbove k < i))⟩)
    • (c.sign • c.timeContract 𝓞 * 𝓞.crAnF (normalOrder
      (ofStateList (optionEraseZ (c.uncontractedList.map φs.get) φ none)))) := by
  by_cases hg : GradingCompliant φs c
  · rw [insertList_none_normalOrder, sign_insert_none]
    simp only [Nat.succ_eq_add_one, timeContract_insertList_none, instCommGroup.eq_1,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
    congr 1
    rw [← mul_assoc]
    congr 1
    rw [signInsertNone_eq_filterset _ _ _ _ hg, ← map_mul]
    congr
    rw [ofFinset_union]
    congr
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_inter, not_and, not_lt, and_imp]
    apply Iff.intro
    · intro ha
      have ha1 := ha.1
      rcases ha1 with ha1 | ha1
      · exact ha1.2
      · exact ha1.2
    · intro ha
      simp only [uncontracted, Finset.mem_filter, Finset.mem_univ, true_and, ha, and_true,
        forall_const]
      have hx : c.getDual? a = none ↔ ¬ (c.getDual? a).isSome := by
        simp
      rw [hx]
      simp only [Bool.not_eq_true, Bool.eq_false_or_eq_true_self, true_and]
      intro h1 h2
      simp_all
  · simp only [Nat.succ_eq_add_one, timeContract_insertList_none, Algebra.smul_mul_assoc,
    instCommGroup.eq_1]
    rw [timeContract_of_not_gradingCompliant]
    simp only [ZeroMemClass.coe_zero, zero_mul, smul_zero]
    exact hg

lemma sign_timeContract_normalOrder_insertList_some (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (c : WickContraction φs.length) (k : c.uncontracted)
    (hlt : ∀ (k : Fin φs.length), timeOrderRel φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬ timeOrderRel φs[k] φ) :
    (c.insertList φ φs i (some k)).sign • (c.insertList φ φs i (some k)).timeContract 𝓞
    * 𝓞.crAnF (normalOrder (ofStateList (List.map (φs.insertIdx i φ).get
      (c.insertList φ φs i (some k)).uncontractedList))) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => i.succAbove x < i))⟩)
    • (c.sign • (𝓞.contractStateAtIndex φ (List.map φs.get c.uncontractedList)
      ((uncontractedStatesEquiv φs c) (some k)) * c.timeContract 𝓞)
    * 𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (c.uncontractedList.map φs.get) φ
      ((uncontractedStatesEquiv φs c) k))))) := by
  by_cases hg : GradingCompliant φs c ∧ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[k.1])
  · by_cases hk : i.succAbove k < i
    · rw [WickContraction.timeConract_insertList_some_eq_mul_contractStateAtIndex_not_lt]
      swap
      · exact hn _ hk
      rw [insertList_some_normalOrder, sign_insert_some]
      simp only [instCommGroup.eq_1, smul_smul, Algebra.smul_mul_assoc]
      congr 1
      rw [mul_assoc, mul_comm (sign φs c), ← mul_assoc]
      congr 1
      exact signInsertSome_mul_filter_contracted_of_lt φ φs c i k hk hg
      · omega
    · have hik : i.succAbove ↑k ≠ i := Fin.succAbove_ne i ↑k
      rw [WickContraction.timeConract_insertList_some_eq_mul_contractStateAtIndex_lt]
      swap
      · exact hlt _
      rw [insertList_some_normalOrder]
      rw [sign_insert_some]
      simp only [instCommGroup.eq_1, smul_smul, Algebra.smul_mul_assoc]
      congr 1
      rw [mul_assoc, mul_comm (sign φs c), ← mul_assoc]
      congr 1
      exact signInsertSome_mul_filter_contracted_of_not_lt φ φs c i k hk hg
      · omega
  · rw [timeConract_insertList_some]
    simp only [Fin.getElem_fin, not_and] at hg
    by_cases hg' : GradingCompliant φs c
    · have hg := hg hg'
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, Algebra.smul_mul_assoc,
        instCommGroup.eq_1, contractStateAtIndex, uncontractedStatesEquiv, Equiv.optionCongr_apply,
        Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply, Fin.coe_cast,
        List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem]
      by_cases h1 : i < i.succAbove ↑k
      · simp only [h1, ↓reduceIte, MulMemClass.coe_mul]
        rw [timeContract_zero_of_diff_grade]
        simp only [zero_mul, smul_zero]
        rw [crAnF_superCommute_anPart_ofState_diff_grade_zero]
        simp only [zero_mul, smul_zero]
        exact hg
        exact hg
      · simp only [h1, ↓reduceIte, MulMemClass.coe_mul]
        rw [timeContract_zero_of_diff_grade]
        simp only [zero_mul, smul_zero]
        rw [crAnF_superCommute_anPart_ofState_diff_grade_zero]
        simp only [zero_mul, smul_zero]
        exact hg
        exact fun a => hg (id (Eq.symm a))
    · rw [timeContract_of_not_gradingCompliant]
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, mul_zero, ZeroMemClass.coe_zero, smul_zero,
        zero_mul, instCommGroup.eq_1]
      exact hg'

lemma mul_sum_contractions (φ : 𝓕.States) (φs : List 𝓕.States) (i : Fin φs.length.succ)
    (c : WickContraction φs.length) (hlt : ∀ (k : Fin φs.length), timeOrderRel φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬timeOrderRel φs[k] φ) :
    (c.sign • c.timeContract 𝓞) * 𝓞.crAnF ((CrAnAlgebra.ofState φ) *
      normalOrder (ofStateList (c.uncontractedList.map φs.get))) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => i.succAbove x < i))⟩) •
    ∑ (k : Option (c.uncontracted)),
    ((c.insertList φ φs i k).sign • (c.insertList φ φs i k).timeContract 𝓞
    * 𝓞.crAnF (normalOrder
      (ofStateList ((c.insertList φ φs i k).uncontractedList.map (φs.insertIdx i φ).get)))) := by
  rw [crAnF_ofState_mul_normalOrder_ofStatesList_eq_sum, Finset.mul_sum,
    uncontractedStatesEquiv_list_sum, Finset.smul_sum]
  simp only [Finset.univ_eq_attach, instCommGroup.eq_1,
    Nat.succ_eq_add_one, timeContract_insertList_none]
  congr 1
  funext n
  match n with
  | none =>
    rw [sign_timeContract_normalOrder_insertList_none]
    simp only [contractStateAtIndex, uncontractedStatesEquiv, Equiv.optionCongr_apply,
      Equiv.coe_trans, Option.map_none', one_mul, Algebra.smul_mul_assoc, instCommGroup.eq_1,
      smul_smul]
    congr 1
    rw [← mul_assoc, exchangeSign_mul_self]
    simp
  | some n =>
    rw [sign_timeContract_normalOrder_insertList_some _ _ _ _ _
      (fun k => hlt k) (fun k a => hn k a)]
    simp only [uncontractedStatesEquiv, Equiv.optionCongr_apply, Equiv.coe_trans, Option.map_some',
      Function.comp_apply, finCongr_apply, Algebra.smul_mul_assoc, instCommGroup.eq_1, smul_smul]
    congr 1
    · rw [← mul_assoc, exchangeSign_mul_self]
      rw [one_mul]
    · rw [← mul_assoc]
      congr 1
      have ht := (WickContraction.timeContract 𝓞 c).prop
      rw [@Subalgebra.mem_center_iff] at ht
      rw [ht]

lemma wicks_theorem_congr {φs φs' : List 𝓕.States} (h : φs = φs') :
    ∑ (c : WickContraction φs.length), (c.sign • c.timeContract 𝓞) *
      𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map φs.get)))
    = ∑ (c : WickContraction φs'.length), (c.sign • c.timeContract 𝓞) *
      𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map φs'.get))) := by
  subst h
  simp

/-- Wick's theorem for the empty list. -/
lemma wicks_theorem_nil :
    𝓞.crAnF (ofStateAlgebra (timeOrder (ofList []))) = ∑ (c : WickContraction [].length),
    (c.sign [] • c.timeContract 𝓞) *
    𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map [].get))) := by
  rw [timeOrder_ofList_nil]
  simp only [map_one, List.length_nil, Algebra.smul_mul_assoc]
  rw [sum_WickContraction_nil, nil_zero_uncontractedList]
  simp only [List.map_nil]
  have h1 : ofStateList (𝓕 := 𝓕) [] = CrAnAlgebra.ofCrAnList [] := by simp
  rw [h1, normalOrder_ofCrAnList]
  simp [WickContraction.timeContract, empty, sign]

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

/-- Wick's theorem for time-ordered products of bosonic and fermionic fields. -/
theorem wicks_theorem : (φs : List 𝓕.States) → 𝓞.crAnF (ofStateAlgebra (timeOrder (ofList φs))) =
    ∑ (c : WickContraction φs.length), (c.sign φs • c.timeContract 𝓞) *
      𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map φs.get)))
  | [] => wicks_theorem_nil
  | φ :: φs => by
    have ih := wicks_theorem (eraseMaxTimeField φ φs)
    rw [timeOrder_eq_maxTimeField_mul_finset, map_mul, map_mul, ih, Finset.mul_sum]
    have h1 : φ :: φs =
        (eraseMaxTimeField φ φs).insertIdx (maxTimeFieldPosFin φ φs) (maxTimeField φ φs) := by
      simp only [eraseMaxTimeField, insertionSortDropMinPos, List.length_cons, Nat.succ_eq_add_one,
        maxTimeField, insertionSortMin, List.get_eq_getElem]
      erw [insertIdx_eraseIdx_fin]
    rw [wicks_theorem_congr h1]
    conv_rhs => rw [insertLift_sum]
    congr
    funext c
    have ht := Subalgebra.mem_center_iff.mp (Subalgebra.smul_mem (Subalgebra.center ℂ 𝓞.A)
      (WickContraction.timeContract 𝓞 c).2 (sign (eraseMaxTimeField φ φs) c))
    rw [map_smul, map_smul, Algebra.smul_mul_assoc, ← mul_assoc, ht, mul_assoc, ← map_mul]
    rw [ofStateAlgebra_ofState, mul_sum_contractions (𝓞 := 𝓞)
      (maxTimeField φ φs) (eraseMaxTimeField φ φs) (maxTimeFieldPosFin φ φs) c]
    trans (1 : ℂ) • ∑ k : Option { x // x ∈ c.uncontracted }, sign
      (List.insertIdx (↑(maxTimeFieldPosFin φ φs)) (maxTimeField φ φs) (eraseMaxTimeField φ φs))
      (insertList (maxTimeField φ φs) (eraseMaxTimeField φ φs) c (maxTimeFieldPosFin φ φs) k) •
      ↑(WickContraction.timeContract 𝓞 (insertList (maxTimeField φ φs) (eraseMaxTimeField φ φs) c
      (maxTimeFieldPosFin φ φs) k)) *
      𝓞.crAnF (normalOrder (ofStateList (List.map (List.insertIdx (↑(maxTimeFieldPosFin φ φs))
      (maxTimeField φ φs) (eraseMaxTimeField φ φs)).get
        (insertList (maxTimeField φ φs) (eraseMaxTimeField φ φs) c
        (maxTimeFieldPosFin φ φs) k).uncontractedList)))
    swap
    · simp
    rw [smul_smul]
    simp only [instCommGroup.eq_1, exchangeSign_mul_self, Nat.succ_eq_add_one,
      Algebra.smul_mul_assoc, Fintype.sum_option, timeContract_insertList_none,
      Finset.univ_eq_attach, smul_add, one_smul]
    · exact fun k => timeOrder_maxTimeField _ _ k
    · exact fun k => lt_maxTimeFieldPosFin_not_timeOrder _ _ k
termination_by φs => φs.length

end FieldSpecification
