/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.TimeContract
/-!

# Wick's theorem

This file contrains the time-dependent version of Wick's theorem
for lists of fields containing both fermions and bosons.

-/

namespace FieldStruct
variable {𝓕 : FieldStruct} {𝓞 : 𝓕.OperatorAlgebra}
open CrAnAlgebra
open StateAlgebra
open OperatorAlgebra
open HepLean.List
open ContractionsNat
open FieldStatistic


lemma insertList_none_normalOrder (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (c : ContractionsNat φs.length) :
     𝓞.crAnF (normalOrder (ofStateList (List.map (φs.insertIdx i φ).get (c.insertList φ φs i none).uncontractedList)))
     = 𝓢(𝓕 |>ₛ φ, fieldStatOfFinset φs.get (c.uncontracted.filter (fun x => i.succAbove x < i))) •
    𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (c.uncontractedList.map φs.get) φ none))) := by
  simp [optionEraseZ]
  rw [crAnF_ofState_normalOrder_insert φ (c.uncontractedList.map φs.get)
    ⟨(c.uncontractedListOrderPos i), by simp⟩]
  rw [smul_smul]
  trans (1 : ℂ) • 𝓞.crAnF
    (normalOrder (ofStateList (List.map (List.insertIdx (↑i) φ φs).get (insertList φ φs c i none).uncontractedList)))
  · simp
  congr 1
  simp
  rw [← List.map_take]
  rw [take_uncontractedListOrderPos_eq_filter]
  have h1 : (𝓕 |>ₛ  (List.map φs.get (List.filter (fun x => decide (↑x < i.1)) c.uncontractedList)))
        = fieldStatOfFinset φs.get (c.uncontracted.filter (fun x => x.val  < i.1)):= by
      simp [fieldStatOfFinset]
      congr
      rw [uncontractedList_eq_sort]
      have hdup : (List.filter (fun x => decide (x.1 < i.1)) (Finset.sort (fun x1 x2 => x1 ≤ x2) c.uncontracted)).Nodup := by
        exact List.Nodup.filter _ (Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) c.uncontracted)
      have hsort : (List.filter (fun x => decide (x.1 < i.1)) (Finset.sort (fun x1 x2 => x1 ≤ x2) c.uncontracted)).Sorted (· ≤ ·) := by
        exact List.Sorted.filter _ (Finset.sort_sorted (fun x1 x2 => x1 ≤ x2) c.uncontracted)
      rw [← (List.toFinset_sort (· ≤ ·) hdup).mpr hsort]
      congr
      ext a
      simp
  rw [h1]
  simp
  have h2 : (Finset.filter (fun x => x.1 < i.1) c.uncontracted) =
    (Finset.filter (fun x => i.succAbove x < i) c.uncontracted) := by
    ext a
    simp
    intro ha
    simp [Fin.succAbove]
    split
    · apply Iff.intro
      · intro h
        omega
      · intro h
        rename_i h
        rw [Fin.lt_def] at h
        simp at h
        omega
    · apply Iff.intro
      · intro h
        rename_i h'
        rw [Fin.lt_def]
        simp
        rw [Fin.lt_def] at h'
        simp at h'
        omega
      · intro h
        rename_i h
        rw [Fin.lt_def] at h
        simp at h
        omega
  rw [h2]
  simp
  congr
  simp
  rw [insertList_uncontractedList_none_map]

lemma insertList_some_normalOrder (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (c : ContractionsNat φs.length) (k : c.uncontracted) :
     𝓞.crAnF (normalOrder (ofStateList (List.map (φs.insertIdx i φ).get
      (c.insertList φ φs i (some k)).uncontractedList)))
     = 𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (c.uncontractedList.map φs.get) φ
    ((uncontractedStatesEquiv φs c) k)))) := by
  simp [optionEraseZ, uncontractedStatesEquiv, insertList]
  congr
  rw [congr_uncontractedList]
  erw [uncontractedList_extractEquiv_symm_some]
  simp
  congr
  conv_rhs => rw [get_eq_insertIdx_succAbove φ φs i]

lemma sign_timeContract_normalOrder_insertList_none (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (c : ContractionsNat φs.length) :
    (c.insertList φ φs i none).sign  • (c.insertList φ φs i none).timeContract 𝓞
    * 𝓞.crAnF (normalOrder (ofStateList (List.map (φs.insertIdx i φ).get
      (c.insertList φ φs i none).uncontractedList))) =
    𝓢(𝓕 |>ₛ φ, fieldStatOfFinset φs.get (Finset.univ.filter (fun k => i.succAbove k < i)))
    • (c.sign • c.timeContract 𝓞 * 𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (c.uncontractedList.map φs.get) φ none)))) := by
  by_cases hg : IsGradedObeying φs c
  · rw [insertList_none_normalOrder]
    rw [sign_insert_none]
    simp [smul_smul]
    congr 1
    rw [← mul_assoc]
    congr 1
    rw [signInsertNone_eq_filterset _ _ _ _ hg]
    rw [← map_mul]
    congr
    rw [fieldStatOfFinset_union]
    congr
    ext a
    simp
    apply Iff.intro
    · intro ha
      have ha1 := ha.1
      rcases ha1 with ha1 | ha1
      · exact ha1.2
      · exact ha1.2
    · intro ha
      simp [ha, uncontracted]
      have hx : c.getDual? a = none ↔ ¬ (c.getDual? a).isSome := by
        simp
      rw [hx]
      simp only [Bool.not_eq_true, Bool.eq_false_or_eq_true_self, true_and]
      intro h1 h2
      simp_all
  · simp
    rw [timeContract_of_not_isGradedObeying]
    simp
    exact hg


lemma sign_timeContract_normalOrder_insertList_some (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (c : ContractionsNat φs.length) (k : c.uncontracted)
    (hlt : ∀ (k : Fin φs.length), timeOrderProp φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬ timeOrderProp φs[k] φ) :
    (c.insertList φ φs i (some k)).sign • (c.insertList φ φs i (some k)).timeContract 𝓞
    * 𝓞.crAnF (normalOrder (ofStateList (List.map (φs.insertIdx i φ).get
      (c.insertList φ φs i (some k)).uncontractedList))) =
    𝓢(𝓕 |>ₛ φ, fieldStatOfFinset φs.get (Finset.univ.filter (fun x => i.succAbove x < i)))
    • (c.sign •
    (𝓞.contractMemList φ (List.map φs.get c.uncontractedList) ((uncontractedStatesEquiv φs c) (some k)) * c.timeContract 𝓞)
    * 𝓞.crAnF (normalOrder (ofStateList (optionEraseZ (c.uncontractedList.map φs.get) φ
      ((uncontractedStatesEquiv φs c) k))))) := by
  by_cases hg : IsGradedObeying φs c ∧ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[k.1])
  · by_cases hk : i.succAbove k < i
    · rw [ContractionsNat.timeConract_insertList_some_eq_mul_contractMemList_not_lt]
      swap
      · exact hn _ hk
      rw [insertList_some_normalOrder]
      rw [sign_insert_some]
      simp [smul_smul]
      congr 1
      rw [mul_assoc, mul_comm (sign φs c), ← mul_assoc]
      congr 1
      exact signInsertSome_mul_filter_contracted_of_lt φ φs c i k hk hg
      · omega
    · have hik : i.succAbove ↑k ≠ i := by exact Fin.succAbove_ne i ↑k
      rw [ContractionsNat.timeConract_insertList_some_eq_mul_contractMemList_lt]
      swap
      · exact hlt _
      rw [insertList_some_normalOrder]
      rw [sign_insert_some]
      simp [smul_smul]
      congr 1
      rw [mul_assoc, mul_comm (sign φs c), ← mul_assoc]
      congr 1
      exact signInsertSome_mul_filter_contracted_of_not_lt φ φs c i k hk hg
      · omega
  · rw [timeConract_insertList_some]
    simp at hg
    by_cases hg' : IsGradedObeying φs c
    · have hg := hg hg'
      simp [contractMemList, uncontractedStatesEquiv]
      by_cases h1 : i < i.succAbove ↑k
      · simp [h1]
        rw [timeContract_zero_of_diff_grade]
        simp
        rw [crAnF_superCommute_anPart_ofState_diff_grade_zero]
        simp
        exact hg
        exact hg
      · simp [h1]
        rw [timeContract_zero_of_diff_grade]
        simp
        rw [crAnF_superCommute_anPart_ofState_diff_grade_zero]
        simp
        exact hg
        exact fun a => hg (id (Eq.symm a))
    · rw [timeContract_of_not_isGradedObeying]
      simp
      exact hg'

lemma mul_sum_contractions (φ : 𝓕.States) (φs : List 𝓕.States) (i : Fin φs.length.succ)
    (c : ContractionsNat φs.length)
    (hlt : ∀ (k : Fin φs.length), timeOrderProp φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬timeOrderProp φs[k] φ):
    (c.sign • c.timeContract 𝓞) * 𝓞.crAnF ((CrAnAlgebra.ofState φ) * normalOrder (ofStateList (c.uncontractedList.map φs.get))) =
    𝓢(𝓕 |>ₛ φ, fieldStatOfFinset φs.get (Finset.univ.filter (fun x => i.succAbove x < i))) • ∑ (k : Option (c.uncontracted)),
    ((c.insertList φ φs i k).sign • (c.insertList φ φs i k).timeContract 𝓞
    * 𝓞.crAnF (normalOrder (ofStateList ((c.insertList φ φs i k).uncontractedList.map (φs.insertIdx i φ).get)))) := by
  rw [crAnF_ofState_mul_normalOrder_ofStatesList_eq_sum, Finset.mul_sum,
    uncontractedStatesEquiv_list_sum, Finset.smul_sum]
  simp only [Finset.univ_eq_attach, instCommGroup.eq_1,
    Nat.succ_eq_add_one, timeContract_insertList_none]
  congr 1
  funext n
  match n with
  | none =>
    rw [sign_timeContract_normalOrder_insertList_none]
    simp only [contractMemList, uncontractedStatesEquiv, Equiv.optionCongr_apply, Equiv.coe_trans,
      Option.map_none', one_mul, Algebra.smul_mul_assoc, instCommGroup.eq_1, smul_smul]
    congr 1
    rw [← mul_assoc, pairedSign_mul_self]
    simp
  | some n =>
    rw [sign_timeContract_normalOrder_insertList_some _ _ _ _ _
      (fun k => hlt k) (fun k a => hn k a)]
    simp only [uncontractedStatesEquiv, Equiv.optionCongr_apply, Equiv.coe_trans, Option.map_some',
      Function.comp_apply, finCongr_apply, Algebra.smul_mul_assoc, instCommGroup.eq_1, smul_smul]
    congr 1
    · rw [← mul_assoc, pairedSign_mul_self]
      rw [one_mul]
    · rw [← mul_assoc]
      congr 1
      have ht := (ContractionsNat.timeContract 𝓞 c).prop
      rw [@Subalgebra.mem_center_iff] at ht
      rw [ht]

lemma wicks_theorem_congr {φs φs' : List 𝓕.States} (h : φs = φs'):
    ∑ (c : ContractionsNat φs.length),
      (c.sign • c.timeContract 𝓞) * 𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map φs.get)))
    = ∑ (c : ContractionsNat φs'.length),
       (c.sign • c.timeContract 𝓞) * 𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map φs'.get))) := by
  subst h
  simp

/-- Wick's theorem for the empty list. -/
lemma wicks_theorem_nil  :
      𝓞.crAnF (ofStateAlgebra (timeOrder (ofList []))) = ∑ (c : ContractionsNat [].length),
      (c.sign [] • c.timeContract 𝓞) *
      𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map [].get))) := by
  rw [timeOrder_ofList_nil]
  simp only [map_one, List.length_nil, Algebra.smul_mul_assoc]
  rw [sum_contractionsNat_nil, nil_zero_uncontractedList]
  simp only [List.map_nil]
  have h1 : ofStateList (𝓕 := 𝓕) [] = CrAnAlgebra.ofCrAnList [] := by simp
  rw [h1, normalOrder_ofCrAnList]
  simp [ContractionsNat.timeContract, nil, sign]

lemma timeOrder_eq_maxTimeField_mul_finset (φ : 𝓕.States) (φs : List 𝓕.States) :
    timeOrder (ofList (φ :: φs)) =
    𝓢(𝓕 |>ₛ maxTimeField φ φs, fieldStatOfFinset (eraseMaxTimeField φ φs).get
        (Finset.filter (fun x => (maxTimeFieldPosFin φ φs).succAbove x < maxTimeFieldPosFin φ φs) Finset.univ)) •
    StateAlgebra.ofState (maxTimeField φ φs) * timeOrder (ofList (eraseMaxTimeField φ φs)) := by
  rw [timeOrder_eq_maxTimeField_mul]
  congr 3
  apply FieldStatistic.ofList_perm
  have h1 : (φ :: φs) = (List.finRange (φ :: φs).length).map (φ :: φs).get := by
    exact Eq.symm (List.finRange_map_get (φ :: φs))
  nth_rewrite 1 [h1]
  simp [eraseMaxTimeField, insertionSortDropMinPos]
  rw [eraseIdx_get]
  rw [← List.map_take, ← List.map_map]
  refine List.Perm.map (φ :: φs).get ?_
  apply (List.perm_ext_iff_of_nodup _ _).mpr
  · intro i
    rw [mem_take_finrange]
    simp [maxTimeFieldPos]
    apply Iff.intro
    · intro hi
      have h2 := (maxTimeFieldPosFin φ φs).2
      simp  [eraseMaxTimeField, Nat.succ_eq_add_one, -Fin.is_lt, insertionSortDropMinPos, maxTimeFieldPosFin, insertionSortMinPosFin] at h2
      use ⟨i, by omega⟩
      apply And.intro
      · simp [Fin.succAbove, maxTimeFieldPosFin, insertionSortMinPosFin]
        rw [Fin.lt_def]
        split
        · simp
          omega
        · omega
      · simp [Fin.succAbove, maxTimeFieldPosFin, insertionSortMinPosFin, Fin.ext_iff]
        split
        · simp
        · simp_all [Fin.lt_def]
    · intro h
      obtain ⟨j, h1, h2⟩ := h
      subst h2
      simp [Fin.lt_def]
      exact h1
  · refine List.Sublist.nodup (List.take_sublist _ _) ?_
    exact List.nodup_finRange (φs.length + 1)
  · refine List.Nodup.map ?hf ?_
    refine Function.Injective.comp ?hf.hg ?hf.hf
    exact Fin.cast_injective (eraseIdx_length (φ :: φs) (insertionSortMinPos timeOrderProp φ φs))
    exact Fin.succAbove_right_injective
    exact
      Finset.sort_nodup (fun x1 x2 => x1 ≤ x2)
        (Finset.filter (fun x => (maxTimeFieldPosFin φ φs).succAbove x < maxTimeFieldPosFin φ φs)
          Finset.univ)

/-- Wick's theorem for time-ordered products of bosonic and fermionic fields. -/
theorem wicks_theorem : (φs : List 𝓕.States) →
      𝓞.crAnF (ofStateAlgebra (timeOrder (ofList φs))) = ∑ (c : ContractionsNat φs.length),
      (c.sign φs • c.timeContract 𝓞) * 𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map φs.get)))
  | [] =>  wicks_theorem_nil
  | φ :: φs => by
    have ih := wicks_theorem (eraseMaxTimeField φ φs)
    rw [timeOrder_eq_maxTimeField_mul_finset, map_mul, map_mul, ih, Finset.mul_sum]
    have h1 : φ :: φs = (eraseMaxTimeField φ φs).insertIdx (maxTimeFieldPosFin φ φs) (maxTimeField φ φs) := by
      simp [eraseMaxTimeField, insertionSortDropMinPos, maxTimeFieldPos, maxTimeField, insertionSortMin]
      erw [insertIdx_eraseIdx_fin]
    rw [wicks_theorem_congr h1]
    conv_rhs => rw [insertLift_sum]
    congr
    funext c
    have ht : sign (eraseMaxTimeField φ φs) c • (ContractionsNat.timeContract 𝓞 c).1 ∈ Subalgebra.center ℂ 𝓞.A := by
      refine Subalgebra.smul_mem (Subalgebra.center ℂ 𝓞.A) ?hx (sign (eraseMaxTimeField φ φs) c)
      exact (ContractionsNat.timeContract 𝓞 c).2
    rw [@Subalgebra.mem_center_iff] at ht
    rw [map_smul, map_smul, Algebra.smul_mul_assoc, ← mul_assoc, ht, mul_assoc,
      ← map_mul]
    have hx := mul_sum_contractions (𝓞 := 𝓞) (maxTimeField φ φs) (eraseMaxTimeField φ φs) (maxTimeFieldPosFin φ φs) c
    rw [ofStateAlgebra_ofState, hx]
    trans (1 : ℂ) •  ∑ k : Option { x // x ∈ c.uncontracted },
      sign (List.insertIdx (↑(maxTimeFieldPosFin φ φs)) (maxTimeField φ φs) (eraseMaxTimeField φ φs))
          (insertList (maxTimeField φ φs) (eraseMaxTimeField φ φs) c (maxTimeFieldPosFin φ φs) k) •
        ↑(ContractionsNat.timeContract 𝓞
            (insertList (maxTimeField φ φs) (eraseMaxTimeField φ φs) c (maxTimeFieldPosFin φ φs) k)) *
      𝓞.crAnF (normalOrder (ofStateList
        (List.map (List.insertIdx (↑(maxTimeFieldPosFin φ φs)) (maxTimeField φ φs) (eraseMaxTimeField φ φs)).get
        (insertList (maxTimeField φ φs) (eraseMaxTimeField φ φs) c (maxTimeFieldPosFin φ φs) k).uncontractedList)))
    swap
    · simp
    rw [smul_smul]
    simp [pairedSign_mul_self]
    · exact fun k =>  timeOrder_maxTimeField _ _ k
    · exact fun k =>  lt_maxTimeFieldPosFin_not_timeOrder _ _ k
termination_by φs => φs.length


end FieldStruct
