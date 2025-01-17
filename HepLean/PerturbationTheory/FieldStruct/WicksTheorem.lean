/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.Contractions
import HepLean.PerturbationTheory.FieldStruct.TimeOrder
import HepLean.PerturbationTheory.FieldStruct.Contractions.Sign
import HepLean.PerturbationTheory.FieldStruct.Contractions.TimeContract
import HepLean.Mathematics.List.InsertIdx
/-!

# Wick's theorem




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
      rw [signInsertSome]
      rw [signInsertSomeProd_eq_finset, signInsertSomeCoef_eq_finset]
      rw [if_neg]
      rw [← map_mul, ← map_mul]
      congr 1
      rw [mul_eq_iff_eq_mul]
      rw [fieldStatOfFinset_union_disjoint]
      swap
      · rw [Finset.disjoint_filter]
        intro j _ h
        simp
        intro h1
        use h1
        intro hj
        omega
      trans fieldStatOfFinset φs.get (Finset.filter (fun x =>
          (↑k < x ∧ i.succAbove x < i ∧ (c.getDual? x = none ∨
          ∀ (h : (c.getDual? x).isSome = true), ↑k < (c.getDual? x).get h))
          ∨ ((c.getDual? x).isSome = true ∧
          ∀ (h : (c.getDual? x).isSome = true), x < ↑k ∧
          (i.succAbove x < i ∧ i < i.succAbove ((c.getDual? x).get h) ∨
          ↑k < (c.getDual? x).get h ∧ ¬i.succAbove x < i))) Finset.univ)
      · congr
        ext j
        simp
      rw [fieldStatOfFinset_union]
      rw [← mul_eq_one_iff]
      rw [fieldStatOfFinset_union]
      simp
      apply fieldStatOfFinset_eq_one_of_isGradedObeying
      · exact hg.1
      /- the getDual? is none case-/
      · intro j hn
        simp [hn, uncontracted]
        intro h
        rcases h with h | h
        · simp [h]
        · simp [h, h.2]
          refine And.intro ?_ (And.intro ?_ h.2)
          · by_contra hkj
            simp at hkj
            have h2 := h.2 hkj
            apply Fin.ne_succAbove i j
            have hij : i.succAbove j ≤ i.succAbove k.1 :=
              Fin.succAbove_le_succAbove_iff.mpr hkj
            omega
          · have h1' := h.1
            rcases h1' with h1' | h1'
            · have hl := h.2 h1'
              have hij : i.succAbove j ≤ i.succAbove k.1 :=
              Fin.succAbove_le_succAbove_iff.mpr h1'
              by_contra hn
              apply Fin.ne_succAbove i j
              omega
            · exact h1'
      /- the getDual? is some case-/
      · intro j hj
        have hn : ¬ c.getDual? j = none := by exact Option.isSome_iff_ne_none.mp hj
        simp [hj, uncontracted, hn]
        intro h1 h2
        have hijsucc : i.succAbove j ≠ i := by exact Fin.succAbove_ne i j
        have hijsucc' : i.succAbove ((c.getDual? j).get hj) ≠ i := by exact Fin.succAbove_ne i _
        have hkneqj : ↑k ≠ j := by
          by_contra hkj
          have hl := congrArg (fun x => (c.getDual? x).isSome) hkj
          simp at hl
          have hk := k.prop
          simp  [uncontracted, - Finset.coe_mem] at hk
          simp_all
        have hkneqgetdual : k.1 ≠ ( c.getDual? j).get hj := by
          by_contra hkj
          have hl := congrArg (fun x => (c.getDual? x).isSome) hkj
          simp at hl
          have hk := k.prop
          simp [uncontracted, - Finset.coe_mem] at hk
          simp_all
        by_cases hik : ↑k < j
        · have hn : ¬ j < ↑k := by omega
          simp [hik, hn] at h1 h2 ⊢
          have hir :  i.succAbove j < i := by
            rcases h1 with h1 | h1
            · simp [h1]
            · simp [h1]
          have hirn : ¬  i < i.succAbove j  := by omega
          simp [hir, hirn] at h1 h2
          have hnkdual : ¬ ↑k < (c.getDual? j).get hj := by
            by_contra hn
            have h2 := h2 hn
            apply Fin.ne_succAbove i j
            omega
          simp [hnkdual] at h2 ⊢
          have hnkdual :  (c.getDual? j).get hj < ↑k := by omega
          have hi : i.succAbove ((c.getDual? j).get hj) < i.succAbove k := by
            rw [@Fin.succAbove_lt_succAbove_iff]
            omega
          simp [hnkdual, hir]
          apply And.intro
          · apply Or.inr
            omega
          · intro h
            omega
        · have ht :  j < ↑k  := by omega
          have ht' : i.succAbove j < i.succAbove k := by
            rw [@Fin.succAbove_lt_succAbove_iff]
            omega
          simp [hik, ht] at h1 h2 ⊢
          by_cases hik : i.succAbove j < i
          · simp_all [hik]
            have hn : ¬ i ≤ i.succAbove j := by omega
            simp_all [hn]
            apply And.intro
            · apply Or.inr
              omega
            · intro h1 h2 h3
              omega
          · simp_all [hik]
            have hl : i < i.succAbove j := by omega
            simp [hl]
            omega
      · omega
      · exact hg.2
      · exact hg.2
      · exact hg.1
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
      rw [signInsertSome]
      rw [signInsertSomeProd_eq_finset, signInsertSomeCoef_eq_finset]
      rw [if_pos (by omega)]
      rw [← map_mul, ← map_mul]
      congr 1
      rw [mul_eq_iff_eq_mul]
      rw [fieldStatOfFinset_union, fieldStatOfFinset_union]
      apply (mul_eq_one_iff _ _).mp
      rw [fieldStatOfFinset_union]
      simp
      apply fieldStatOfFinset_eq_one_of_isGradedObeying
      · exact hg.1
      · intro j hj
        have hijsucc : i.succAbove j ≠ i := by exact Fin.succAbove_ne i j
        simp [hj, uncontracted]
        intro h
        have hij : i < i.succAbove j := by
          rcases h with h | h
          · exact h.1
          · have h1 := h.1
            rcases h1 with h1 | h1
            · have h2 := h.2 h1
              omega
            · have h2 := h.2.mt (by omega)
              simp at h2
              have hik : i.succAbove k.1 ≤ i.succAbove j := by
                rw [Fin.succAbove_le_succAbove_iff]
                omega
              omega
        simp [hij] at h ⊢
        have hjk :  j < ↑k := by
          rcases h with h | h
          · exact h
          · have h1 := h.1
            rcases h1 with h1 | h1
            · omega
            · omega
        simp [hjk]
        omega
      · intro j hj
        have hn : ¬ c.getDual? j = none := by exact Option.isSome_iff_ne_none.mp hj
        have hijSuc :  i.succAbove j ≠ i := by exact Fin.succAbove_ne i j
        have hkneqj : ↑k ≠ j := by
          by_contra hkj
          have hl := congrArg (fun x => (c.getDual? x).isSome) hkj
          simp at hl
          have hk := k.prop
          simp  [uncontracted, - Finset.coe_mem] at hk
          simp_all
        have hkneqgetdual : k.1 ≠ ( c.getDual? j).get hj := by
          by_contra hkj
          have hl := congrArg (fun x => (c.getDual? x).isSome) hkj
          simp at hl
          have hk := k.prop
          simp [uncontracted, - Finset.coe_mem] at hk
          simp_all
        simp [hj, uncontracted, hn]
        by_cases hik : ↑k < j
        · have hikn : ¬ j < k.1 := by omega
          have hksucc : i.succAbove k.1 < i.succAbove j := by
            rw [Fin.succAbove_lt_succAbove_iff]
            omega
          have hkn : i < i.succAbove j := by omega
          have hl : ¬ i.succAbove j < i := by omega
          simp [hik, hikn, hkn, hl]
        · have hikn : j < k.1 := by omega
          have hksucc : i.succAbove j < i.succAbove k.1 := by
            rw [Fin.succAbove_lt_succAbove_iff]
            omega
          simp [hik, hikn]
          by_cases hij: i < i.succAbove j
          · simp [hij]
            have hijn : ¬ i.succAbove j < i := by omega
            simp [hijn]
            have hijle :  i ≤ i.succAbove j := by omega
            simp [hijle]
            intro h1 h2
            apply And.intro
            · rcases h1 with h1 | h1
              · simp [h1]
                have h2 := h2 h1
                apply Or.inl
                omega
              · apply Or.inl
                have hi : i.succAbove k.1 < i.succAbove ((c.getDual? j).get hj) := by
                  rw [Fin.succAbove_lt_succAbove_iff]
                  omega
                apply And.intro
                · apply Or.inr
                  apply And.intro
                  · omega
                  · omega
                · omega
            · intro h3 h4
              omega
          · simp [hij]
            have hijn : i.succAbove j < i := by omega
            have hijn' : ¬ i ≤ i.succAbove j := by omega
            simp [hijn, hijn']
            intro h
            have hij : i.succAbove ((c.getDual? j).get hj) ≠ i :=  Fin.succAbove_ne i ((c.getDual? j).get hj)
            exact lt_of_le_of_ne h hij
      · exact hg.2
      · exact hg.2
      · exact hg.1
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
  rw [crAnF_ofState_mul_normalOrder_ofStatesList_eq_sum]
  rw [Finset.mul_sum]
  rw [uncontractedStatesEquiv_list_sum]
  rw [Finset.smul_sum]
  simp only [Finset.univ_eq_attach, instCommGroup.eq_1,
    Nat.succ_eq_add_one, timeContract_insertList_none]
  congr 1
  funext n
  match n with
  | none =>
    rw [sign_timeContract_normalOrder_insertList_none]
    simp [smul_smul, contractMemList, uncontractedStatesEquiv]
    congr 1
    rw [← mul_assoc]
    rw [pairedSign_mul_self]
    simp
  | some n =>
    rw [sign_timeContract_normalOrder_insertList_some]
    simp [smul_smul, uncontractedStatesEquiv]
    congr 1
    rw [← mul_assoc]
    rw [pairedSign_mul_self]
    simp
    rw [← mul_assoc]
    congr 1
    have ht := (ContractionsNat.timeContract 𝓞 c).prop
    rw [@Subalgebra.mem_center_iff] at ht
    rw [ht]
    exact fun k => hlt k
    exact fun k a => hn k a

lemma wicks_theorem_congr {φs φs' : List 𝓕.States} (h : φs = φs'):
    ∑ (c : ContractionsNat φs.length),
      (c.sign • c.timeContract 𝓞) * 𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map φs.get)))
    = ∑ (c : ContractionsNat φs'.length),
       (c.sign • c.timeContract 𝓞) * 𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map φs'.get))) := by
  subst h
  simp


lemma wicks_theorem_nil  :
      𝓞.crAnF (ofStateAlgebra (timeOrder (ofList []))) = ∑ (c : ContractionsNat [].length),
      (c.sign [] • c.timeContract 𝓞) *
      𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map [].get))) := by
  rw [timeOrder_ofList_nil]
  simp
  rw [sum_contractionsNat_nil]
  rw [nil_zero_uncontractedList]
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

theorem wicks_theorem  : (φs : List 𝓕.States) →
      𝓞.crAnF (ofStateAlgebra (timeOrder (ofList φs))) = ∑ (c : ContractionsNat φs.length),
      (c.sign φs • c.timeContract 𝓞) * 𝓞.crAnF (normalOrder (ofStateList (c.uncontractedList.map φs.get)))
  | [] =>  wicks_theorem_nil
  | φ :: φs => by
    have ih := wicks_theorem (eraseMaxTimeField φ φs)
    rw [timeOrder_eq_maxTimeField_mul_finset]
    rw [map_mul, map_mul, ih]
    rw [Finset.mul_sum]
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
