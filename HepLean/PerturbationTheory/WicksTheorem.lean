/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.Meta.Remark.Basic
/-!

# Wick's theorem

This file contrains the time-dependent version of Wick's theorem
for lists of fields containing both fermions and bosons.

Wick's theorem is related to Isserlis' theorem in mathematics.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification} {𝓞 : 𝓕.ProtoOperatorAlgebra}
open CrAnAlgebra
open ProtoOperatorAlgebra
open HepLean.List
open WickContraction
open FieldStatistic

/-!

## Normal order of uncontracted terms within proto-algebra.

-/

/--
Let `c` be a Wick Contraction for `φs := φ₀φ₁…φₙ`.
We have (roughly) `𝓝ᶠ([φsΛ ↩Λ φ i none]ᵘᶜ) = s • 𝓝ᶠ(φ :: [φsΛ]ᵘᶜ)`
Where `s` is the exchange sign for `φ` and the uncontracted fields in `φ₀φ₁…φᵢ₋₁`.
-/
lemma normalOrderF_uncontracted_none (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) :
    𝓞.crAnF (𝓝ᶠ([φsΛ ↩Λ φ i none]ᵘᶜ))
    = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, φsΛ.uncontracted.filter (fun x => i.succAbove x < i)⟩) •
    𝓞.crAnF 𝓝ᶠ(φ :: [φsΛ]ᵘᶜ) := by
  simp only [Nat.succ_eq_add_one, instCommGroup.eq_1]
  rw [crAnF_ofState_normalOrderF_insert φ [φsΛ]ᵘᶜ
    ⟨(φsΛ.uncontractedListOrderPos i), by simp [uncontractedListGet]⟩, smul_smul]
  trans (1 : ℂ) • 𝓞.crAnF (𝓝ᶠ(ofStateList [φsΛ ↩Λ φ i none]ᵘᶜ))
  · simp
  congr 1
  simp only [instCommGroup.eq_1, uncontractedListGet]
  rw [← List.map_take, take_uncontractedListOrderPos_eq_filter]
  have h1 : (𝓕 |>ₛ List.map φs.get (List.filter (fun x => decide (↑x < i.1)) φsΛ.uncontractedList))
        = 𝓕 |>ₛ ⟨φs.get, (φsΛ.uncontracted.filter (fun x => x.val < i.1))⟩ := by
      simp only [Nat.succ_eq_add_one, ofFinset]
      congr
      rw [uncontractedList_eq_sort]
      have hdup : (List.filter (fun x => decide (x.1 < i.1))
          (Finset.sort (fun x1 x2 => x1 ≤ x2) φsΛ.uncontracted)).Nodup := by
        exact List.Nodup.filter _ (Finset.sort_nodup (fun x1 x2 => x1 ≤ x2) φsΛ.uncontracted)
      have hsort : (List.filter (fun x => decide (x.1 < i.1))
          (Finset.sort (fun x1 x2 => x1 ≤ x2) φsΛ.uncontracted)).Sorted (· ≤ ·) := by
        exact List.Sorted.filter _ (Finset.sort_sorted (fun x1 x2 => x1 ≤ x2) φsΛ.uncontracted)
      rw [← (List.toFinset_sort (· ≤ ·) hdup).mpr hsort]
      congr
      ext a
      simp
  rw [h1]
  simp only [Nat.succ_eq_add_one]
  have h2 : (Finset.filter (fun x => x.1 < i.1) φsΛ.uncontracted) =
    (Finset.filter (fun x => i.succAbove x < i) φsΛ.uncontracted) := by
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
  rw [insertAndContract_uncontractedList_none_map]

/--
Let `c` be a Wick Contraction for `φ₀φ₁…φₙ`.
We have (roughly) `N(c ↩Λ φ i k).uncontractedList`
is equal to `N((c.uncontractedList).eraseIdx k')`
where `k'` is the position in `c.uncontractedList` corresponding to `k`.
-/
lemma normalOrderF_uncontracted_some (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) (k : φsΛ.uncontracted) :
    𝓞.crAnF 𝓝ᶠ([φsΛ ↩Λ φ i (some k)]ᵘᶜ)
    = 𝓞.crAnF 𝓝ᶠ((optionEraseZ [φsΛ]ᵘᶜ φ ((uncontractedStatesEquiv φs φsΛ) k))) := by
  simp only [Nat.succ_eq_add_one, insertAndContract, optionEraseZ, uncontractedStatesEquiv,
    Equiv.optionCongr_apply, Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply,
    Fin.coe_cast, uncontractedListGet]
  congr
  rw [congr_uncontractedList]
  erw [uncontractedList_extractEquiv_symm_some]
  simp only [Fin.coe_succAboveEmb, List.map_eraseIdx, List.map_map]
  congr
  conv_rhs => rw [get_eq_insertIdx_succAbove φ φs i]

/-!

## Wick terms

-/

remark wick_term_terminology := "
  Let `φsΛ` be a Wick contraction. We informally call the term
  `(φsΛ.sign • φsΛ.timeContract 𝓞) * 𝓞.crAnF 𝓝ᶠ([φsΛ]ᵘᶜ)` the Wick term
  associated with `φsΛ`. We do not make this a fully-fledge definition, as
  in most cases we want to consider slight modifications of this term."

/--
Let `φsΛ` be a Wick Contraction for `φs = φ₀φ₁…φₙ`. Then the wick-term of ` (φsΛ ↩Λ φ i none)`

```(φsΛ ↩Λ φ i none).sign • (φsΛ ↩Λ φ i none).timeContract 𝓞 * 𝓞.crAnF 𝓝ᶠ([φsΛ ↩Λ φ i none]ᵘᶜ)```

is equal to

`s • (φsΛ.sign • φsΛ.timeContract 𝓞 * 𝓞.crAnF 𝓝ᶠ(φ :: [φsΛ]ᵘᶜ))`

where `s` is the exchange sign of `φ` and the uncontracted fields in `φ₀φ₁…φᵢ₋₁`.

The proof of this result relies primarily on:
- `normalOrderF_uncontracted_none` which replaces `𝓝ᶠ([φsΛ ↩Λ φ i none]ᵘᶜ)` with
  `𝓝ᶠ(φ :: [φsΛ]ᵘᶜ)` up to a sign.
- `timeContract_insertAndContract_none` which replaces `(φsΛ ↩Λ φ i none).timeContract 𝓞` with
  `φsΛ.timeContract 𝓞`.
- `sign_insert_none` and `signInsertNone_eq_filterset` which are used to take account of
  signs.
-/
lemma wick_term_none_eq_wick_term_cons (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) :
    (φsΛ ↩Λ φ i none).sign • (φsΛ ↩Λ φ i none).timeContract 𝓞
    * 𝓞.crAnF 𝓝ᶠ([φsΛ ↩Λ φ i none]ᵘᶜ) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun k => i.succAbove k < i))⟩)
    • (φsΛ.sign • φsΛ.timeContract 𝓞 * 𝓞.crAnF 𝓝ᶠ(φ :: [φsΛ]ᵘᶜ)) := by
  by_cases hg : GradingCompliant φs φsΛ
  · rw [normalOrderF_uncontracted_none, sign_insert_none]
    simp only [Nat.succ_eq_add_one, timeContract_insertAndContract_none, instCommGroup.eq_1,
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
      have hx : φsΛ.getDual? a = none ↔ ¬ (φsΛ.getDual? a).isSome := by
        simp
      rw [hx]
      simp only [Bool.not_eq_true, Bool.eq_false_or_eq_true_self, true_and]
      intro h1 h2
      simp_all
  · simp only [Nat.succ_eq_add_one, timeContract_insertAndContract_none, Algebra.smul_mul_assoc,
    instCommGroup.eq_1]
    rw [timeContract_of_not_gradingCompliant]
    simp only [ZeroMemClass.coe_zero, zero_mul, smul_zero]
    exact hg

/--
Let `c` be a Wick Contraction for `φ₀φ₁…φₙ`.
This lemma states that
`(c.sign • c.timeContract 𝓞) * N(c.uncontracted)`
for `c` equal to `c ↩Λ φ i (some k)` is equal to that for just `c`
mulitiplied by the exchange sign of `φ` and `φ₀φ₁…φᵢ₋₁`.
-/
lemma wick_term_some_eq_wick_term_optionEraseZ (φ : 𝓕.States) (φs : List 𝓕.States)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) (k : φsΛ.uncontracted)
    (hlt : ∀ (k : Fin φs.length), timeOrderRel φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬ timeOrderRel φs[k] φ) :
    (φsΛ ↩Λ φ i (some k)).sign • (φsΛ ↩Λ φ i (some k)).timeContract 𝓞
      * 𝓞.crAnF 𝓝ᶠ([φsΛ ↩Λ φ i (some k)]ᵘᶜ) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => i.succAbove x < i))⟩)
    • (φsΛ.sign • (𝓞.contractStateAtIndex φ [φsΛ]ᵘᶜ
      ((uncontractedStatesEquiv φs φsΛ) (some k)) * φsΛ.timeContract 𝓞)
    * 𝓞.crAnF 𝓝ᶠ((optionEraseZ [φsΛ]ᵘᶜ φ (uncontractedStatesEquiv φs φsΛ k)))) := by
  by_cases hg : GradingCompliant φs φsΛ ∧ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[k.1])
  · by_cases hk : i.succAbove k < i
    · rw [WickContraction.timeConract_insertAndContract_some_eq_mul_contractStateAtIndex_not_lt]
      swap
      · exact hn _ hk
      rw [normalOrderF_uncontracted_some, sign_insert_some]
      simp only [instCommGroup.eq_1, smul_smul, Algebra.smul_mul_assoc]
      congr 1
      rw [mul_assoc, mul_comm (sign φs φsΛ), ← mul_assoc]
      congr 1
      exact signInsertSome_mul_filter_contracted_of_lt φ φs φsΛ i k hk hg
      · omega
    · have hik : i.succAbove ↑k ≠ i := Fin.succAbove_ne i ↑k
      rw [WickContraction.timeConract_insertAndContract_some_eq_mul_contractStateAtIndex_lt]
      swap
      · exact hlt _
      rw [normalOrderF_uncontracted_some]
      rw [sign_insert_some]
      simp only [instCommGroup.eq_1, smul_smul, Algebra.smul_mul_assoc]
      congr 1
      rw [mul_assoc, mul_comm (sign φs φsΛ), ← mul_assoc]
      congr 1
      exact signInsertSome_mul_filter_contracted_of_not_lt φ φs φsΛ i k hk hg
      · omega
  · rw [timeConract_insertAndContract_some]
    simp only [Fin.getElem_fin, not_and] at hg
    by_cases hg' : GradingCompliant φs φsΛ
    · have hg := hg hg'
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, Algebra.smul_mul_assoc,
        instCommGroup.eq_1, contractStateAtIndex, uncontractedStatesEquiv, Equiv.optionCongr_apply,
        Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply, Fin.coe_cast,
        List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem,
        uncontractedListGet]
      by_cases h1 : i < i.succAbove ↑k
      · simp only [h1, ↓reduceIte, MulMemClass.coe_mul]
        rw [timeContract_zero_of_diff_grade]
        simp only [zero_mul, smul_zero]
        rw [crAnF_superCommuteF_anPart_ofState_diff_grade_zero]
        simp only [zero_mul, smul_zero]
        exact hg
        exact hg
      · simp only [h1, ↓reduceIte, MulMemClass.coe_mul]
        rw [timeContract_zero_of_diff_grade]
        simp only [zero_mul, smul_zero]
        rw [crAnF_superCommuteF_anPart_ofState_diff_grade_zero]
        simp only [zero_mul, smul_zero]
        exact hg
        exact fun a => hg (id (Eq.symm a))
    · rw [timeContract_of_not_gradingCompliant]
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, mul_zero, ZeroMemClass.coe_zero, smul_zero,
        zero_mul, instCommGroup.eq_1]
      exact hg'

/--
Given a Wick contraction `φsΛ` of `φs = φ₀φ₁…φₙ` and an `i`, we have that
`(φsΛ.sign • φsΛ.timeContract 𝓞) * 𝓞.crAnF (φ * 𝓝ᶠ([φsΛ]ᵘᶜ))`
is equal to the product of
- the exchange sign of `φ` and `φ₀φ₁…φᵢ₋₁`,
- the sum of `((φsΛ ↩Λ φ i k).sign • (φsΛ ↩Λ φ i k).timeContract 𝓞) * 𝓞.crAnF 𝓝ᶠ([φsΛ ↩Λ φ i k]ᵘᶜ)`
  over all `k` in `Option φsΛ.uncontracted`.

The proof of this result primarily depends on
- `crAnF_ofState_mul_normalOrderF_ofStatesList_eq_sum` to rewrite `𝓞.crAnF (φ * 𝓝ᶠ([φsΛ]ᵘᶜ))`
- `wick_term_none_eq_wick_term_cons`
- `wick_term_some_eq_wick_term_optionEraseZ`
-/
lemma wick_term_cons_eq_sum_wick_term (φ : 𝓕.States) (φs : List 𝓕.States) (i : Fin φs.length.succ)
    (φsΛ : WickContraction φs.length) (hlt : ∀ (k : Fin φs.length), timeOrderRel φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬timeOrderRel φs[k] φ) :
    (φsΛ.sign • φsΛ.timeContract 𝓞) * 𝓞.crAnF ((CrAnAlgebra.ofState φ) * 𝓝ᶠ([φsΛ]ᵘᶜ)) =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => i.succAbove x < i))⟩) •
    ∑ (k : Option φsΛ.uncontracted), ((φsΛ ↩Λ φ i k).sign •
    (φsΛ ↩Λ φ i k).timeContract 𝓞 * 𝓞.crAnF (𝓝ᶠ([φsΛ ↩Λ φ i k]ᵘᶜ))) := by
  rw [crAnF_ofState_mul_normalOrderF_ofStatesList_eq_sum, Finset.mul_sum,
    uncontractedStatesEquiv_list_sum, Finset.smul_sum]
  simp only [instCommGroup.eq_1, Nat.succ_eq_add_one]
  congr 1
  funext n
  match n with
  | none =>
    rw [wick_term_none_eq_wick_term_cons]
    simp only [contractStateAtIndex, uncontractedStatesEquiv, Equiv.optionCongr_apply,
      Equiv.coe_trans, Option.map_none', one_mul, Algebra.smul_mul_assoc, instCommGroup.eq_1,
      smul_smul]
    congr 1
    rw [← mul_assoc, exchangeSign_mul_self]
    simp
  | some n =>
    rw [wick_term_some_eq_wick_term_optionEraseZ _ _ _ _ _
      (fun k => hlt k) (fun k a => hn k a)]
    simp only [uncontractedStatesEquiv, Equiv.optionCongr_apply, Equiv.coe_trans, Option.map_some',
      Function.comp_apply, finCongr_apply, Algebra.smul_mul_assoc, instCommGroup.eq_1, smul_smul]
    congr 1
    · rw [← mul_assoc, exchangeSign_mul_self]
      rw [one_mul]
    · rw [← mul_assoc]
      congr 1
      have ht := (WickContraction.timeContract 𝓞 φsΛ).prop
      rw [@Subalgebra.mem_center_iff] at ht
      rw [ht]

/-!

## Wick's theorem

-/

/-- Wick's theorem for the empty list. -/
lemma wicks_theorem_nil :
    𝓞.crAnF (𝓣ᶠ(ofStateList [])) = ∑ (nilΛ : WickContraction [].length),
    (nilΛ.sign • nilΛ.timeContract 𝓞) * 𝓞.crAnF 𝓝ᶠ([nilΛ]ᵘᶜ) := by
  rw [timeOrder_ofStateList_nil]
  simp only [map_one, List.length_nil, Algebra.smul_mul_assoc]
  rw [sum_WickContraction_nil, uncontractedListGet, nil_zero_uncontractedList]
  simp only [List.map_nil]
  have h1 : ofStateList (𝓕 := 𝓕) [] = CrAnAlgebra.ofCrAnList [] := by simp
  rw [h1, normalOrderF_ofCrAnList]
  simp [WickContraction.timeContract, empty, sign]

lemma wicks_theorem_congr {φs φs' : List 𝓕.States} (h : φs = φs') :
    ∑ (φsΛ : WickContraction φs.length), (φsΛ.sign • φsΛ.timeContract 𝓞) *
      𝓞.crAnF 𝓝ᶠ([φsΛ]ᵘᶜ)
    = ∑ (φs'Λ : WickContraction φs'.length), (φs'Λ.sign • φs'Λ.timeContract 𝓞) *
      𝓞.crAnF 𝓝ᶠ([φs'Λ]ᵘᶜ) := by
  subst h
  simp

remark wicks_theorem_context := "
  Wick's theorem is one of the most important results in perturbative quantum field theory.
  It expresses a time-ordered product of fields as a sum of terms consisting of
  time-contractions of pairs of fields multiplied by the normal-ordered product of
  the remaining fields. Wick's theorem is also the precursor to the diagrammatic
  approach to quantum field theory called Feynman diagrams."

/-- Wick's theorem for time-ordered products of bosonic and fermionic fields.
  The time ordered product `T(φ₀φ₁…φₙ)` is equal to the sum of terms,
  for all possible Wick contractions `c` of the list of fields `φs := φ₀φ₁…φₙ`, given by
  the multiple of:
- The sign corresponding to the number of fermionic-fermionic exchanges one must do
    to put elements in contracted pairs of `c` next to each other.
- The product of time-contractions of the contracted pairs of `c`.
- The normal-ordering of the uncontracted fields in `c`.
-/
theorem wicks_theorem : (φs : List 𝓕.States) → 𝓞.crAnF (𝓣ᶠ(ofStateList φs)) =
    ∑ (φsΛ : WickContraction φs.length), (φsΛ.sign • φsΛ.timeContract 𝓞) * 𝓞.crAnF 𝓝ᶠ([φsΛ]ᵘᶜ)
  | [] => wicks_theorem_nil
  | φ :: φs => by
    have ih := wicks_theorem (eraseMaxTimeField φ φs)
    rw [timeOrder_eq_maxTimeField_mul_finset, map_mul, ih, Finset.mul_sum]
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
    rw [map_smul, Algebra.smul_mul_assoc, ← mul_assoc, ht, mul_assoc, ← map_mul]
    rw [wick_term_cons_eq_sum_wick_term (𝓞 := 𝓞)
      (maxTimeField φ φs) (eraseMaxTimeField φ φs) (maxTimeFieldPosFin φ φs) c]
    trans (1 : ℂ) • ∑ k : Option { x // x ∈ c.uncontracted }, sign
      (List.insertIdx (↑(maxTimeFieldPosFin φ φs)) (maxTimeField φ φs) (eraseMaxTimeField φ φs))
      (c ↩Λ (maxTimeField φ φs) (maxTimeFieldPosFin φ φs) k) •
      ↑((c ↩Λ (maxTimeField φ φs) (maxTimeFieldPosFin φ φs) k).timeContract 𝓞) *
      𝓞.crAnF 𝓝ᶠ(ofStateList (List.map (List.insertIdx (↑(maxTimeFieldPosFin φ φs))
      (maxTimeField φ φs) (eraseMaxTimeField φ φs)).get
        (c ↩Λ (maxTimeField φ φs) (maxTimeFieldPosFin φ φs) k).uncontractedList))
    swap
    · simp [uncontractedListGet]
    rw [smul_smul]
    simp only [instCommGroup.eq_1, exchangeSign_mul_self, Nat.succ_eq_add_one,
      Algebra.smul_mul_assoc, Fintype.sum_option, timeContract_insertAndContract_none,
      Finset.univ_eq_attach, smul_add, one_smul, uncontractedListGet]
    · exact fun k => timeOrder_maxTimeField _ _ k
    · exact fun k => lt_maxTimeFieldPosFin_not_timeOrder _ _ k
termination_by φs => φs.length

end FieldSpecification
