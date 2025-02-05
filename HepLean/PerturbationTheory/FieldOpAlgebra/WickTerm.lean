/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.Sign.Basic
import HepLean.PerturbationTheory.WickContraction.Sign.InsertNone
import HepLean.PerturbationTheory.WickContraction.Sign.InsertSome
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.FieldOpAlgebra.NormalOrder.WickContractions
/-!

# Wick term

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra
open FieldStatistic
noncomputable section

/-- For a Wick contraction `φsΛ`, we define `wickTerm φsΛ` to be the element of `𝓕.FieldOpAlgebra`
  given by `φsΛ.sign • φsΛ.timeContract * 𝓝([φsΛ]ᵘᶜ)`. -/
def wickTerm {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) : 𝓕.FieldOpAlgebra :=
  φsΛ.sign • φsΛ.timeContract * 𝓝(ofFieldOpList [φsΛ]ᵘᶜ)

@[simp]
lemma wickTerm_empty_nil  :
    wickTerm (empty (n := ([] : List 𝓕.FieldOp).length)) = 1 := by
  rw [wickTerm]
  simp [sign_empty]

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
lemma wickTerm_insert_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) :
    (φsΛ ↩Λ φ i none).wickTerm =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun k => i.succAbove k < i))⟩)
    • (φsΛ.sign • φsΛ.timeContract * 𝓝(ofFieldOpList (φ :: [φsΛ]ᵘᶜ))) := by
  rw [wickTerm]
  by_cases hg : GradingCompliant φs φsΛ
  · rw [normalOrder_uncontracted_none, sign_insert_none  _ _ _ _ hg]
    simp only [Nat.succ_eq_add_one, timeContract_insertAndContract_none, instCommGroup.eq_1,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
    congr 1
    rw [← mul_assoc]
    congr 1
    rw [← map_mul]
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
lemma wickTerm_insert_some (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (i : Fin φs.length.succ) (φsΛ : WickContraction φs.length) (k : φsΛ.uncontracted)
    (hlt : ∀ (k : Fin φs.length), timeOrderRel φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬ timeOrderRel φs[k] φ) :
    (φsΛ ↩Λ φ i (some k)).wickTerm =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => i.succAbove x < i))⟩)
    • (φsΛ.sign • (contractStateAtIndex φ [φsΛ]ᵘᶜ
      ((uncontractedFieldOpEquiv φs φsΛ) (some k)) * φsΛ.timeContract)
    * 𝓝(ofFieldOpList (optionEraseZ [φsΛ]ᵘᶜ φ (uncontractedFieldOpEquiv φs φsΛ k)))) := by
  rw [wickTerm]
  by_cases hg : GradingCompliant φs φsΛ ∧ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φs[k.1])
  · by_cases hk : i.succAbove k < i
    · rw [WickContraction.timeContract_insertAndContract_some_eq_mul_contractStateAtIndex_not_lt]
      swap
      · exact hn _ hk
      · rw [normalOrder_uncontracted_some, sign_insert_some_of_lt φ φs φsΛ i k hk hg]
        simp only [instCommGroup.eq_1, smul_smul, Algebra.smul_mul_assoc]
        congr 1
        rw [mul_assoc, mul_assoc, mul_comm, mul_assoc, mul_assoc]
        simp
      · omega
    · have hik : i.succAbove ↑k ≠ i := Fin.succAbove_ne i ↑k
      rw [timeContract_insertAndContract_some_eq_mul_contractStateAtIndex_lt]
      swap
      · exact hlt _
      · rw [normalOrder_uncontracted_some]
        rw [sign_insert_some_of_not_lt φ φs φsΛ i k hk hg]
        simp only [instCommGroup.eq_1, smul_smul, Algebra.smul_mul_assoc]
        congr 1
        rw [mul_assoc, mul_assoc, mul_comm, mul_assoc, mul_assoc]
        simp
      · omega
  · rw [timeContract_insertAndContract_some]
    simp only [Fin.getElem_fin, not_and] at hg
    by_cases hg' : GradingCompliant φs φsΛ
    · have hg := hg hg'
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, Algebra.smul_mul_assoc,
        instCommGroup.eq_1, contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
        Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply, Fin.coe_cast,
        List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem,
        uncontractedListGet]
      by_cases h1 : i < i.succAbove ↑k
      · simp only [h1, ↓reduceIte, MulMemClass.coe_mul]
        rw [timeContract_zero_of_diff_grade]
        simp only [zero_mul, smul_zero]
        rw [superCommute_anPart_ofFieldOpF_diff_grade_zero]
        simp only [zero_mul, smul_zero]
        exact hg
        exact hg
      · simp only [h1, ↓reduceIte, MulMemClass.coe_mul]
        rw [timeContract_zero_of_diff_grade]
        simp only [zero_mul, smul_zero]
        rw [superCommute_anPart_ofFieldOpF_diff_grade_zero]
        simp only [zero_mul, smul_zero]
        exact hg
        exact fun a => hg (id (Eq.symm a))
    · rw [timeContract_of_not_gradingCompliant]
      simp only [Nat.succ_eq_add_one, Fin.getElem_fin, mul_zero, ZeroMemClass.coe_zero, smul_zero,
        zero_mul, instCommGroup.eq_1]
      exact hg'

/--
Let `φsΛ` be a Wick contraction for `φs = φ₀φ₁…φₙ`. Let `φ` be a field with time
greater then or equal to all the fields in `φs`. Let `i` be a in `Fin φs.length.succ` such that
all files in `φ₀…φᵢ₋₁` have time strictly less then `φ`. Then
`φ * φsΛ.wickTerm = 𝓢(φ, φ₀…φᵢ₋₁) • ∑ k, (φsΛ ↩Λ φ i k).wickTerm`
where the sum is over all `k` in `Option φsΛ.uncontracted` (so either `none` or `some k`).

The proof of proceeds as follows:
- `ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum` is used to expand  `φ 𝓝([φsΛ]ᵘᶜ)` as
  a sum over `k` in `Option φsΛ.uncontracted` of terms involving `[φ, φs[k]]` etc.
- Then `wickTerm_insert_none` and `wickTerm_insert_some` are used to equate terms.
-/
lemma mul_wickTerm_eq_sum (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) (i : Fin φs.length.succ)
    (φsΛ : WickContraction φs.length) (hlt : ∀ (k : Fin φs.length), timeOrderRel φ φs[k])
    (hn : ∀ (k : Fin φs.length), i.succAbove k < i → ¬timeOrderRel φs[k] φ) :
    ofFieldOp φ * φsΛ.wickTerm =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (Finset.univ.filter (fun x => i.succAbove x < i))⟩) •
    ∑ (k : Option φsΛ.uncontracted), (φsΛ ↩Λ φ i k).wickTerm := by
  trans (φsΛ.sign • φsΛ.timeContract) * ((ofFieldOp φ) * 𝓝(ofFieldOpList [φsΛ]ᵘᶜ))
  · have ht := Subalgebra.mem_center_iff.mp (Subalgebra.smul_mem (Subalgebra.center ℂ _)
      (WickContraction.timeContract φsΛ).2 (φsΛ.sign))
    rw [wickTerm]
    rw [← mul_assoc, ht, mul_assoc]
  rw [ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum, Finset.mul_sum,
    uncontractedFieldOpEquiv_list_sum, Finset.smul_sum]
  simp only [instCommGroup.eq_1, Nat.succ_eq_add_one]
  congr 1
  funext n
  match n with
  | none =>
    rw [wickTerm_insert_none]
    simp only [contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
      Equiv.coe_trans, Option.map_none', one_mul, Algebra.smul_mul_assoc, instCommGroup.eq_1,
      smul_smul]
    congr 1
    rw [← mul_assoc, exchangeSign_mul_self]
    simp
  | some n =>
    rw [wickTerm_insert_some _ _ _ _ _
      (fun k => hlt k) (fun k a => hn k a)]
    simp only [uncontractedFieldOpEquiv, Equiv.optionCongr_apply, Equiv.coe_trans, Option.map_some',
      Function.comp_apply, finCongr_apply, Algebra.smul_mul_assoc, instCommGroup.eq_1, smul_smul]
    congr 1
    · rw [← mul_assoc, exchangeSign_mul_self]
      rw [one_mul]
    · rw [← mul_assoc]
      congr 1
      have ht := (WickContraction.timeContract φsΛ).prop
      rw [@Subalgebra.mem_center_iff] at ht
      rw [ht]

end
end WickContraction
