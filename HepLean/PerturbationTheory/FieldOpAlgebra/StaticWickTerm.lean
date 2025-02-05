/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpAlgebra.NormalOrder.WickContractions
import HepLean.PerturbationTheory.WickContraction.Sign.InsertNone
import HepLean.PerturbationTheory.WickContraction.Sign.InsertSome
import HepLean.PerturbationTheory.WickContraction.StaticContract
/-!

# Static Wick's terms

-/


open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra
open FieldStatistic
noncomputable section

/-- For a Wick contraction `φsΛ`, we define `staticWickTerm φsΛ` to be the element of
  `𝓕.FieldOpAlgebra` given by `φsΛ.sign • φsΛ.staticContract * 𝓝([φsΛ]ᵘᶜ)`. -/
def staticWickTerm {φs : List 𝓕.FieldOp} (φsΛ : WickContraction φs.length) : 𝓕.FieldOpAlgebra :=
  φsΛ.sign • φsΛ.staticContract * 𝓝(ofFieldOpList [φsΛ]ᵘᶜ)

@[simp]
lemma staticWickTerm_empty_nil  :
    staticWickTerm (empty (n := ([] : List 𝓕.FieldOp).length)) = 1 := by
  rw [staticWickTerm, uncontractedListGet, nil_zero_uncontractedList]
  simp [sign, empty, staticContract]

lemma staticWickTerm_insert_zero_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) :
    (φsΛ ↩Λ φ 0 none).staticWickTerm =
    φsΛ.sign • φsΛ.staticContract * 𝓝(ofFieldOpList (φ :: [φsΛ]ᵘᶜ)) := by
  symm
  erw [staticWickTerm, sign_insert_none_zero]
  simp only [staticContract_insertAndContract_none, insertAndContract_uncontractedList_none_zero,
    Algebra.smul_mul_assoc]

lemma staticWickTerm_insert_zero_some (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (k : { x // x ∈ φsΛ.uncontracted }) :
    (φsΛ ↩Λ φ 0 k).staticWickTerm =
    sign φs φsΛ • (↑φsΛ.staticContract *
    (contractStateAtIndex φ [φsΛ]ᵘᶜ ((uncontractedFieldOpEquiv φs φsΛ) (some k)) *
    𝓝(ofFieldOpList (optionEraseZ [φsΛ]ᵘᶜ φ (uncontractedFieldOpEquiv φs φsΛ k))))) := by
  symm
  rw [staticWickTerm, normalOrder_uncontracted_some]
  simp only [← mul_assoc]
  rw [← smul_mul_assoc]
  congr 1
  rw [staticContract_insertAndContract_some_eq_mul_contractStateAtIndex_lt]
  swap
  · simp
  rw [smul_smul]
  by_cases hn : GradingCompliant φs φsΛ ∧ (𝓕|>ₛφ) = (𝓕|>ₛ φs[k.1])
  · congr 1
    swap
    · have h1 := φsΛ.staticContract.2
      rw [@Subalgebra.mem_center_iff] at h1
      rw [h1]
    erw [sign_insert_some]
    rw [mul_assoc, mul_comm φsΛ.sign, ← mul_assoc]
    rw [signInsertSome_mul_filter_contracted_of_not_lt]
    simp only [instCommGroup.eq_1, Fin.zero_succAbove, Fin.not_lt_zero, Finset.filter_False,
      ofFinset_empty, map_one, one_mul]
    simp only [Fin.zero_succAbove, Fin.not_lt_zero, not_false_eq_true]
    exact hn
  · simp only [Fin.getElem_fin, not_and] at hn
    by_cases h0 : ¬ GradingCompliant φs φsΛ
    · rw [staticContract_of_not_gradingCompliant]
      simp only [ZeroMemClass.coe_zero, zero_mul, smul_zero, instCommGroup.eq_1, mul_zero]
      exact h0
    · simp_all only [Finset.mem_univ, not_not, instCommGroup.eq_1, forall_const]
      have h1 : contractStateAtIndex φ [φsΛ]ᵘᶜ (uncontractedFieldOpEquiv φs φsΛ k) = 0 := by
        simp only [contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
          Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply,
          instCommGroup.eq_1, Fin.coe_cast, Fin.getElem_fin, smul_eq_zero]
        right
        simp only [uncontractedListGet, List.getElem_map,
          uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem]
        rw [superCommute_anPart_ofFieldOpF_diff_grade_zero]
        exact hn
      rw [h1]
      simp

lemma mul_staticWickTerm_eq_sum (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) :
    ofFieldOp φ * φsΛ.staticWickTerm =
    ∑ (k : Option φsΛ.uncontracted), (φsΛ ↩Λ φ 0 k).staticWickTerm := by
  trans (φsΛ.sign • φsΛ.staticContract * (ofFieldOp φ * normalOrder (ofFieldOpList [φsΛ]ᵘᶜ)))
  · have ht := Subalgebra.mem_center_iff.mp (Subalgebra.smul_mem (Subalgebra.center ℂ _)
      (φsΛ.staticContract).2 φsΛ.sign)
    conv_rhs => rw [← mul_assoc, ← ht]
    simp [mul_assoc, staticWickTerm]
  rw [ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum]
  rw [Finset.mul_sum]
  rw [uncontractedFieldOpEquiv_list_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  match n with
  | none =>
    simp only [contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
      Equiv.coe_trans, Option.map_none', one_mul, Algebra.smul_mul_assoc, Nat.succ_eq_add_one,
      Fin.zero_eta, Fin.val_zero, List.insertIdx_zero, staticContract_insertAndContract_none,
      insertAndContract_uncontractedList_none_zero]
    rw [staticWickTerm_insert_zero_none]
    simp only [Algebra.smul_mul_assoc]
    rfl
  | some n =>
    simp only [Algebra.smul_mul_assoc, Nat.succ_eq_add_one, Fin.zero_eta, Fin.val_zero,
      List.insertIdx_zero]
    rw [staticWickTerm_insert_zero_some]

end
end WickContraction
