/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.StaticContract
import HepLean.PerturbationTheory.WicksTheorem
import HepLean.Meta.Remark.Basic
/-!

# Static Wick's theorem

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldOpFreeAlgebra

open HepLean.List
open WickContraction
open FieldStatistic
namespace FieldOpAlgebra

lemma static_wick_theorem_nil : ofFieldOpList [] = ∑ (φsΛ : WickContraction [].length),
    φsΛ.sign (𝓕 := 𝓕) • φsΛ.staticContract * 𝓝(ofFieldOpList [φsΛ]ᵘᶜ) := by
  simp only [ofFieldOpList, ofFieldOpListF_nil, map_one, List.length_nil]
  rw [sum_WickContraction_nil, uncontractedListGet, nil_zero_uncontractedList]
  simp [sign, empty, staticContract]

/--
The static Wicks theorem states that
`φ₀…φₙ` is equal to the sum of
`φsΛ.1.sign • φsΛ.1.staticContract * 𝓝(ofFieldOpList [φsΛ.1]ᵘᶜ)`
over all Wick contraction `φsΛ`.
This is compared to the ordinary Wicks theorem in which `staticContract` is replaced with
`timeContract`.
-/
theorem static_wick_theorem : (φs : List 𝓕.States) →
    ofFieldOpList φs = ∑ (φsΛ : WickContraction φs.length),
    φsΛ.sign • φsΛ.staticContract * 𝓝(ofFieldOpList [φsΛ]ᵘᶜ)
  | [] => static_wick_theorem_nil
  | φ :: φs => by
    rw [ofFieldOpList_cons, static_wick_theorem φs]
    rw [show (φ :: φs) = φs.insertIdx (⟨0, Nat.zero_lt_succ φs.length⟩ : Fin φs.length.succ) φ
      from rfl]
    conv_rhs => rw [insertLift_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    trans (sign φs c • ↑c.staticContract * (ofFieldOp φ * normalOrder (ofFieldOpList [c]ᵘᶜ)))
    · have ht := Subalgebra.mem_center_iff.mp (Subalgebra.smul_mem (Subalgebra.center ℂ _)
        (c.staticContract).2 c.sign)
      conv_rhs => rw [← mul_assoc, ← ht]
      simp [mul_assoc]
    rw [ofFieldOp_mul_normalOrder_ofFieldOpList_eq_sum]
    rw [Finset.mul_sum]
    rw [uncontractedStatesEquiv_list_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    match n with
    | none =>
      simp only [contractStateAtIndex, uncontractedStatesEquiv, Equiv.optionCongr_apply,
        Equiv.coe_trans, Option.map_none', one_mul, Algebra.smul_mul_assoc, Nat.succ_eq_add_one,
        Fin.zero_eta, Fin.val_zero, List.insertIdx_zero, staticContract_insertAndContract_none,
        insertAndContract_uncontractedList_none_zero]
      erw [sign_insert_none_zero]
      rfl
    | some n =>
      simp only [Algebra.smul_mul_assoc, Nat.succ_eq_add_one, Fin.zero_eta, Fin.val_zero,
        List.insertIdx_zero]
      rw [normalOrder_uncontracted_some]
      simp only [← mul_assoc]
      rw [← smul_mul_assoc]
      conv_rhs => rw [← smul_mul_assoc]
      congr 1
      rw [staticConract_insertAndContract_some_eq_mul_contractStateAtIndex_lt]
      swap
      · simp
      rw [smul_smul]
      by_cases hn : GradingCompliant φs c ∧ (𝓕|>ₛφ) = (𝓕|>ₛ φs[n.1])
      · congr 1
        swap
        · have h1 := c.staticContract.2
          rw [@Subalgebra.mem_center_iff] at h1
          rw [h1]
        erw [sign_insert_some]
        rw [mul_assoc, mul_comm c.sign, ← mul_assoc]
        rw [signInsertSome_mul_filter_contracted_of_not_lt]
        simp only [instCommGroup.eq_1, Fin.zero_succAbove, Fin.not_lt_zero, Finset.filter_False,
          ofFinset_empty, map_one, one_mul]
        simp only [Fin.zero_succAbove, Fin.not_lt_zero, not_false_eq_true]
        exact hn
      · simp only [Fin.getElem_fin, not_and] at hn
        by_cases h0 : ¬ GradingCompliant φs c
        · rw [staticContract_of_not_gradingCompliant]
          simp only [ZeroMemClass.coe_zero, zero_mul, smul_zero, instCommGroup.eq_1, mul_zero]
          exact h0
        · simp_all only [Finset.mem_univ, not_not, instCommGroup.eq_1, forall_const]
          have h1 : contractStateAtIndex φ [c]ᵘᶜ
              ((uncontractedStatesEquiv φs c) (some n)) = 0 := by
            simp only [contractStateAtIndex, uncontractedStatesEquiv, Equiv.optionCongr_apply,
              Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply,
              instCommGroup.eq_1, Fin.coe_cast, Fin.getElem_fin, smul_eq_zero]
            right
            simp only [uncontractedListGet, List.getElem_map,
              uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem]
            rw [superCommute_anPart_ofFieldOpF_diff_grade_zero]
            exact hn
          rw [h1]
          simp

end FieldOpAlgebra
end FieldSpecification
