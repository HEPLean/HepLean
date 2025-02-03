/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.Sign.Basic
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.TimeContraction
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
noncomputable def staticContract {φs : List 𝓕.FieldOp}
    (φsΛ : WickContraction φs.length) :
    Subalgebra.center ℂ 𝓕.FieldOpAlgebra :=
  ∏ (a : φsΛ.1), ⟨[anPart (φs.get (φsΛ.fstFieldOfContract a)),
    ofFieldOp (φs.get (φsΛ.sndFieldOfContract a))]ₛ,
      superCommute_anPart_ofFieldOp_mem_center _ _⟩

@[simp]
lemma staticContract_insertAndContract_none (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) :
    (φsΛ ↩Λ φ i none).staticContract = φsΛ.staticContract := by
  rw [staticContract, insertAndContract_none_prod_contractions]
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
lemma staticContract_insertAndContract_some
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (j : φsΛ.uncontracted) :
    (φsΛ ↩Λ φ i (some j)).staticContract =
    (if i < i.succAbove j then
      ⟨[anPart φ, ofFieldOp φs[j.1]]ₛ, superCommute_anPart_ofFieldOp_mem_center _ _⟩
    else ⟨[anPart φs[j.1], ofFieldOp φ]ₛ, superCommute_anPart_ofFieldOp_mem_center _ _⟩) *
    φsΛ.staticContract := by
  rw [staticContract, insertAndContract_some_prod_contractions]
  congr 1
  · simp only [Nat.succ_eq_add_one, insertAndContract_fstFieldOfContract_some_incl, finCongr_apply,
    List.get_eq_getElem, insertAndContract_sndFieldOfContract_some_incl, Fin.getElem_fin]
    split
    · simp
    · simp
  · congr
    ext a
    simp

open FieldStatistic

lemma staticConract_insertAndContract_some_eq_mul_contractStateAtIndex_lt
    (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (i : Fin φs.length.succ) (k : φsΛ.uncontracted)
    (hik : i < i.succAbove k) :
    (φsΛ ↩Λ φ i (some k)).staticContract =
    𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ⟨φs.get, (φsΛ.uncontracted.filter (fun x => x < k))⟩)
    • (contractStateAtIndex φ [φsΛ]ᵘᶜ ((uncontractedFieldOpEquiv φs φsΛ) (some k)) *
      φsΛ.staticContract) := by
  rw [staticContract_insertAndContract_some]
  simp only [Nat.succ_eq_add_one, Fin.getElem_fin, ite_mul, instCommGroup.eq_1,
    contractStateAtIndex, uncontractedFieldOpEquiv, Equiv.optionCongr_apply,
    Equiv.coe_trans, Option.map_some', Function.comp_apply, finCongr_apply, Fin.coe_cast,
    List.getElem_map, uncontractedList_getElem_uncontractedIndexEquiv_symm, List.get_eq_getElem,
    Algebra.smul_mul_assoc, uncontractedListGet]
  · simp only [hik, ↓reduceIte, MulMemClass.coe_mul]
    trans (1 : ℂ) • ((superCommute (anPart φ)) (ofFieldOp φs[k.1]) * ↑φsΛ.staticContract)
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

lemma staticContract_of_not_gradingCompliant (φs : List 𝓕.FieldOp)
    (φsΛ : WickContraction φs.length) (h : ¬ GradingCompliant φs φsΛ) :
    φsΛ.staticContract = 0 := by
  rw [staticContract]
  simp only [GradingCompliant, Fin.getElem_fin, Subtype.forall, not_forall] at h
  obtain ⟨a, ha⟩ := h
  obtain ⟨ha, ha2⟩ := ha
  apply Finset.prod_eq_zero (i := ⟨a, ha⟩)
  simp only [Finset.univ_eq_attach, Finset.mem_attach]
  apply Subtype.eq
  simp only [List.get_eq_getElem, ZeroMemClass.coe_zero]
  rw [superCommute_anPart_ofFieldOpF_diff_grade_zero]
  simp [ha2]

end WickContraction
