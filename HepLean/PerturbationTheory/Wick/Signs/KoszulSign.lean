/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Signs.KoszulSignInsert
/-!

# Koszul sign

-/

namespace Wick

open HepLean.List
open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- Gives a factor of `- 1` for every fermion-fermion (`q` is `1`) crossing that occurs when sorting
  a list of based on `r`. -/
def koszulSign (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] :
    List 𝓕 → ℂ
  | [] => 1
  | a :: l => koszulSignInsert q le a l * koszulSign q le l

lemma koszulSign_mul_self (l : List 𝓕) : koszulSign q le l * koszulSign q le l = 1 := by
  induction l with
  | nil => simp [koszulSign]
  | cons a l ih =>
    simp only [koszulSign]
    trans (koszulSignInsert q le a l * koszulSignInsert q le a l) *
      (koszulSign q le l * koszulSign q le l)
    · ring
    · rw [ih, koszulSignInsert_mul_self, mul_one]

@[simp]
lemma koszulSign_freeMonoid_of (φ : 𝓕) : koszulSign q le (FreeMonoid.of φ) = 1 := by
  simp only [koszulSign, mul_one]
  rfl

lemma koszulSignInsert_erase_boson {𝓕 : Type} (q : 𝓕 → FieldStatistic)
    (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] (φ : 𝓕) :
    (φs : List 𝓕) → (n : Fin φs.length) → (heq : q (φs.get n) = bosonic) →
    koszulSignInsert q le φ (φs.eraseIdx n) = koszulSignInsert q le φ φs
  | [], _, _ => by
    simp
  | r1 :: r, ⟨0, h⟩, hr => by
    simp only [List.eraseIdx_zero, List.tail_cons]
    simp only [List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
      List.getElem_cons_zero] at hr
    rw [koszulSignInsert]
    simp [hr]
  | r1 :: r, ⟨n + 1, h⟩, hr => by
    simp only [List.eraseIdx_cons_succ]
    rw [koszulSignInsert, koszulSignInsert]
    rw [koszulSignInsert_erase_boson q le φ r ⟨n, Nat.succ_lt_succ_iff.mp h⟩ hr]

lemma koszulSign_erase_boson {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop)
    [DecidableRel le] :
    (φs : List 𝓕) → (n : Fin φs.length) → (heq : q (φs.get n) = bosonic) →
    koszulSign q le (φs.eraseIdx n) = koszulSign q le φs
  | [], _ => by
    simp
  | φ :: φs, ⟨0, h⟩ => by
    simp only [List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
      List.getElem_cons_zero, Fin.isValue, List.eraseIdx_zero, List.tail_cons, koszulSign]
    intro h
    rw [koszulSignInsert_boson]
    simp only [one_mul]
    exact h
  | φ :: φs, ⟨n + 1, h⟩ => by
    simp only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ, Fin.isValue,
      List.eraseIdx_cons_succ]
    intro h'
    rw [koszulSign, koszulSign, koszulSign_erase_boson q le φs ⟨n, Nat.succ_lt_succ_iff.mp h⟩]
    congr 1
    rw [koszulSignInsert_erase_boson q le φ φs ⟨n, Nat.succ_lt_succ_iff.mp h⟩ h']
    exact h'

lemma koszulSign_insertIdx [IsTotal 𝓕 le] [IsTrans 𝓕 le] (φ : 𝓕) :
    (φs : List 𝓕) → (n : ℕ) → (hn : n ≤ φs.length) →
    koszulSign q le (List.insertIdx n φ φs) = insertSign q n φ φs * koszulSign q le φs *
      insertSign q (insertionSortEquiv le (List.insertIdx n φ φs) ⟨n, by
        rw [List.length_insertIdx _ _ hn]
        omega⟩) φ (List.insertionSort le (List.insertIdx n φ φs))
  | [], 0, h => by
    simp [koszulSign, insertSign, superCommuteCoef, koszulSignInsert]
  | [], n + 1, h => by
    simp at h
  | φ1 :: φs, 0, h => by
    simp only [List.insertIdx_zero, List.insertionSort, List.length_cons, Fin.zero_eta]
    rw [koszulSign]
    trans koszulSign q le (φ1 :: φs) * koszulSignInsert q le φ (φ1 :: φs)
    ring
    simp only [insertionSortEquiv, List.length_cons, Nat.succ_eq_add_one, List.insertionSort,
      orderedInsertEquiv, OrderIso.toEquiv_symm, Fin.symm_castOrderIso, HepLean.Fin.equivCons_trans,
      Equiv.trans_apply, HepLean.Fin.equivCons_zero, HepLean.Fin.finExtractOne_apply_eq,
      Fin.isValue, HepLean.Fin.finExtractOne_symm_inl_apply, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, Fin.cast_mk, Fin.eta]
    conv_rhs =>
      enter [2, 4]
      rw [orderedInsert_eq_insertIdx_orderedInsertPos]
    conv_rhs =>
      rhs
      rw [← insertSign_insert]
      change insertSign q (↑(orderedInsertPos le ((List.insertionSort le (φ1 :: φs))) φ)) φ
        (List.insertionSort le (φ1 :: φs))
      rw [← koszulSignInsert_eq_insertSign q le]
    rw [insertSign_zero]
    simp
  | φ1 :: φs, n + 1, h => by
    conv_lhs =>
      rw [List.insertIdx_succ_cons]
      rw [koszulSign]
    rw [koszulSign_insertIdx]
    conv_rhs =>
      rhs
      simp only [List.insertIdx_succ_cons]
      simp only [List.insertionSort, List.length_cons, insertionSortEquiv, Nat.succ_eq_add_one,
        Equiv.trans_apply, HepLean.Fin.equivCons_succ]
      erw [orderedInsertEquiv_fin_succ]
      simp only [Fin.eta, Fin.coe_cast]
      rhs
      rw [orderedInsert_eq_insertIdx_orderedInsertPos]
    conv_rhs =>
      lhs
      rw [insertSign_succ_cons, koszulSign]
    ring_nf
    conv_lhs =>
      lhs
      rw [mul_assoc, mul_comm]
    rw [mul_assoc]
    conv_rhs =>
      rw [mul_assoc, mul_assoc]
    congr 1
    let rs := (List.insertionSort le (List.insertIdx n φ φs))
    have hnsL : n < (List.insertIdx n φ φs).length := by
      rw [List.length_insertIdx _ _]
      simp only [List.length_cons, add_le_add_iff_right] at h
      omega
      exact Nat.le_of_lt_succ h
    let ni : Fin rs.length := (insertionSortEquiv le (List.insertIdx n φ φs))
      ⟨n, hnsL⟩
    let nro : Fin (rs.length + 1) :=
      ⟨↑(orderedInsertPos le rs φ1), orderedInsertPos_lt_length le rs φ1⟩
    rw [koszulSignInsert_insertIdx, koszulSignInsert_cons]
    trans koszulSignInsert q le φ1 φs * (koszulSignCons q le φ1 φ *insertSign q ni φ rs)
    · simp only [rs, ni]
      ring
    trans koszulSignInsert q le φ1 φs * (superCommuteCoef q [φ] [φ1] *
          insertSign q (nro.succAbove ni) φ (List.insertIdx nro φ1 rs))
    swap
    · simp only [rs, nro, ni]
      ring
    congr 1
    simp only [Fin.succAbove]
    have hns : rs.get ni = φ := by
      simp only [Fin.eta, rs]
      rw [← insertionSortEquiv_get]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, List.get_eq_getElem, ni]
      simp_all only [List.length_cons, add_le_add_iff_right, List.getElem_insertIdx_self]
    have hc1 (hninro : ni.castSucc < nro) :  ¬ le φ1 φ := by
      rw [← hns]
      exact lt_orderedInsertPos_rel le φ1 rs ni hninro
    have hc2 (hninro : ¬ ni.castSucc < nro) :  le φ1 φ := by
      rw [← hns]
      refine gt_orderedInsertPos_rel le φ1 rs ?_ ni hninro
      exact List.sorted_insertionSort le (List.insertIdx n φ φs)
    by_cases hn : ni.castSucc < nro
    · simp only [hn, ↓reduceIte, Fin.coe_castSucc]
      rw [insertSign_insert_gt]
      swap
      · exact hn
      congr 1
      rw [koszulSignCons_eq_superComuteCoef]
      simp only [hc1 hn, ↓reduceIte]
      rw [superCommuteCoef_comm]
    · simp only [hn, ↓reduceIte, Fin.val_succ]
      rw [insertSign_insert_lt, ← mul_assoc]
      congr 1
      rw [superCommuteCoef_mul_self, koszulSignCons]
      simp only [hc2 hn, ↓reduceIte]
      exact Nat.le_of_not_lt hn
      exact Nat.le_of_lt_succ (orderedInsertPos_lt_length le rs φ1)
    · exact Nat.le_of_lt_succ h
    · exact Nat.le_of_lt_succ h

end Wick
