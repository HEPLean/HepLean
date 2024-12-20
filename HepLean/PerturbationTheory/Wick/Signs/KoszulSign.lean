/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic
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
    ring
    rw [ih]
    rw [koszulSignInsert_mul_self, mul_one]

@[simp]
lemma koszulSign_freeMonoid_of (i : 𝓕) : koszulSign q le (FreeMonoid.of i) = 1 := by
  change koszulSign q le [i] = 1
  simp only [koszulSign, mul_one]
  rfl

lemma koszulSignInsert_erase_boson {𝓕 : Type} (q : 𝓕 → FieldStatistic)
    (le : 𝓕 → 𝓕 → Prop) [DecidableRel le] (r0 : 𝓕) :
    (r : List 𝓕) → (n : Fin r.length) → (heq : q (r.get n) = bosonic) →
    koszulSignInsert q le r0 (r.eraseIdx n) = koszulSignInsert q le r0 r
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
    rw [koszulSignInsert_erase_boson q le r0 r ⟨n, Nat.succ_lt_succ_iff.mp h⟩ hr]

lemma koszulSign_erase_boson {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le :𝓕 → 𝓕 → Prop)
    [DecidableRel le] :
    (r : List 𝓕) → (n : Fin r.length) → (heq : q (r.get n) = bosonic) →
    koszulSign q le (r.eraseIdx n) = koszulSign q le r
  | [], _ => by
    simp
  | r0 :: r, ⟨0, h⟩ => by
    simp only [List.length_cons, Fin.zero_eta, List.get_eq_getElem, Fin.val_zero,
      List.getElem_cons_zero, Fin.isValue, List.eraseIdx_zero, List.tail_cons, koszulSign]
    intro h
    rw [koszulSignInsert_boson]
    simp only [one_mul]
    exact h
  | r0 :: r, ⟨n + 1, h⟩ => by
    simp only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ, Fin.isValue,
      List.eraseIdx_cons_succ]
    intro h'
    rw [koszulSign, koszulSign]
    rw [koszulSign_erase_boson q le r ⟨n, Nat.succ_lt_succ_iff.mp h⟩]
    congr 1
    rw [koszulSignInsert_erase_boson q le r0 r ⟨n, Nat.succ_lt_succ_iff.mp h⟩ h']
    exact h'

lemma koszulSign_insertIdx [IsTotal 𝓕 le] [IsTrans 𝓕 le] (i : 𝓕) :
    (r : List 𝓕) → (n : ℕ) → (hn : n ≤ r.length) →
    koszulSign q le (List.insertIdx n i r) = insertSign q n i r
      * koszulSign q le r
      * insertSign q (insertionSortEquiv le (List.insertIdx n i r) ⟨n, by
        rw [List.length_insertIdx _ _ hn]
        omega⟩) i
        (List.insertionSort le (List.insertIdx n i r))
  | [], 0, h => by
    simp [koszulSign, insertSign, superCommuteCoef, koszulSignInsert]
  | [], n + 1, h => by
    simp at h
  | r0 :: r, 0, h => by
    simp only [List.insertIdx_zero, List.insertionSort, List.length_cons, Fin.zero_eta]
    rw [koszulSign]
    trans koszulSign q le (r0 :: r) * koszulSignInsert q le i (r0 :: r)
    ring
    simp only [insertionSortEquiv, List.length_cons, Nat.succ_eq_add_one, List.insertionSort,
      orderedInsertEquiv, OrderIso.toEquiv_symm, Fin.symm_castOrderIso, HepLean.Fin.equivCons_trans,
      Equiv.trans_apply, HepLean.Fin.equivCons_zero, HepLean.Fin.finExtractOne_apply_eq,
      Fin.isValue, HepLean.Fin.finExtractOne_symm_inl_apply, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, Fin.cast_mk, Fin.eta]
    conv_rhs =>
      rhs
      rhs
      rw [orderedInsert_eq_insertIdx_orderedInsertPos]
    conv_rhs =>
      rhs
      rw [← insertSign_insert]
      change insertSign q (↑(orderedInsertPos le ((List.insertionSort le (r0 :: r))) i)) i
        (List.insertionSort le (r0 :: r))
      rw [← koszulSignInsert_eq_insertSign q le]
    rw [insertSign_zero]
    simp
  | r0 :: r, n + 1, h => by
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
    let rs := (List.insertionSort le (List.insertIdx n i r))
    have hnsL : n < (List.insertIdx n i r).length := by
      rw [List.length_insertIdx _ _]
      simp only [List.length_cons, add_le_add_iff_right] at h
      omega
      exact Nat.le_of_lt_succ h
    let ni : Fin rs.length := (insertionSortEquiv le (List.insertIdx n i r))
      ⟨n, hnsL⟩
    let nro : Fin (rs.length + 1) :=
      ⟨↑(orderedInsertPos le rs r0), orderedInsertPos_lt_length le rs r0⟩
    rw [koszulSignInsert_insertIdx, koszulSignInsert_cons]
    trans koszulSignInsert q le r0 r * (koszulSignCons q le r0 i *insertSign q ni i rs)
    · simp only [rs, ni]
      ring
    trans koszulSignInsert q le r0 r * (superCommuteCoef q [i] [r0] *
          insertSign q (nro.succAbove ni) i (List.insertIdx nro r0 rs))
    swap
    · simp only [rs, nro, ni]
      ring
    congr 1
    simp only [Fin.succAbove]
    have hns : rs.get ni = i := by
      simp only [Fin.eta, rs]
      rw [← insertionSortEquiv_get]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, List.get_eq_getElem, ni]
      simp_all only [List.length_cons, add_le_add_iff_right, List.getElem_insertIdx_self]
    have hc1 : ni.castSucc < nro → ¬ le r0 i := by
      intro hninro
      rw [← hns]
      exact lt_orderedInsertPos_rel le r0 rs ni hninro
    have hc2 : ¬ ni.castSucc < nro → le r0 i := by
      intro hninro
      rw [← hns]
      refine gt_orderedInsertPos_rel le r0 rs ?_ ni hninro
      exact List.sorted_insertionSort le (List.insertIdx n i r)
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
      rw [insertSign_insert_lt]
      rw [← mul_assoc]
      congr 1
      rw [superCommuteCoef_mul_self]
      rw [koszulSignCons]
      simp only [hc2 hn, ↓reduceIte]
      exact Nat.le_of_not_lt hn
      exact Nat.le_of_lt_succ (orderedInsertPos_lt_length le rs r0)
    · exact Nat.le_of_lt_succ h
    · exact Nat.le_of_lt_succ h

end Wick
