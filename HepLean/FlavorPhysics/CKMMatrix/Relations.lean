/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Rows
import Mathlib.Analysis.SpecialFunctions.Complex.Arg


open Matrix Complex


noncomputable section

namespace CKMMatrix
open ComplexConjugate

lemma fst_row_normalized_abs (V : CKMMatrix) :
    abs [V]ud ^ 2 + abs [V]us ^ 2 + abs [V]ub ^ 2 = 1 := by
  have h1 := VAbs_sum_sq_row_eq_one ⟦V⟧ 0
  simp [VAbs] at h1
  exact h1

lemma fst_row_normalized_normSq (V : CKMMatrix) :
    normSq [V]ud + normSq [V]us + normSq [V]ub = 1 := by
  have h1 := V.fst_row_normalized_abs
  repeat rw [Complex.sq_abs] at h1
  exact h1

lemma snd_row_normalized_abs (V : CKMMatrix) :
    abs [V]cd ^ 2 + abs [V]cs ^ 2 + abs [V]cb ^ 2 = 1 := by
  have h1 := VAbs_sum_sq_row_eq_one ⟦V⟧ 1
  simp [VAbs] at h1
  exact h1

lemma snd_row_normalized_normSq (V : CKMMatrix) :
    normSq [V]cd + normSq [V]cs + normSq [V]cb = 1 := by
  have h1 := V.snd_row_normalized_abs
  repeat rw [Complex.sq_abs] at h1
  exact h1

lemma ud_us_neq_zero_iff_ub_neq_one (V : CKMMatrix) :
    [V]ud ≠ 0 ∨ [V]us ≠ 0 ↔ abs [V]ub ≠ 1 := by
  have h2 := V.fst_row_normalized_abs
  apply Iff.intro
  intro h
  intro h1
  rw [h1] at h2
  simp at h2
  rw [add_eq_zero_iff' (sq_nonneg _) (sq_nonneg _)] at h2
  simp_all
  intro h
  by_contra hn
  rw [not_or] at hn
  simp at hn
  simp_all
  have h1 := Complex.abs.nonneg [V]ub
  rw [h2] at h1
  have h2 : ¬ 0 ≤ ( -1 : ℝ) := by simp
  exact h2 h1

lemma thd_col_normalized_abs (V : CKMMatrix) :
    abs [V]ub ^ 2 + abs [V]cb ^ 2 + abs [V]tb ^ 2 = 1 := by
  have h1 := VAbs_sum_sq_col_eq_one ⟦V⟧ 2
  simp [VAbs] at h1
  exact h1

lemma thd_col_normalized_normSq (V : CKMMatrix) :
    normSq [V]ub + normSq [V]cb + normSq [V]tb = 1 := by
  have h1 := V.thd_col_normalized_abs
  repeat rw [Complex.sq_abs] at h1
  exact h1

lemma cb_tb_neq_zero_iff_ub_neq_one (V : CKMMatrix) :
    [V]cb ≠ 0 ∨ [V]tb ≠ 0 ↔ abs [V]ub ≠ 1 := by
  have h2 := V.thd_col_normalized_abs
  apply Iff.intro
  intro h
  intro h1
  rw [h1] at h2
  simp at h2
  have h2 : Complex.abs (V.1 1 2) ^ 2 + Complex.abs (V.1 2 2) ^ 2 = 0 := by
    linear_combination h2
  rw [add_eq_zero_iff' (sq_nonneg _) (sq_nonneg _)] at h2
  simp_all
  intro h
  by_contra hn
  rw [not_or] at hn
  simp at hn
  simp_all
  have h1 := Complex.abs.nonneg [V]ub
  rw [h2] at h1
  have h2 : ¬ 0 ≤ ( -1 : ℝ) := by simp
  exact h2 h1

lemma tb_neq_zero_of_cb_zero_ud_us_neq_zero {V : CKMMatrix} (h : [V]cb = 0)
    (h1 : [V]ud ≠ 0 ∨ [V]us ≠ 0) :  [V]tb ≠ 0 := by
  rw [ud_us_neq_zero_iff_ub_neq_one] at h1
  rw [← cb_tb_neq_zero_iff_ub_neq_one] at h1
  simp_all

lemma cb_eq_zero_of_ud_us_zero {V : CKMMatrix} (h :  [V]ud = 0 ∧ [V]us = 0) :
    [V]cb = 0 := by
  have h1 := fst_row_normalized_abs V
  rw [← thd_col_normalized_abs V] at h1
  simp [h] at h1
  rw [add_assoc] at h1
  simp at h1
  rw [add_eq_zero_iff' (sq_nonneg _) (sq_nonneg _)] at h1
  simp at h1
  exact h1.1



lemma normSq_tb_of_cb_zero {V : CKMMatrix} (h : [V]cb = 0) : normSq [V]tb =
    normSq [V]ud + normSq [V]us := by
  have h1 := fst_row_normalized_normSq V
  rw [← thd_col_normalized_normSq V] at h1
  rw [h] at h1
  simp at h1
  linear_combination -(1 * h1)


lemma div_td_of_cb_zero_ud_us_neq_zero {V : CKMMatrix} (h : [V]cb = 0)
    (h1 : [V]ud ≠ 0 ∨ [V]us ≠ 0) (a : ℂ) : a / [V]tb =
    (a * conj [V]tb) / (normSq [V]ud + normSq [V]us) := by
  have h2 := tb_neq_zero_of_cb_zero_ud_us_neq_zero h h1
  have h3 : conj [V]tb ≠ 0 := (AddEquivClass.map_ne_zero_iff starRingAut).mpr h2
  have h1 : a / [V]tb = a * conj [V]tb / normSq [V]tb := by
    rw [normSq_eq_conj_mul_self]
    field_simp
    ring
  rw [normSq_tb_of_cb_zero h] at h1
  simp at h1
  exact h1

lemma normSq_Vud_plus_normSq_Vus (V : CKMMatrix) :
    normSq [V]ud + normSq [V]us = 1 - normSq [V]ub := by
  linear_combination (fst_row_normalized_normSq V)

lemma normSq_Vud_plus_normSq_Vus_neq_zero_ℝ {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) :
    normSq [V]ud + normSq [V]us ≠ 0 := by
  rw [normSq_Vud_plus_normSq_Vus V]
  rw [ud_us_neq_zero_iff_ub_neq_one] at hb
  by_contra hn
  rw [← Complex.sq_abs] at hn
  have h2 : Complex.abs (V.1 0 2) ^2 = 1 := by
    linear_combination -(1 * hn)
  simp at h2
  cases' h2 with h2 h2
  exact hb h2
  have h3 := Complex.abs.nonneg [V]ub
  rw [h2] at h3
  have h2 : ¬ 0 ≤ ( -1 : ℝ) := by simp
  exact h2 h3

lemma normSq_Vud_plus_normSq_Vus_neq_zero_ℂ  {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) :
    (normSq [V]ud : ℂ) + normSq [V]us ≠ 0 := by
  have h1 := normSq_Vud_plus_normSq_Vus_neq_zero_ℝ hb
  simp at h1
  rw [← ofReal_inj] at h1
  simp_all

lemma Vabs_sq_add_neq_zero {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) :
    ((VAbs 0 0 ⟦V⟧ : ℂ) * ↑(VAbs 0 0 ⟦V⟧) + ↑(VAbs 0 1 ⟦V⟧) * ↑(VAbs 0 1 ⟦V⟧)) ≠ 0 := by
  have h1 := normSq_Vud_plus_normSq_Vus_neq_zero_ℂ hb
  rw [← Complex.sq_abs, ← Complex.sq_abs] at h1
  simp [sq] at h1
  exact h1


end CKMMatrix
end
