/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Rows
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
/-!
# Relations for the CKM Matrix

This file contains a collection of relations and properties between the elements of the CKM
matrix.

-/

open Matrix Complex

noncomputable section

namespace CKMMatrix
open ComplexConjugate

section rows

lemma VAbs_sum_sq_row_eq_one (V : Quotient CKMMatrixSetoid) (i : Fin 3) :
    (VAbs i 0 V) ^ 2 + (VAbs i 1 V) ^ 2 + (VAbs i 2 V) ^ 2 = 1 := by
  obtain ⟨V, hV⟩ := Quot.exists_rep V
  subst hV
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV i) i
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_conj, mul_conj, mul_conj] at ht
  repeat rw [← Complex.sq_abs] at ht
  rw [← ofReal_inj]
  simpa using ht

lemma fst_row_normalized_abs (V : CKMMatrix) : abs [V]ud ^ 2 + abs [V]us ^ 2 + abs [V]ub ^ 2 = 1 :=
  VAbs_sum_sq_row_eq_one ⟦V⟧ 0

lemma snd_row_normalized_abs (V : CKMMatrix) : abs [V]cd ^ 2 + abs [V]cs ^ 2 + abs [V]cb ^ 2 = 1 :=
  VAbs_sum_sq_row_eq_one ⟦V⟧ 1

lemma thd_row_normalized_abs (V : CKMMatrix) : abs [V]td ^ 2 + abs [V]ts ^ 2 + abs [V]tb ^ 2 = 1 :=
  VAbs_sum_sq_row_eq_one ⟦V⟧ 2

lemma fst_row_normalized_normSq (V : CKMMatrix) :
    normSq [V]ud + normSq [V]us + normSq [V]ub = 1 := by
  repeat rw [← Complex.sq_abs]
  exact V.fst_row_normalized_abs

lemma snd_row_normalized_normSq (V : CKMMatrix) :
    normSq [V]cd + normSq [V]cs + normSq [V]cb = 1 := by
  repeat rw [← Complex.sq_abs]
  exact V.snd_row_normalized_abs

lemma thd_row_normalized_normSq (V : CKMMatrix) :
    normSq [V]td + normSq [V]ts + normSq [V]tb = 1 := by
  repeat rw [← Complex.sq_abs]
  exact V.thd_row_normalized_abs

lemma normSq_Vud_plus_normSq_Vus (V : CKMMatrix) :
    normSq [V]ud + normSq [V]us = 1 - normSq [V]ub := by
  linear_combination (fst_row_normalized_normSq V)

lemma VudAbs_sq_add_VusAbs_sq : VudAbs V ^ 2 + VusAbs V ^2 = 1 - VubAbs V ^2 := by
  linear_combination (VAbs_sum_sq_row_eq_one V 0)

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
  have h2 : ¬ 0 ≤ (-1 : ℝ) := by simp
  exact h2 h1

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
  have h2 : ¬ 0 ≤ (-1 : ℝ) := by simp
  exact h2 h3

lemma VAbsub_neq_zero_Vud_Vus_neq_zero {V : Quotient CKMMatrixSetoid}
    (hV : VAbs 0 2 V ≠ 1) :(VudAbs V ^ 2 + VusAbs V ^ 2) ≠ 0 := by
  obtain ⟨V⟩ := V
  change VubAbs ⟦V⟧ ≠ 1 at hV
  simp only [VubAbs, VAbs, VAbs', Fin.isValue, Quotient.lift_mk] at hV
  rw [← ud_us_neq_zero_iff_ub_neq_one V] at hV
  simpa [← Complex.sq_abs] using (normSq_Vud_plus_normSq_Vus_neq_zero_ℝ hV)

lemma VAbsub_neq_zero_sqrt_Vud_Vus_neq_zero {V : Quotient CKMMatrixSetoid}
    (hV : VAbs 0 2 V ≠ 1) : √(VudAbs V ^ 2 + VusAbs V ^ 2) ≠ 0 := by
  obtain ⟨V⟩ := V
  rw [Real.sqrt_ne_zero (Left.add_nonneg (sq_nonneg _) (sq_nonneg _))]
  change VubAbs ⟦V⟧ ≠ 1 at hV
  simp only [VubAbs, VAbs, VAbs', Fin.isValue, Quotient.lift_mk] at hV
  rw [← ud_us_neq_zero_iff_ub_neq_one V] at hV
  simpa [← Complex.sq_abs] using (normSq_Vud_plus_normSq_Vus_neq_zero_ℝ hV)

lemma normSq_Vud_plus_normSq_Vus_neq_zero_ℂ {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) :
    (normSq [V]ud : ℂ) + normSq [V]us ≠ 0 := by
  have h1 := normSq_Vud_plus_normSq_Vus_neq_zero_ℝ hb
  simp at h1
  rw [← ofReal_inj] at h1
  simp_all

lemma Vabs_sq_add_neq_zero {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) :
    ((VudAbs ⟦V⟧ : ℂ) * ↑(VudAbs ⟦V⟧) + ↑(VusAbs ⟦V⟧) * ↑(VusAbs ⟦V⟧)) ≠ 0 := by
  have h1 := normSq_Vud_plus_normSq_Vus_neq_zero_ℂ hb
  rw [← Complex.sq_abs, ← Complex.sq_abs] at h1
  simp [sq] at h1
  exact h1

section orthogonal

lemma fst_row_orthog_snd_row (V : CKMMatrix) :
    [V]cd * conj [V]ud + [V]cs * conj [V]us + [V]cb * conj [V]ub = 0 := by
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  exact ht

lemma fst_row_orthog_thd_row (V : CKMMatrix) :
    [V]td * conj [V]ud + [V]ts * conj [V]us + [V]tb * conj [V]ub = 0 := by
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  exact ht

lemma Vcd_mul_conj_Vud (V : CKMMatrix) :
    [V]cd * conj [V]ud = -[V]cs * conj [V]us - [V]cb * conj [V]ub := by
  linear_combination (V.fst_row_orthog_snd_row)

lemma Vcs_mul_conj_Vus (V : CKMMatrix) :
    [V]cs * conj [V]us = - [V]cd * conj [V]ud - [V]cb * conj [V]ub := by
  linear_combination V.fst_row_orthog_snd_row

end orthogonal

lemma VAbs_thd_eq_one_fst_eq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3} (hV : VAbs i 2 V = 1) :
    VAbs i 0 V = 0 := by
  have h := VAbs_sum_sq_row_eq_one V i
  rw [hV] at h
  simp at h
  nlinarith

lemma VAbs_thd_eq_one_snd_eq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3} (hV : VAbs i 2 V = 1) :
    VAbs i 1 V = 0 := by
  have h := VAbs_sum_sq_row_eq_one V i
  rw [hV] at h
  simp at h
  nlinarith

section crossProduct

lemma conj_Vtb_cross_product {V : CKMMatrix} {τ : ℝ}
    (hτ : [V]t = cexp (τ * I) • (conj [V]u ×₃ conj [V]c)) :
    conj [V]tb = cexp (- τ * I) * ([V]cs * [V]ud - [V]us * [V]cd) := by
  have h1 := congrFun hτ 2
  simp [crossProduct, tRow, uRow, cRow] at h1
  apply congrArg conj at h1
  simp at h1
  rw [h1]
  simp only [← exp_conj, _root_.map_mul, conj_ofReal, conj_I, mul_neg, Fin.isValue, neg_mul]
  field_simp
  ring_nf

end crossProduct

lemma conj_Vtb_mul_Vud {V : CKMMatrix} {τ : ℝ}
    (hτ : [V]t = cexp (τ * I) • (conj [V]u ×₃ conj [V]c)) :
    cexp (τ * I) * conj [V]tb * conj [V]ud =
    [V]cs * (normSq [V]ud + normSq [V]us) + [V]cb * conj [V]ub * [V]us := by
  rw [conj_Vtb_cross_product hτ]
  simp [exp_neg]
  have h2 : ([V]cs * [V]ud - [V]us * [V]cd) * conj [V]ud = [V]cs
      * [V]ud * conj [V]ud - [V]us * ([V]cd * conj [V]ud) := by
    ring
  rw [h2, V.Vcd_mul_conj_Vud]
  rw [normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
  simp only [Fin.isValue, neg_mul]
  ring

lemma conj_Vtb_mul_Vus {V : CKMMatrix} {τ : ℝ}
    (hτ : [V]t = cexp (τ * I) • (conj [V]u ×₃ conj [V]c)) :
    cexp (τ * I) * conj [V]tb * conj [V]us =
    - ([V]cd * (normSq [V]ud + normSq [V]us) + [V]cb * conj ([V]ub) * [V]ud) := by
  rw [conj_Vtb_cross_product hτ]
  simp [exp_neg]
  have h2 : ([V]cs * [V]ud - [V]us * [V]cd) * conj [V]us = ([V]cs
      * conj [V]us) * [V]ud - [V]us * [V]cd * conj [V]us := by
    ring
  rw [h2, V.Vcs_mul_conj_Vus]
  rw [normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
  simp only [Fin.isValue, neg_mul]
  ring

lemma cs_of_ud_us_ub_cb_tb {V : CKMMatrix} (h : [V]ud ≠ 0 ∨ [V]us ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    [V]cs = (- conj [V]ub * [V]us * [V]cb +
      cexp (τ * I) * conj [V]tb * conj [V]ud) / (normSq [V]ud + normSq [V]us) := by
  have h1 := normSq_Vud_plus_normSq_Vus_neq_zero_ℂ h
  rw [conj_Vtb_mul_Vud hτ]
  field_simp
  ring

lemma cd_of_ud_us_ub_cb_tb {V : CKMMatrix} (h : [V]ud ≠ 0 ∨ [V]us ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    [V]cd = - (conj [V]ub * [V]ud * [V]cb + cexp (τ * I) * conj [V]tb * conj [V]us) /
      (normSq [V]ud + normSq [V]us) := by
  have h1 := normSq_Vud_plus_normSq_Vus_neq_zero_ℂ h
  rw [conj_Vtb_mul_Vus hτ]
  field_simp
  ring

end rows

section individual

lemma VAbs_ge_zero (i j : Fin 3) (V : Quotient CKMMatrixSetoid) : 0 ≤ VAbs i j V := by
  obtain ⟨V, hV⟩ := Quot.exists_rep V
  rw [← hV]
  exact Complex.abs.nonneg _

lemma VAbs_leq_one (i j : Fin 3) (V : Quotient CKMMatrixSetoid) : VAbs i j V ≤ 1 := by
  have h := VAbs_sum_sq_row_eq_one V i
  fin_cases j
  change VAbs i 0 V ≤ 1
  nlinarith
  change VAbs i 1 V ≤ 1
  nlinarith
  change VAbs i 2 V ≤ 1
  nlinarith

end individual

section columns

lemma VAbs_sum_sq_col_eq_one (V : Quotient CKMMatrixSetoid) (i : Fin 3) :
    (VAbs 0 i V) ^ 2 + (VAbs 1 i V) ^ 2 + (VAbs 2 i V) ^ 2 = 1 := by
  obtain ⟨V, hV⟩ := Quot.exists_rep V
  subst hV
  have hV := V.prop
  rw [mem_unitaryGroup_iff'] at hV
  have ht := congrFun (congrFun hV i) i
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm, mul_conj, mul_comm, mul_conj, mul_comm, mul_conj] at ht
  repeat rw [← Complex.sq_abs] at ht
  rw [← ofReal_inj]
  simpa using ht

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

lemma cb_eq_zero_of_ud_us_zero {V : CKMMatrix} (h : [V]ud = 0 ∧ [V]us = 0) :
    [V]cb = 0 := by
  have h1 := fst_row_normalized_abs V
  rw [← thd_col_normalized_abs V] at h1
  simp [h] at h1
  rw [add_assoc] at h1
  simp at h1
  rw [add_eq_zero_iff' (sq_nonneg _) (sq_nonneg _)] at h1
  simp at h1
  exact h1.1

lemma cs_of_ud_us_zero {V : CKMMatrix} (ha : ¬ ([V]ud ≠ 0 ∨ [V]us ≠ 0)) :
    VcsAbs ⟦V⟧ = √(1 - VcdAbs ⟦V⟧ ^ 2) := by
  have h1 := snd_row_normalized_abs V
  symm
  rw [Real.sqrt_eq_iff_sq_eq]
  simp [not_or] at ha
  rw [cb_eq_zero_of_ud_us_zero ha] at h1
  simp at h1
  simp [VAbs]
  linear_combination h1
  simp only [VcdAbs, Fin.isValue, sub_nonneg, sq_le_one_iff_abs_le_one]
  rw [@abs_le]
  have h1 := VAbs_leq_one 1 0 ⟦V⟧
  have h0 := VAbs_ge_zero 1 0 ⟦V⟧
  simp_all
  have hn : -1 ≤ (0 : ℝ) := by simp
  exact hn.trans h0
  exact VAbs_ge_zero _ _ ⟦V⟧

lemma VcbAbs_sq_add_VtbAbs_sq (V : Quotient CKMMatrixSetoid) :
    VcbAbs V ^ 2 + VtbAbs V ^ 2 = 1 - VubAbs V ^2 := by
  linear_combination (VAbs_sum_sq_col_eq_one V 2)

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
  have h2 : ¬ 0 ≤ (-1 : ℝ) := by simp
  exact h2 h1

lemma VAbs_fst_col_eq_one_snd_eq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3}
    (hV : VAbs 0 i V = 1) : VAbs 1 i V = 0 := by
  have h := VAbs_sum_sq_col_eq_one V i
  rw [hV] at h
  simp at h
  nlinarith

lemma VAbs_fst_col_eq_one_thd_eq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3}
    (hV : VAbs 0 i V = 1) : VAbs 2 i V = 0 := by
  have h := VAbs_sum_sq_col_eq_one V i
  rw [hV] at h
  simp at h
  nlinarith

end columns

end CKMMatrix
end
