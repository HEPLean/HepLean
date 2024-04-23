/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Matrix Complex


noncomputable section


def S₁₃ (V : Quotient CKMMatrixSetoid) : ℝ := VubAbs V

lemma VubAbs_eq_S₁₃ (V : Quotient CKMMatrixSetoid) : VubAbs V = S₁₃ V := rfl

def C₁₃ (V : Quotient CKMMatrixSetoid) : ℝ := √ (1 - S₁₃ V ^ 2)

lemma C₁₃_of_Vub_eq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : C₁₃ V = 0 := by
  rw [C₁₃, ← VubAbs_eq_S₁₃, ha]
  simp

lemma C₁₃_eq_add_sq (V : Quotient CKMMatrixSetoid) : C₁₃ V = √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₁₃, S₁₃]
  have h1 : 1 - VubAbs V ^ 2 = VudAbs V ^ 2 + VusAbs V ^ 2 := by
    linear_combination - (VAbs_sum_sq_row_eq_one V 0)
  rw [h1]


/-- If VubAbs V = 1 this will give zero.-/
def S₁₂ (V : Quotient CKMMatrixSetoid) : ℝ := VusAbs V / (√ (VudAbs V ^ 2 + VusAbs V ^ 2))

lemma S₁₂_Vub_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : S₁₂ V = 0 := by
  rw [S₁₂]
  have h1 : 1 - VubAbs V ^ 2 = VudAbs V ^ 2 + VusAbs V ^ 2 := by
    linear_combination - (VAbs_sum_sq_row_eq_one V 0)
  rw [← h1]
  rw [ha]
  simp


def C₁₂ (V : Quotient CKMMatrixSetoid) : ℝ := √ (1 - S₁₂ V ^ 2)

lemma C₁₂_eq_Vud_div_sqrt {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    C₁₂ V = VudAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₁₂, S₁₂, div_pow, Real.sq_sqrt]
  rw [one_sub_div]
  simp
  rw [Real.sqrt_div]
  rw [Real.sqrt_sq]
  exact VAbs_ge_zero 0 0 V
  exact sq_nonneg (VAbs 0 0 V)
  exact VAbs_thd_neq_one_fst_snd_sq_neq_zero ha
  exact (Left.add_nonneg (sq_nonneg (VAbs 0 0 V)) (sq_nonneg (VAbs 0 1 V)))


theorem VusAbs_eq_S₁₂_mul_C₁₃ (V : Quotient CKMMatrixSetoid) : VusAbs V = S₁₂ V * C₁₃ V := by
  rw [C₁₃, S₁₂, S₁₃]
  have h1 : 1 - VubAbs V ^ 2 = VudAbs V ^ 2 + VusAbs V ^ 2 := by
    linear_combination - (VAbs_sum_sq_row_eq_one V 0)
  rw [h1]
  rw [mul_comm]
  by_cases ha : VubAbs V = 1
  rw [ha] at h1
  simp only [one_pow, sub_self, Fin.isValue] at h1
  rw [← h1]
  simp only [Real.sqrt_zero, div_zero, mul_zero]
  exact VAbs_thd_eq_one_snd_eq_zero ha
  have h2 := VAbs_thd_neq_one_sqrt_fst_snd_sq_neq_zero ha
  exact (mul_div_cancel₀ (VusAbs V) h2).symm

theorem VudAbs_eq_C₁₂_mul_C₁₃ (V : Quotient CKMMatrixSetoid) : VudAbs V = C₁₂ V * C₁₃ V := by
  by_cases ha : VubAbs V = 1
  change VAbs 0 0 V = C₁₂ V * C₁₃ V
  rw [VAbs_thd_eq_one_fst_eq_zero ha]
  rw [C₁₃, ← VubAbs_eq_S₁₃, ha]
  simp
  rw [C₁₂_eq_Vud_div_sqrt ha, C₁₃, S₁₃]
  have h1 : 1 - VubAbs V ^ 2 = VudAbs V ^ 2 + VusAbs V ^ 2 := by
    linear_combination - (VAbs_sum_sq_row_eq_one V 0)
  rw [h1, mul_comm]
  exact (mul_div_cancel₀ (VudAbs V) (VAbs_thd_neq_one_sqrt_fst_snd_sq_neq_zero ha)).symm

def S₂₃ (V : Quotient CKMMatrixSetoid) : ℝ :=
  if VubAbs V = 1 then
    VcdAbs V
  else
    VcbAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2)

lemma S₂₃_of_Vub_eq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : S₂₃ V = VcdAbs V := by
  rw [S₂₃, if_pos ha]

lemma S₂₃_of_Vub_neq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    S₂₃ V = VcbAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2)  := by
  rw [S₂₃, if_neg ha]

def C₂₃ (V : Quotient CKMMatrixSetoid) : ℝ := √(1 - S₂₃ V ^ 2)

lemma C₂₃_of_Vub_neq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    C₂₃ V = VtbAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₂₃, S₂₃_of_Vub_neq_one ha, div_pow, Real.sq_sqrt]
  rw [VudAbs_sq_add_VusAbs_sq, ← VcbAbs_sq_add_VtbAbs_sq]
  rw [one_sub_div]
  simp only [VcbAbs, Fin.isValue, VtbAbs, add_sub_cancel_left]
  rw [Real.sqrt_div (sq_nonneg (VAbs 2 2 V))]
  rw [Real.sqrt_sq (VAbs_ge_zero 2 2 V)]
  rw [VcbAbs_sq_add_VtbAbs_sq, ← VudAbs_sq_add_VusAbs_sq ]
  exact VAbs_thd_neq_one_fst_snd_sq_neq_zero ha
  exact (Left.add_nonneg (sq_nonneg (VAbs 0 0 V)) (sq_nonneg (VAbs 0 1 V)))


lemma VcbAbs_eq_S₂₃_mul_C₁₃ (V : Quotient CKMMatrixSetoid) : VcbAbs V = S₂₃ V * C₁₃ V := by
  by_cases ha : VubAbs V = 1
  rw [C₁₃_of_Vub_eq_one ha]
  simp
  exact VAbs_fst_col_eq_one_snd_eq_zero ha
  rw [S₂₃_of_Vub_neq_one ha, C₁₃_eq_add_sq]
  rw [mul_comm]
  exact (mul_div_cancel₀ (VcbAbs V) (VAbs_thd_neq_one_sqrt_fst_snd_sq_neq_zero ha)).symm

lemma VtbAbs_eq_C₂₃_mul_C₁₃ (V : Quotient CKMMatrixSetoid) : VtbAbs V = C₂₃ V * C₁₃ V := by
  by_cases ha : VubAbs V = 1
  rw [C₁₃_of_Vub_eq_one ha]
  simp
  exact VAbs_fst_col_eq_one_thd_eq_zero ha
  rw [C₂₃_of_Vub_neq_one ha, C₁₃_eq_add_sq]
  rw [mul_comm]
  exact (mul_div_cancel₀ (VtbAbs V) (VAbs_thd_neq_one_sqrt_fst_snd_sq_neq_zero ha)).symm


lemma S₁₂_mul_C₂₃_of_Vud_neq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    S₁₂ V  * C₂₃ V = VusAbs V * VtbAbs V / (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [S₁₂, C₂₃_of_Vub_neq_one ha]
  rw [@div_mul_div_comm]
  rw [Real.mul_self_sqrt]
  exact (Left.add_nonneg (sq_nonneg (VAbs 0 0 V)) (sq_nonneg (VAbs 0 1 V)))

lemma C₁₂_mul_S₂₃_mul_S₁₃_of_Vud_neq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    C₁₂ V * S₂₃ V * S₁₃ V = VudAbs V * VcbAbs V * VubAbs V / (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₁₂_eq_Vud_div_sqrt ha, S₂₃_of_Vub_neq_one ha, S₁₃]
  rw [@div_mul_div_comm]
  rw [Real.mul_self_sqrt (Left.add_nonneg (sq_nonneg (VAbs 0 0 V)) (sq_nonneg (VAbs 0 1 V)))]
  exact (mul_div_right_comm (VudAbs V * VcbAbs V) (VubAbs V) (VudAbs V ^ 2 + VusAbs V ^ 2)).symm

namespace CKMMatrix
open ComplexConjugate

lemma Vud_eq_C₁₂_mul_C₁₃_arg (V : CKMMatrix) :
    V.1 0 0 = (C₁₂ ⟦V⟧ * C₁₃ ⟦V⟧) * exp (I * arg (V.1 0 0)) := by
  nth_rewrite 1 [← abs_mul_exp_arg_mul_I (V.1 0 0)]
  rw [mul_comm _ I]
  congr
  have h1 := VudAbs_eq_C₁₂_mul_C₁₃ ⟦V⟧
  rw [← ofReal_inj] at h1
  simpa using h1

lemma Vus_eq_C₁₂_mul_C₁₃_arg (V : CKMMatrix) :
    V.1 0 1 = (S₁₂ ⟦V⟧ * C₁₃ ⟦V⟧ ) * exp (I * arg (V.1 0 1)) := by
  nth_rewrite 1 [← abs_mul_exp_arg_mul_I (V.1 0 1)]
  rw [mul_comm _ I]
  congr
  have h1 := VusAbs_eq_S₁₂_mul_C₁₃ ⟦V⟧
  rw [← ofReal_inj] at h1
  simpa using h1

lemma Vub_eq_C₁₃_arg (V : CKMMatrix) : V.1 0 2 = S₁₃ ⟦V⟧ * exp (I * arg (V.1 0 2)) := by
  nth_rewrite 1 [← abs_mul_exp_arg_mul_I (V.1 0 2)]
  rw [mul_comm _ I]
  congr

lemma Vcb_eq_S₂₃_mul_C₁₃_arg (V : CKMMatrix) :
    V.1 1 2 = (S₂₃ ⟦V⟧ * C₁₃ ⟦V⟧) * exp (I * arg (V.1 1 2)) := by
  nth_rewrite 1 [← abs_mul_exp_arg_mul_I (V.1 1 2)]
  rw [mul_comm _ I]
  congr
  have h1 := VcbAbs_eq_S₂₃_mul_C₁₃ ⟦V⟧
  rw [← ofReal_inj] at h1
  simpa using h1

lemma Vud_neq_zero_abs_neq_zero (V : CKMMatrix) : abs (V.1 0 0) ≠ 0  ↔ V.1 0 0 ≠ 0 := by
  exact AbsoluteValue.ne_zero_iff Complex.abs

lemma Vcb_neq_zero_abs_neq_zero (V : CKMMatrix) : abs (V.1 1 2) ≠ 0  ↔ V.1 1 2 ≠ 0 := by
  exact AbsoluteValue.ne_zero_iff Complex.abs

lemma Vud_neq_zero_C₁₂_neq_zero {V : CKMMatrix} (ha :  V.1 0 0 ≠ 0) : C₁₂ ⟦V⟧ ≠ 0 := by
  rw [← Vud_neq_zero_abs_neq_zero] at ha
  have h2 := VudAbs_eq_C₁₂_mul_C₁₃ ⟦V⟧
  simp [VAbs] at h2
  rw [h2] at ha
  simp at ha
  rw [not_or] at ha
  exact ha.1

lemma Vud_neq_zero_C₁₃_neq_zero {V : CKMMatrix} (ha : V.1 0 0 ≠ 0) : C₁₃ ⟦V⟧ ≠ 0 := by
  rw [← Vud_neq_zero_abs_neq_zero] at ha
  have h2 := VudAbs_eq_C₁₂_mul_C₁₃ ⟦V⟧
  simp [VAbs] at h2
  rw [h2] at ha
  simp at ha
  rw [not_or] at ha
  exact ha.2

lemma Vcb_neq_zero_S₂₃_neq_zero {V : CKMMatrix} (hb : V.1 1 2 ≠ 0) : S₂₃ ⟦V⟧ ≠ 0 := by
  rw [← Vcb_neq_zero_abs_neq_zero] at hb
  have h2 := VcbAbs_eq_S₂₃_mul_C₁₃ ⟦V⟧
  simp [VAbs] at h2
  rw [h2] at hb
  simp at hb
  rw [not_or] at hb
  exact hb.1

def B (V : CKMMatrix) : ℂ := V.1 0 1 / V.1 0 0

lemma B_abs (V : CKMMatrix) (ha : V.1 0 0 ≠ 0) : abs (B V) = S₁₂ ⟦V⟧ / C₁₂ ⟦V⟧ := by
  rw [B]
  simp only [Fin.isValue, map_div₀]
  have h1 := VusAbs_eq_S₁₂_mul_C₁₃ ⟦V⟧
  have h2 := VudAbs_eq_C₁₂_mul_C₁₃ ⟦V⟧
  simp [VAbs] at h1 h2
  rw [h1, h2]
  rw [@mul_div_mul_comm]
  rw [div_self]
  simp
  exact Vud_neq_zero_C₁₃_neq_zero ha

lemma B_normSq (V : CKMMatrix) (ha : V.1 0 0 ≠ 0) :
    normSq (B V) = (S₁₂ ⟦V⟧ ^ 2) / (C₁₂ ⟦V⟧ ^ 2) := by
  rw [← Complex.sq_abs]
  rw [B_abs V ha]
  simp

def A (V : CKMMatrix) : ℂ := V.1 0 2 / V.1 0 0

lemma A_abs (V : CKMMatrix) :
    abs (A V) = (S₁₃ ⟦V⟧ / C₁₃ ⟦V⟧) * (1 / C₁₂ ⟦V⟧):= by
  rw [A]
  simp only [Fin.isValue, map_div₀]
  have h1 := VubAbs_eq_S₁₃ ⟦V⟧
  have h2 := VudAbs_eq_C₁₂_mul_C₁₃ ⟦V⟧
  simp [VAbs] at h1 h2
  rw [h1, h2]
  rw [← @mul_div_mul_comm]
  simp
  rw [mul_comm]

lemma A_normSq (V : CKMMatrix) :
    normSq (A V) = (S₁₃ ⟦V⟧ ^ 2) / (C₁₃ ⟦V⟧ ^ 2) * (1 / (C₁₂ ⟦V⟧ ^ 2)) := by
  rw [← Complex.sq_abs]
  rw [A_abs V]
  rw [mul_pow]
  simp

def D (V : CKMMatrix) : ℂ := V.1 1 0 / V.1 1 2

def C' (V : CKMMatrix) : ℂ := V.1 1 1 / V.1 1 2

def C (V : CKMMatrix) : ℂ := C' V * (1 + abs (B V)^2) + conj (A V) * B V

lemma C'_of_C (V : CKMMatrix) : C' V = (C V - conj (A V) * B V) / (1 + abs (B V)^2) := by
  have h1 : C V = C' V * (1 + abs (B V)^2) + conj (A V) * B V := by rfl
  have h2 : C V - conj (A V) * B V = C' V * (1 + abs (B V)^2) := by
    linear_combination h1
  rw [h2]
  rw [mul_div_cancel_right₀]
  have h2 : 0 ≤ ↑(Complex.abs (B V)) ^ 2 := by simp
  have h3 : 0 < 1 + ↑(Complex.abs (B V)) ^ 2 := by linarith
  by_contra hn
  have hx : 1 + Complex.abs (B V) ^ 2 = 0 := by
    rw [← ofReal_inj]
    simpa using hn
  have h4 := lt_of_lt_of_eq h3 hx
  simp at h4

lemma norm_D_C'_A {V : CKMMatrix} (ha : V.1 1 2 ≠ 0) (hb : V.1 0 0 ≠ 0) :
    D V + C' V  * conj (B V) + conj (A V) = 0 := by
  have h1 : (V.1 1 0 * conj (V.1 0 0) + V.1 1 1 * conj (V.1 0 1)
    + V.1 1 2 * conj (V.1 0 2))/ (V.1 1 2 * conj (V.1 0 0)) = 0 := by
    rw [fst_row_snd_row V ]
    simp
  rw [← div_add_div_same, ← div_add_div_same] at h1
  rw [mul_div_mul_comm, mul_div_mul_comm, mul_div_mul_comm] at h1
  rw [div_self, div_self] at h1
  change D V * 1 + _ + _ = _ at h1
  have h2 : (starRingEnd ℂ) (V.1 0 2) / (starRingEnd ℂ) (V.1 0 0) = conj (A V) := by
    simp [A]
  have h3 : ((starRingEnd ℂ) (V.1 0 1) / (starRingEnd ℂ) (V.1 0 0)) = conj (B V) := by
    simp [B]
  rw [h2, h3] at h1
  simp at h1
  exact h1
  exact ha
  simpa using hb


lemma norm_D_C_A {V : CKMMatrix} (ha : V.1 1 2 ≠ 0) (hb : V.1 0 0 ≠ 0) :
    D V + (conj (A V) + C V * conj (B V) ) / (1 + abs (B V)^2) = 0 := by
  have h1 := norm_D_C'_A ha hb
  rw [C'_of_C] at h1
  rw [div_mul_eq_mul_div] at h1
  rw [add_assoc] at h1
  rw [div_add'] at h1
  have h2 : ((C V - (starRingEnd ℂ) (A V) * B V) * (starRingEnd ℂ) (B V) +
      (starRingEnd ℂ) (A V) * (1 + ↑(Complex.abs (B V)) ^ 2)) =
      (conj (A V) + C V * conj (B V) ) := by
    have h3 : ↑(Complex.abs (B V)) ^ 2 = (B V) * conj (B V) := by
      rw [mul_conj]
      rw [ ← Complex.sq_abs]
      simp
    rw [h3]
    ring
  rw [h2] at h1
  exact h1
  have h2 : 0 ≤ ↑(Complex.abs (B V)) ^ 2 := by simp
  have h3 : 0 < 1 + ↑(Complex.abs (B V)) ^ 2 := by linarith
  by_contra hn
  have hx : 1 + Complex.abs (B V) ^ 2 = 0 := by
    rw [← ofReal_inj]
    simpa using hn
  have h4 := lt_of_lt_of_eq h3 hx
  simp at h4

lemma D_of_A_C {V : CKMMatrix} (ha : V.1 1 2 ≠ 0) (hb : V.1 0 0 ≠ 0) :
    D V = - (conj (A V) + C V * conj (B V) ) / (1 + abs (B V)^2)  := by
  linear_combination (norm_D_C_A ha hb)

lemma normSq_D_C'_add' (V : CKMMatrix) (ha : V.1 1 2 ≠ 0) (hb : V.1 0 0 ≠ 0)  :
    normSq (D V) + normSq (C' V) + 1 = ((1 + normSq (B V)) *
    (normSq (C V) + normSq (B V) + normSq (A V) + 1)) / (1 + normSq (B V)) ^ 2 := by
  rw [← ofReal_inj]
  simp
  rw [← mul_conj, ← mul_conj]
  rw [D_of_A_C, C'_of_C]
  simp
  rw [conj_ofReal]
  rw [div_mul_div_comm, div_mul_div_comm]
  rw [div_add_div_same]
  rw [div_add_one]
  have h1 : ((Complex.abs (B V)) : ℂ) ^ 2 = normSq (B V) := by
    rw [← Complex.sq_abs]
    simp
  congr 1
  rw [← mul_conj, ← mul_conj, ← mul_conj]
  rw [h1, ← mul_conj]
  ring
  rw [h1]
  ring
  simp
  have h2 : 0 ≤ ↑(Complex.abs (B V)) ^ 2 := by simp
  have h3 : 0 < 1 + ↑(Complex.abs (B V)) ^ 2 := by linarith
  by_contra hn
  have hx : 1 + Complex.abs (B V) ^ 2 = 0 := by
    rw [← ofReal_inj]
    simpa using hn
  have h4 := lt_of_lt_of_eq h3 hx
  simp at h4
  exact ha
  exact hb

lemma normS1_B_neq_zero (V : CKMMatrix):
    1 + normSq (B V) ≠ 0 := by
  have h2 : 0 ≤ normSq (B V) := by
    exact normSq_nonneg (B V)
  have h3 : 0 < 1 + normSq (B V) := by linarith
  by_contra hn
  have ht := lt_of_lt_of_eq h3 hn
  simp at ht

lemma normSq_D_C'_add (V : CKMMatrix) (ha : V.1 1 2 ≠ 0) (hb : V.1 0 0 ≠ 0)  :
    normSq (D V) + normSq (C' V) + 1 =
    (normSq (C V) + normSq (B V) + normSq (A V) + 1) / (1 + normSq (B V)) := by
  rw [normSq_D_C'_add' V ha hb]
  rw [sq]
  rw [← div_mul_div_comm]
  rw [div_self]
  simp
  exact normS1_B_neq_zero V

lemma D_C'_of_S_C (V : CKMMatrix) (ha : V.1 1 2 ≠ 0) :
    normSq (D V) + normSq (C' V) + 1 = 1 / (S₂₃ ⟦V⟧ * C₁₃ ⟦V⟧) ^ 2 := by
  have h1 : ((abs (V.1 1 0)) ^ 2 + (abs (V.1 1 1)) ^ 2 + (abs (V.1 1 2)) ^ 2)/ (abs (V.1 1 2))^2
      = 1 /(abs (V.1 1 2))^2 := by
    have h2 := VAbs_sum_sq_row_eq_one ⟦V⟧ 1
    erw [h2]
  rw [← div_add_div_same, ← div_add_div_same] at h1
  rw [← div_pow, ← div_pow] at h1
  rw [div_self] at h1
  have h3 : (Complex.abs (V.1 1 0) / Complex.abs (V.1 1 2)) = abs (D V) := by
    simp [D]
  have h4 : (Complex.abs (V.1 1 1) / Complex.abs (V.1 1 2)) = abs (C' V) := by
    simp [C']
  rw [h3, h4] at h1
  have h5 := VcbAbs_eq_S₂₃_mul_C₁₃ ⟦V⟧
  simp [VAbs] at h5
  rw [h5] at h1
  rw [Complex.sq_abs, Complex.sq_abs] at h1
  exact h1
  simp
  exact ha

lemma C_of_S_C (V : CKMMatrix) (ha : V.1 1 2 ≠ 0)  (hb : V.1 0 0 ≠ 0) :
    normSq (C V) = 0 := by
  have h1 :=  D_C'_of_S_C V ha
  rw [normSq_D_C'_add V ha hb] at h1
  rw [div_eq_mul_inv] at h1
  have h3 : 1 / (S₂₃ ⟦V⟧ * C₁₃ ⟦V⟧) ^ 2 ≠ 0 := by
    simp
    rw [not_or]
  have h2 := eq_mul_of_mul_inv_eq₀ h3 h1
  have h4 : normSq (C V) = 1 / (S₂₃ ⟦V⟧ * C₁₃ ⟦V⟧) ^ 2 * (1 + normSq (B V))
    - normSq (B V) - normSq (A V) - 1 := by
    linear_combination h2
  rw [B_normSq] at h4
  rw [A_normSq] at h4
  field_simp at h4



end CKMMatrix



end
