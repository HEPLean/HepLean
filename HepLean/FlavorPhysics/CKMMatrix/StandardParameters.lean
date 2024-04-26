/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Rows
import HepLean.FlavorPhysics.CKMMatrix.PhaseFreedom
import HepLean.FlavorPhysics.CKMMatrix.Ratios
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Matrix Complex
open ComplexConjugate


noncomputable section


def S₁₃ (V : Quotient CKMMatrixSetoid) : ℝ := VubAbs V

lemma VubAbs_eq_S₁₃ (V : Quotient CKMMatrixSetoid) : VubAbs V = S₁₃ V := rfl

def θ₁₃ (V : Quotient CKMMatrixSetoid) : ℝ := Real.arcsin (S₁₃ V)

lemma S₁₃_eq_sin_θ₁₃ (V : Quotient CKMMatrixSetoid) : Real.sin (θ₁₃ V) = S₁₃ V  := by
  refine Real.sin_arcsin ?_ ?_
  have h1 := VAbs_ge_zero 0 2 V
  rw [← VubAbs_eq_S₁₃]
  simp
  linarith
  rw [← VubAbs_eq_S₁₃]
  exact (VAbs_leq_one 0 2 V)

lemma S₁₃_eq_ℂsin_θ₁₃ (V : Quotient CKMMatrixSetoid) : Complex.sin (θ₁₃ V) = S₁₃ V := by
  rw [← S₁₃_eq_sin_θ₁₃]
  simp

lemma complexAbs_sin_θ₁₃ (V : Quotient CKMMatrixSetoid) : Complex.abs (Complex.sin (θ₁₃ V)) =
    sin (θ₁₃ V):= by
  rw [S₁₃_eq_ℂsin_θ₁₃, ← VubAbs_eq_S₁₃]
  rw [Complex.abs_ofReal]
  simp
  exact VAbs_ge_zero 0 2 V


lemma S₁₃_of_Vub_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : S₁₃ V = 1 := by
  rw [← VubAbs_eq_S₁₃, ha]


def C₁₃ (V : Quotient CKMMatrixSetoid) : ℝ := Real.cos (θ₁₃ V)

lemma C₁₃_eq_ℂcos_θ₁₃ (V : Quotient CKMMatrixSetoid) : Complex.cos (θ₁₃ V) = C₁₃ V := by
  simp [C₁₃]

lemma complexAbs_cos_θ₁₃ (V : Quotient CKMMatrixSetoid) : Complex.abs (Complex.cos (θ₁₃ V)) =
    cos (θ₁₃ V):= by
  rw [C₁₃_eq_ℂcos_θ₁₃, Complex.abs_ofReal]
  simp
  exact Real.cos_arcsin_nonneg _

lemma cos_θ₁₃_zero {V : Quotient CKMMatrixSetoid} (h1 : Real.cos (θ₁₃ V) = 0) :
    VubAbs V = 1 := by
  rw [θ₁₃, Real.cos_arcsin, ← VubAbs_eq_S₁₃, Real.sqrt_eq_zero] at h1
  have h2 : VubAbs V ^ 2 = 1 := by linear_combination -(1 * h1)
  simp at h2
  cases' h2 with h2 h2
  exact h2
  have h3 := VAbs_ge_zero 0 2 V
  rw [h2] at h3
  simp at h3
  linarith
  simp
  rw [_root_.abs_of_nonneg (VAbs_ge_zero 0 2 V)]
  exact VAbs_leq_one 0 2 V


lemma S₁₃_sq_add_C₁₃_sq (V : Quotient CKMMatrixSetoid) : S₁₃ V ^ 2 + C₁₃ V ^ 2 = 1 := by
  rw [← S₁₃_eq_sin_θ₁₃ V, C₁₃]
  exact Real.sin_sq_add_cos_sq (θ₁₃ V)

lemma C₁₃_of_Vub_eq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : C₁₃ V = 0 := by
  rw [C₁₃, θ₁₃, Real.cos_arcsin, ← VubAbs_eq_S₁₃, ha]
  simp

lemma C₁₃_eq_add_sq (V : Quotient CKMMatrixSetoid) : C₁₃ V = √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₁₃, θ₁₃, Real.cos_arcsin, S₁₃]
  have h1 : 1 - VubAbs V ^ 2 = VudAbs V ^ 2 + VusAbs V ^ 2 := by
    linear_combination - (VAbs_sum_sq_row_eq_one V 0)
  rw [h1]

/-- If VubAbs V = 1 this will give zero.-/
def S₁₂ (V : Quotient CKMMatrixSetoid) : ℝ := VusAbs V / (√ (VudAbs V ^ 2 + VusAbs V ^ 2))

def θ₁₂ (V : Quotient CKMMatrixSetoid) : ℝ := Real.arcsin (S₁₂ V)

lemma S₁₂_nonneg (V : Quotient CKMMatrixSetoid) : 0 ≤ S₁₂ V := by
  rw [S₁₂]
  rw [@div_nonneg_iff]
  apply Or.inl
  apply And.intro
  exact VAbs_ge_zero 0 1 V
  exact Real.sqrt_nonneg (VudAbs V ^ 2 + VusAbs V ^ 2)


lemma S₁₂_leq_one (V : Quotient CKMMatrixSetoid) : S₁₂ V ≤ 1 := by
  rw [S₁₂]
  rw [@div_le_one_iff]
  by_cases h1 : √(VudAbs V ^ 2 + VusAbs V ^ 2) = 0
  simp [h1]
  have h2 := Real.sqrt_nonneg (VudAbs V ^ 2 + VusAbs V ^ 2)
  rw [le_iff_eq_or_lt] at h2
  have h3 : 0 < √(VudAbs V ^ 2 + VusAbs V ^ 2) := by
    cases' h2 with h2 h2
    simp_all
    exact h2
  apply Or.inl
  simp_all
  rw [Real.le_sqrt]
  simp
  exact sq_nonneg (VAbs 0 0 V)
  exact VAbs_ge_zero 0 1 V
  exact le_of_lt h3

lemma S₁₂_eq_sin_θ₁₂ (V : Quotient CKMMatrixSetoid) : Real.sin (θ₁₂ V) = S₁₂ V :=
  Real.sin_arcsin (le_trans (by simp) (S₁₂_nonneg V)) (S₁₂_leq_one V)

lemma S₁₂_eq_ℂsin_θ₁₂ (V : Quotient CKMMatrixSetoid) : Complex.sin (θ₁₂ V) = S₁₂ V := by
  rw [← S₁₂_eq_sin_θ₁₂]
  simp

lemma complexAbs_sin_θ₁₂ (V : Quotient CKMMatrixSetoid) : Complex.abs (Complex.sin (θ₁₂ V)) =
    sin (θ₁₂ V):= by
  rw [S₁₂_eq_ℂsin_θ₁₂, Complex.abs_ofReal]
  simp
  exact S₁₂_nonneg _

lemma S₁₂_of_Vub_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : S₁₂ V = 0 := by
  rw [S₁₂]
  have h1 : 1 - VubAbs V ^ 2 = VudAbs V ^ 2 + VusAbs V ^ 2 := by
    linear_combination - (VAbs_sum_sq_row_eq_one V 0)
  rw [← h1]
  rw [ha]
  simp

def C₁₂ (V : Quotient CKMMatrixSetoid) : ℝ := Real.cos (θ₁₂ V)

lemma C₁₂_eq_ℂcos_θ₁₂ (V : Quotient CKMMatrixSetoid) : Complex.cos (θ₁₂ V) = C₁₂ V := by
  simp [C₁₂]

lemma complexAbs_cos_θ₁₂ (V : Quotient CKMMatrixSetoid) : Complex.abs (Complex.cos (θ₁₂ V)) =
    cos (θ₁₂ V):= by
  rw [C₁₂_eq_ℂcos_θ₁₂, Complex.abs_ofReal]
  simp
  exact Real.cos_arcsin_nonneg _

lemma C₁₂_of_Vub_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : C₁₂ V = 1 := by
  rw [C₁₂, θ₁₂, Real.cos_arcsin, S₁₂_of_Vub_one ha]
  simp

lemma S₁₂_sq_add_C₁₂_sq (V : Quotient CKMMatrixSetoid) : S₁₂ V ^ 2 + C₁₂ V ^ 2 = 1 := by
  rw [← S₁₂_eq_sin_θ₁₂ V, C₁₂]
  exact Real.sin_sq_add_cos_sq (θ₁₂ V)

lemma C₁₂_eq_Vud_div_sqrt {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    C₁₂ V = VudAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₁₂, θ₁₂, Real.cos_arcsin, S₁₂, div_pow, Real.sq_sqrt]
  rw [one_sub_div]
  simp
  rw [Real.sqrt_div]
  rw [Real.sqrt_sq]
  exact VAbs_ge_zero 0 0 V
  exact sq_nonneg (VAbs 0 0 V)
  exact VAbs_thd_neq_one_fst_snd_sq_neq_zero ha
  exact (Left.add_nonneg (sq_nonneg (VAbs 0 0 V)) (sq_nonneg (VAbs 0 1 V)))

theorem VusAbs_eq_S₁₂_mul_C₁₃ (V : Quotient CKMMatrixSetoid) : VusAbs V = S₁₂ V * C₁₃ V := by
  rw [C₁₃, θ₁₃, Real.cos_arcsin, S₁₂, S₁₃]
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
  rw [C₁₃, θ₁₃, Real.cos_arcsin, ← VubAbs_eq_S₁₃, ha]
  simp
  rw [C₁₂_eq_Vud_div_sqrt ha, C₁₃, θ₁₃, Real.cos_arcsin, S₁₃]
  have h1 : 1 - VubAbs V ^ 2 = VudAbs V ^ 2 + VusAbs V ^ 2 := by
    linear_combination - (VAbs_sum_sq_row_eq_one V 0)
  rw [h1, mul_comm]
  exact (mul_div_cancel₀ (VudAbs V) (VAbs_thd_neq_one_sqrt_fst_snd_sq_neq_zero ha)).symm

def S₂₃ (V : Quotient CKMMatrixSetoid) : ℝ :=
  if VubAbs V = 1 then
    VcdAbs V
  else
    VcbAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2)

lemma S₂₃_nonneg (V : Quotient CKMMatrixSetoid) : 0 ≤ S₂₃ V := by
  by_cases ha : VubAbs V = 1
  rw [S₂₃, if_pos ha]
  exact VAbs_ge_zero 1 0 V
  rw [S₂₃, if_neg ha]
  rw [@div_nonneg_iff]
  apply Or.inl
  apply And.intro
  exact VAbs_ge_zero 1 2 V
  exact Real.sqrt_nonneg (VudAbs V ^ 2 + VusAbs V ^ 2)

lemma S₂₃_leq_one (V : Quotient CKMMatrixSetoid) : S₂₃ V ≤ 1 := by
  by_cases ha : VubAbs V = 1
  rw [S₂₃, if_pos ha]
  exact VAbs_leq_one 1 0 V
  rw [S₂₃, if_neg ha]
  rw [@div_le_one_iff]
  by_cases h1 : √(VudAbs V ^ 2 + VusAbs V ^ 2) = 0
  simp [h1]
  have h2 := Real.sqrt_nonneg (VudAbs V ^ 2 + VusAbs V ^ 2)
  rw [le_iff_eq_or_lt] at h2
  have h3 : 0 < √(VudAbs V ^ 2 + VusAbs V ^ 2) := by
    cases' h2 with h2 h2
    simp_all
    exact h2
  apply Or.inl
  simp_all
  rw [Real.le_sqrt]
  rw [VudAbs_sq_add_VusAbs_sq, ← VcbAbs_sq_add_VtbAbs_sq]
  simp
  exact sq_nonneg (VAbs 2 2 V)
  exact VAbs_ge_zero 1 2 V
  exact le_of_lt h3

def θ₂₃ (V : Quotient CKMMatrixSetoid) : ℝ := Real.arcsin (S₂₃ V)

lemma S₂₃_eq_sin_θ₂₃ (V : Quotient CKMMatrixSetoid) : Real.sin (θ₂₃ V) = S₂₃ V :=
  Real.sin_arcsin (le_trans (by simp) (S₂₃_nonneg V)) (S₂₃_leq_one V)

lemma S₂₃_eq_ℂsin_θ₂₃ (V : Quotient CKMMatrixSetoid) : Complex.sin (θ₂₃ V) = S₂₃ V := by
  rw [← S₂₃_eq_sin_θ₂₃]
  simp

lemma complexAbs_sin_θ₂₃ (V : Quotient CKMMatrixSetoid) : Complex.abs (Complex.sin (θ₂₃ V)) =
    sin (θ₂₃ V):= by
  rw [S₂₃_eq_ℂsin_θ₂₃, Complex.abs_ofReal]
  simp
  exact S₂₃_nonneg _

lemma S₂₃_of_Vub_eq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V = 1) : S₂₃ V = VcdAbs V := by
  rw [S₂₃, if_pos ha]

lemma S₂₃_of_Vub_neq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    S₂₃ V = VcbAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2)  := by
  rw [S₂₃, if_neg ha]

def C₂₃ (V : Quotient CKMMatrixSetoid) : ℝ := Real.cos (θ₂₃ V)

lemma C₂₃_eq_ℂcos_θ₂₃ (V : Quotient CKMMatrixSetoid) : Complex.cos (θ₂₃ V) = C₂₃ V := by
  simp [C₂₃]

lemma complexAbs_cos_θ₂₃ (V : Quotient CKMMatrixSetoid) : Complex.abs (Complex.cos (θ₂₃ V)) =
    cos (θ₂₃ V):= by
  rw [C₂₃_eq_ℂcos_θ₂₃, Complex.abs_ofReal]
  simp
  exact Real.cos_arcsin_nonneg _

lemma S₂₃_sq_add_C₂₃_sq (V : Quotient CKMMatrixSetoid) : S₂₃ V ^ 2 + C₂₃ V ^ 2 = 1 := by
  rw [← S₂₃_eq_sin_θ₂₃ V, C₂₃]
  exact Real.sin_sq_add_cos_sq (θ₂₃ V)

lemma C₂₃_of_Vub_neq_one {V : Quotient CKMMatrixSetoid} (ha : VubAbs V ≠ 1) :
    C₂₃ V = VtbAbs V / √ (VudAbs V ^ 2 + VusAbs V ^ 2) := by
  rw [C₂₃, θ₂₃, Real.cos_arcsin, S₂₃_of_Vub_neq_one ha, div_pow, Real.sq_sqrt]
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



def standardParameterizationAsMatrix (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ  :=
  ![![Real.cos θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₂ * Real.cos θ₁₃, Real.sin θ₁₃ * exp (-I * δ₁₃)],
    ![(-Real.sin θ₁₂ * Real.cos θ₂₃) - (Real.cos θ₁₂ * Real.sin θ₁₃ * Real.sin θ₂₃ * exp (I * δ₁₃)),
      Real.cos θ₁₂ * Real.cos θ₂₃ - Real.sin θ₁₂ * Real.sin θ₁₃ * Real.sin θ₂₃ * exp (I * δ₁₃),
      Real.sin θ₂₃ * Real.cos θ₁₃],
    ![Real.sin θ₁₂ * Real.sin θ₂₃ - Real.cos θ₁₂ * Real.sin θ₁₃ * Real.cos θ₂₃ * exp (I * δ₁₃),
      (-Real.cos θ₁₂ * Real.sin θ₂₃) - (Real.sin θ₁₂ * Real.sin θ₁₃ * Real.cos θ₂₃ * exp (I * δ₁₃)),
      Real.cos θ₂₃ * Real.cos θ₁₃]]

open CKMMatrix

lemma standardParameterizationAsMatrix_unitary  (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) :
    ((standardParameterizationAsMatrix θ₁₂ θ₁₃ θ₂₃ δ₁₃)ᴴ *  standardParameterizationAsMatrix θ₁₂ θ₁₃ θ₂₃ δ₁₃)  = 1 := by
  funext j i
  simp only [standardParameterizationAsMatrix, neg_mul, Fin.isValue]
  rw [mul_apply]
  have h1 := exp_ne_zero (I * ↑δ₁₃)
  fin_cases j <;> rw [Fin.sum_univ_three]
  simp only [Fin.zero_eta, Fin.isValue, conjTranspose_apply, cons_val', cons_val_zero, empty_val',
    cons_val_fin_one, star_mul', RCLike.star_def, conj_ofReal, cons_val_one, head_cons, star_sub,
    star_neg, ← exp_conj, _root_.map_mul, conj_I, neg_mul, cons_val_two, tail_cons, head_fin_const]
  simp [conj_ofReal]
  rw [exp_neg ]
  fin_cases i <;> simp
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq, sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq]
    ring
  simp only [Fin.mk_one, Fin.isValue, conjTranspose_apply, cons_val', cons_val_one, head_cons,
    empty_val', cons_val_fin_one, cons_val_zero, star_mul', RCLike.star_def, conj_ofReal, star_sub,
    ← exp_conj, _root_.map_mul, conj_I, neg_mul, cons_val_two, tail_cons, head_fin_const, star_neg]
  simp [conj_ofReal]
  rw [exp_neg]
  fin_cases i <;> simp
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq, sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq]
    ring
  simp only [Fin.reduceFinMk, Fin.isValue, conjTranspose_apply, cons_val', cons_val_two, tail_cons,
    head_cons, empty_val', cons_val_fin_one, cons_val_zero, star_mul', RCLike.star_def, conj_ofReal,
    ← exp_conj, map_neg, _root_.map_mul, conj_I, neg_mul, neg_neg, cons_val_one, head_fin_const]
  simp [conj_ofReal]
  rw [exp_neg]
  fin_cases i <;> simp
  · ring_nf
    rw [sin_sq]
    ring
  · ring_nf
    rw [sin_sq]
    ring
  · ring_nf
    field_simp
    rw [sin_sq, sin_sq]
    ring

def sP (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) : CKMMatrix :=
  ⟨standardParameterizationAsMatrix θ₁₂ θ₁₃ θ₂₃ δ₁₃, by
   rw [mem_unitaryGroup_iff']
   exact standardParameterizationAsMatrix_unitary θ₁₂ θ₁₃ θ₂₃ δ₁₃⟩

lemma sP_cross (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) :
    [sP θ₁₂ θ₁₃ θ₂₃ δ₁₃]t = (conj [sP θ₁₂ θ₁₃ θ₂₃ δ₁₃]u ×₃ conj [sP θ₁₂ θ₁₃ θ₂₃ δ₁₃]c) := by
  have h1 := exp_ne_zero (I * ↑δ₁₃)
  funext i
  fin_cases i
  · simp only [tRow, sP, standardParameterizationAsMatrix, neg_mul, exp_neg,
    Fin.isValue, cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_two, tail_cons,
    head_fin_const, cons_val_one, head_cons, Fin.zero_eta, crossProduct, uRow, cRow,
    LinearMap.mk₂_apply, Pi.conj_apply, _root_.map_mul, map_inv₀, ← exp_conj, conj_I, conj_ofReal,
    inv_inv, map_sub, map_neg]
    field_simp
    ring_nf
    rw [sin_sq]
    ring
  · simp only [tRow, sP, standardParameterizationAsMatrix, neg_mul, exp_neg, Fin.isValue, cons_val',
    cons_val_zero, empty_val', cons_val_fin_one, cons_val_two, tail_cons, head_fin_const,
    cons_val_one, head_cons, Fin.mk_one, crossProduct, uRow, cRow, LinearMap.mk₂_apply,
    Pi.conj_apply, _root_.map_mul, conj_ofReal, map_inv₀, ← exp_conj, conj_I, inv_inv, map_sub,
    map_neg]
    field_simp
    ring_nf
    rw [sin_sq]
    ring
  · simp only [tRow, sP, standardParameterizationAsMatrix, neg_mul, exp_neg, Fin.isValue,
    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_two, tail_cons, head_fin_const,
    cons_val_one, head_cons, Fin.reduceFinMk, crossProduct, uRow, cRow, LinearMap.mk₂_apply,
    Pi.conj_apply, _root_.map_mul, conj_ofReal, map_inv₀, ← exp_conj, conj_I, inv_inv, map_sub,
    map_neg]
    field_simp
    ring_nf
    rw [sin_sq]
    ring

lemma eq_sP (U : CKMMatrix) {θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ} (hu : [U]u = [sP θ₁₂ θ₁₃ θ₂₃ δ₁₃]u)
    (hc : [U]c = [sP θ₁₂ θ₁₃ θ₂₃ δ₁₃]c) (hU :  [U]t = conj [U]u ×₃ conj [U]c) :
    U = sP θ₁₂ θ₁₃ θ₂₃ δ₁₃ := by
  apply ext_Rows hu hc
  rw [hU, sP_cross, hu, hc]

lemma eq_phases_sP (θ₁₂ θ₁₃ θ₂₃ δ₁₃ δ₁₃' : ℝ) (h : cexp (δ₁₃ * I) = cexp (δ₁₃' * I)) :
    sP θ₁₂ θ₁₃ θ₂₃ δ₁₃ = sP θ₁₂ θ₁₃ θ₂₃ δ₁₃' := by
  simp [sP, standardParameterizationAsMatrix]
  apply CKMMatrix_ext
  simp
  rw [show  exp (I * δ₁₃) = exp (I * δ₁₃') by rw [mul_comm, h, mul_comm]]
  rw [show cexp (-(I * ↑δ₁₃)) = cexp (-(I * ↑δ₁₃')) by rw [exp_neg, exp_neg, mul_comm, h, mul_comm]]

section zeroEntries
variable (a b c d e f : ℝ)

lemma sP_cos_θ₁₃_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.cos (θ₁₃ ⟦V⟧) = 0) :
    sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  have hS13 := congrArg ofReal (S₁₃_of_Vub_one (cos_θ₁₃_zero  h))
  simp [← S₁₃_eq_ℂsin_θ₁₃] at hS13
  have hC12 := congrArg ofReal (C₁₂_of_Vub_one (cos_θ₁₃_zero h))
  simp [← C₁₂_eq_ℂcos_θ₁₂] at hC12
  have hS12 := congrArg ofReal (S₁₂_of_Vub_one (cos_θ₁₃_zero h))
  simp [← S₁₂_eq_ℂsin_θ₁₂] at hS12
  use 0, 0, 0, δ₁₃, 0, -δ₁₃
  simp [sP, standardParameterizationAsMatrix, h, phaseShift, hS13, hC12, hS12]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, mul_apply, Fin.sum_univ_three]
  rfl
  rfl

lemma sP_cos_θ₁₂_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.cos (θ₁₂ ⟦V⟧) = 0) :
    sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, δ₁₃, δ₁₃, -δ₁₃, 0, - δ₁₃
  have hb := exp_ne_zero (I * δ₁₃)
  simp [sP, standardParameterizationAsMatrix, h, phaseShift, exp_neg]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, mul_apply, Fin.sum_univ_three]
  apply Or.inr
  rfl
  change _ = _ + _ * 0
  simp
  field_simp
  ring
  ring
  field_simp
  ring
  change _ = _ + _ * 0
  simp
  field_simp
  ring
  ring
  field_simp
  ring

lemma sP_cos_θ₂₃_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.cos (θ₂₃ ⟦V⟧) = 0) :
    sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, δ₁₃, 0, 0, 0, - δ₁₃
  have hb := exp_ne_zero (I * δ₁₃)
  simp [sP, standardParameterizationAsMatrix, h, phaseShift, exp_neg]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, mul_apply, Fin.sum_univ_three]
  apply Or.inr
  rfl
  ring_nf
  change _ = _ + _ * 0
  simp
  ring
  field_simp
  ring

lemma sP_sin_θ₁₃_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.sin (θ₁₃ ⟦V⟧) = 0) :
    sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, 0, 0, 0, 0, 0
  simp [sP, standardParameterizationAsMatrix, h, phaseShift, exp_neg]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, mul_apply, Fin.sum_univ_three]
  apply Or.inr
  rfl
  apply Or.inr
  rfl

lemma sP_sin_θ₁₂_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.sin (θ₁₂ ⟦V⟧) = 0) :
    sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, δ₁₃, δ₁₃, 0, -δ₁₃, - δ₁₃
  have hb := exp_ne_zero (I * δ₁₃)
  simp [sP, standardParameterizationAsMatrix, h, phaseShift, exp_neg]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, mul_apply, Fin.sum_univ_three]
  apply Or.inr
  rfl
  change _ = _ + _ * 0
  simp
  ring
  field_simp
  ring
  field_simp
  ring
  change _ = _ + _ * 0
  simp
  ring
  field_simp
  ring
  field_simp
  ring


lemma sP_sin_θ₂₃_eq_zero {V : CKMMatrix} (δ₁₃ : ℝ) (h : Real.sin (θ₂₃ ⟦V⟧) = 0) :
    sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₁₃ ≈ sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  use 0, 0, δ₁₃, 0, 0, - δ₁₃
  have hb := exp_ne_zero (I * δ₁₃)
  simp [sP, standardParameterizationAsMatrix, h, phaseShift, exp_neg]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_three, mul_apply, Fin.sum_univ_three]
  apply Or.inr
  rfl
  change _ = _ + _ * 0
  simp
  ring
  ring
  field_simp
  ring


lemma Vs_zero_iff_cos_sin_zero (V : CKMMatrix) :
    VudAbs ⟦V⟧ = 0 ∨ VubAbs ⟦V⟧ = 0 ∨ VusAbs ⟦V⟧ = 0 ∨ VcbAbs ⟦V⟧ = 0 ∨ VtbAbs ⟦V⟧ = 0
    ↔ Real.cos (θ₁₂ ⟦V⟧) = 0 ∨ Real.cos (θ₁₃ ⟦V⟧) = 0 ∨ Real.cos (θ₂₃ ⟦V⟧) = 0 ∨
      Real.sin (θ₁₂ ⟦V⟧) = 0 ∨ Real.sin (θ₁₃ ⟦V⟧) = 0 ∨ Real.sin (θ₂₃ ⟦V⟧) = 0 := by
  rw [VudAbs_eq_C₁₂_mul_C₁₃, VubAbs_eq_S₁₃, VusAbs_eq_S₁₂_mul_C₁₃, VcbAbs_eq_S₂₃_mul_C₁₃,
    VtbAbs_eq_C₂₃_mul_C₁₃]
  rw [C₁₂, C₁₃, C₂₃, S₁₂_eq_sin_θ₁₂, S₂₃_eq_sin_θ₂₃, S₁₃_eq_sin_θ₁₃]
  aesop








end zeroEntries

lemma UCond₁_eq_sP {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb ≠ 0)
    (hV : UCond₁ V) : V = sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) (- arg [V]ub) := by
  have hb' : VubAbs ⟦V⟧ ≠ 1 := by
    rw [ud_us_neq_zero_iff_ub_neq_one] at hb
    simp [VAbs, hb]
  have h1 : ofReal (√(VAbs 0 0 ⟦V⟧ ^ 2 + VAbs 0 1 ⟦V⟧ ^ 2)   * ↑√(VAbs 0 0 ⟦V⟧ ^ 2 + VAbs 0 1 ⟦V⟧ ^ 2) )
    = ofReal ((VAbs 0 0 ⟦V⟧ ^ 2 + VAbs 0 1 ⟦V⟧ ^ 2) ) := by
    rw [Real.mul_self_sqrt ]
    apply add_nonneg (sq_nonneg _) (sq_nonneg _)
  simp at h1
  have hx := Vabs_sq_add_neq_zero hb
  refine eq_sP V ?_ ?_ hV.2.2.2.2
  funext i
  fin_cases i
  simp only [uRow, Fin.isValue, Fin.zero_eta, cons_val_zero, sP, standardParameterizationAsMatrix,
    ofReal_cos,  ofReal_sin, ofReal_neg, mul_neg, neg_mul, neg_neg, cons_val', empty_val',
    cons_val_fin_one, cons_val_one, head_cons, cons_val_two, tail_cons]
  rw [hV.1, VudAbs_eq_C₁₂_mul_C₁₃ ⟦V⟧]
  simp [C₁₂, C₁₃]
  simp [uRow, sP, standardParameterizationAsMatrix]
  rw [hV.2.1, VusAbs_eq_S₁₂_mul_C₁₃ ⟦V⟧, ← S₁₂_eq_sin_θ₁₂ ⟦V⟧, C₁₃]
  simp
  simp [uRow, sP, standardParameterizationAsMatrix]
  nth_rewrite 1 [← abs_mul_exp_arg_mul_I (V.1 0 2)]
  rw [show Complex.abs (V.1 0 2) = VubAbs ⟦V⟧ from rfl]
  rw [VubAbs_eq_S₁₃, ← S₁₃_eq_sin_θ₁₃ ⟦V⟧]
  simp
  ring_nf
  simp
  funext i
  fin_cases i
  simp [cRow, sP, standardParameterizationAsMatrix]
  rw [cd_of_us_or_ud_neq_zero_UCond hb ha hV]
  rw [S₁₂_eq_ℂsin_θ₁₂ ⟦V⟧, S₁₂, C₁₂_eq_ℂcos_θ₁₂ ⟦V⟧, C₁₂_eq_Vud_div_sqrt hb']
  rw [S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, S₂₃_of_Vub_neq_one hb', C₂₃_eq_ℂcos_θ₂₃ ⟦V⟧,
  C₂₃_of_Vub_neq_one hb', S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₁₃]
  field_simp
  rw [h1]
  simp [sq]
  field_simp
  ring_nf
  simp [cRow, sP, standardParameterizationAsMatrix]
  rw [C₁₂_eq_ℂcos_θ₁₂ ⟦V⟧, C₂₃_eq_ℂcos_θ₂₃ ⟦V⟧, S₁₂_eq_ℂsin_θ₁₂ ⟦V⟧,
    S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧]
  rw [C₁₂_eq_Vud_div_sqrt hb', C₂₃_of_Vub_neq_one hb', S₁₂, S₁₃, S₂₃_of_Vub_neq_one hb']
  rw [cs_of_us_or_ud_neq_zero_UCond hb ha hV]
  field_simp
  rw [h1]
  simp [sq]
  field_simp
  ring_nf
  simp [cRow, sP, standardParameterizationAsMatrix]
  rw [hV.2.2.1]
  rw [VcbAbs_eq_S₂₃_mul_C₁₃ ⟦V⟧, S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, C₁₃]
  simp


lemma UCond₂_eq_sP {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb = 0)
    (hV : UCond₂ V) : V = sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  have h23 : S₂₃ ⟦V⟧ = 0 := by
    have h1 := VcbAbs_eq_S₂₃_mul_C₁₃ ⟦V⟧
    simp [VAbs] at h1
    rw [ha] at h1
    simp at h1
    cases' h1 with h1 h1
    exact h1
    have h2 : abs [V]ud = 0 := by
      change VudAbs ⟦V⟧ = 0
      rw [VudAbs_eq_C₁₂_mul_C₁₃, h1]
      simp
    have h2b : abs [V]us = 0 := by
      change VusAbs ⟦V⟧ = 0
      rw [VusAbs_eq_S₁₂_mul_C₁₃, h1]
      simp
    simp_all
  have h1 : ofReal (√(VAbs 0 0 ⟦V⟧ ^ 2 + VAbs 0 1 ⟦V⟧ ^ 2)   * ↑√(VAbs 0 0 ⟦V⟧ ^ 2 + VAbs 0 1 ⟦V⟧ ^ 2) )
    = ofReal ((VAbs 0 0 ⟦V⟧ ^ 2 + VAbs 0 1 ⟦V⟧ ^ 2) ) := by
    rw [Real.mul_self_sqrt ]
    apply add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hx := Vabs_sq_add_neq_zero hb
  simp at h1
  have hb' : VubAbs ⟦V⟧ ≠ 1 := by
    rw [ud_us_neq_zero_iff_ub_neq_one] at hb
    simp [VAbs, hb]
  refine eq_sP V ?_ ?_ hV.2.2.2.1
  funext i
  fin_cases i
  simp [uRow, sP, standardParameterizationAsMatrix]
  rw [hV.1, VudAbs_eq_C₁₂_mul_C₁₃ ⟦V⟧, C₁₂, C₁₃]
  simp
  simp [uRow, sP, standardParameterizationAsMatrix]
  rw [hV.2.1, VusAbs_eq_S₁₂_mul_C₁₃ ⟦V⟧, ← S₁₂_eq_sin_θ₁₂ ⟦V⟧, C₁₃]
  simp
  simp [uRow, sP, standardParameterizationAsMatrix]
  rw [hV.2.2.1, VubAbs_eq_S₁₃, S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧]
  funext i
  fin_cases i
  simp [cRow, sP, standardParameterizationAsMatrix]
  rw [S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, h23]
  simp
  rw [C₂₃_eq_ℂcos_θ₂₃ ⟦V⟧, C₂₃_of_Vub_neq_one hb']
  rw [S₁₂_eq_ℂsin_θ₁₂ ⟦V⟧, S₁₂]
  rw [hV.2.2.2.2.1]
  field_simp
  rw [h1]
  simp [sq]
  field_simp
  ring_nf
  simp
  simp [cRow, sP, standardParameterizationAsMatrix]
  rw [S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, h23]
  simp
  rw [C₂₃_eq_ℂcos_θ₂₃ ⟦V⟧, C₂₃_of_Vub_neq_one hb']
  rw [C₁₂_eq_ℂcos_θ₁₂ ⟦V⟧, C₁₂_eq_Vud_div_sqrt hb']
  rw [hV.2.2.2.2.2]
  field_simp
  rw [h1]
  simp [sq]
  field_simp
  ring_nf
  simp [cRow, sP, standardParameterizationAsMatrix]
  rw [ha, S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, h23]
  simp


lemma UCond₃_eq_sP {V : CKMMatrix} (hV : UCond₃ V) : V = sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) 0 := by
  have h1 : VubAbs ⟦V⟧ = 1 := by
    simp [VAbs]
    rw [hV.2.2.2.1]
    simp
  refine eq_sP V ?_ ?_ hV.2.2.2.2.1
  funext i
  fin_cases i
  simp [uRow, sP, standardParameterizationAsMatrix]
  rw [C₁₃_eq_ℂcos_θ₁₃ ⟦V⟧, C₁₃_of_Vub_eq_one h1, hV.1]
  simp
  simp [uRow, sP, standardParameterizationAsMatrix]
  rw [C₁₃_eq_ℂcos_θ₁₃ ⟦V⟧, C₁₃_of_Vub_eq_one h1, hV.2.1]
  simp
  simp [uRow, sP, standardParameterizationAsMatrix]
  rw [S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₁₃]
  simp [VAbs]
  rw [hV.2.2.2.1]
  simp
  funext i
  fin_cases i
  simp [cRow, sP, standardParameterizationAsMatrix]
  rw [S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, S₂₃_of_Vub_eq_one h1]
  rw [S₁₂_eq_ℂsin_θ₁₂ ⟦V⟧, S₁₂_of_Vub_one h1]
  rw [C₁₂_eq_ℂcos_θ₁₂ ⟦V⟧, C₁₂_of_Vub_one h1]
  rw [S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₁₃_of_Vub_one h1]
  rw [hV.2.2.2.2.2.1]
  simp
  simp [cRow, sP, standardParameterizationAsMatrix]
  rw [S₂₃_eq_ℂsin_θ₂₃ ⟦V⟧, S₂₃_of_Vub_eq_one h1]
  rw [S₁₂_eq_ℂsin_θ₁₂ ⟦V⟧, S₁₂_of_Vub_one h1]
  rw [C₁₂_eq_ℂcos_θ₁₂ ⟦V⟧, C₁₂_of_Vub_one h1]
  rw [S₁₃_eq_ℂsin_θ₁₃ ⟦V⟧, S₁₃_of_Vub_one h1]
  simp
  have h3 : (Real.cos (θ₂₃ ⟦V⟧) : ℂ) = √(1 - S₂₃ ⟦V⟧ ^ 2) := by
    rw [θ₂₃, Real.cos_arcsin]
  simp at h3
  rw [h3, S₂₃_of_Vub_eq_one h1, hV.2.2.2.2.2.2]
  simp [cRow, sP, standardParameterizationAsMatrix]
  rw [C₁₃_eq_ℂcos_θ₁₃ ⟦V⟧, C₁₃_of_Vub_eq_one h1, hV.2.2.1]
  simp


theorem exists_standardParameterization (V : CKMMatrix) :
    ∃ (δ₃ : ℝ), V ≈ sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) δ₃ := by
  obtain ⟨U, hU⟩ := all_eq_abs V
  have hUV : ⟦U⟧ = ⟦V⟧ := (Quotient.eq.mpr (phaseShiftEquivRelation.symm hU.1))
  by_cases ha : [V]ud ≠ 0 ∨ [V]us ≠ 0
  have haU : [U]ud ≠ 0 ∨ [U]us ≠ 0 := by
    by_contra hn
    simp [not_or] at hn
    have hna : VudAbs ⟦U⟧ = 0 ∧ VusAbs ⟦U⟧ =0 := by
      simp [VAbs]
      exact hn
    rw [hUV] at hna
    simp [VAbs] at hna
    simp_all
  by_cases hb : [V]cb ≠ 0
  have hbU : [U]cb ≠ 0 := by
    by_contra hn
    simp at hn
    have hna : VcbAbs ⟦U⟧ = 0 := by
      simp [VAbs]
      exact hn
    rw [hUV] at hna
    simp [VAbs] at hna
    simp_all
  have hU' := UCond₁_eq_sP haU hbU hU.2
  rw [hU'] at hU
  use (- arg ([U]ub))
  rw [← hUV]
  exact hU.1
  simp at hb
  have hbU : [U]cb = 0 := by
    have hna : VcbAbs ⟦U⟧ = 0 := by
      rw [hUV]
      simp [VAbs]
      exact hb
    simpa [VAbs] using hna
  obtain ⟨U2, hU2⟩ := UCond₂_exists haU hbU hU.2
  have hUVa2 : V ≈ U2 := phaseShiftEquivRelation.trans hU.1 hU2.1
  have hUV2 : ⟦U2⟧ = ⟦V⟧ := (Quotient.eq.mpr (phaseShiftEquivRelation.symm hUVa2))
  have haU2 : [U2]ud ≠ 0 ∨ [U2]us ≠ 0 := by
    by_contra hn
    simp [not_or] at hn
    have hna : VudAbs ⟦U2⟧ = 0 ∧ VusAbs ⟦U2⟧ =0 := by
      simp [VAbs]
      exact hn
    rw [hUV2] at hna
    simp [VAbs] at hna
    simp_all
  have hbU2 : [U2]cb = 0 := by
    have hna : VcbAbs ⟦U2⟧ = 0 := by
      rw [hUV2]
      simp [VAbs]
      exact hb
    simpa [VAbs] using hna
  have hU2' := UCond₂_eq_sP haU2 hbU2 hU2.2
  use 0
  rw [← hUV2, ← hU2']
  exact hUVa2
  have haU : ¬ ([U]ud ≠ 0 ∨ [U]us ≠ 0) := by
    simp [not_or] at ha
    have h1 : VudAbs ⟦U⟧ = 0 ∧ VusAbs ⟦U⟧ = 0 := by
      rw [hUV]
      simp [VAbs]
      exact ha
    simpa [not_or, VAbs] using h1
  have ⟨U2, hU2⟩ := UCond₃_exists haU hU.2
  have hUVa2 : V ≈ U2 := phaseShiftEquivRelation.trans hU.1 hU2.1
  have hUV2 : ⟦U2⟧ = ⟦V⟧ := (Quotient.eq.mpr (phaseShiftEquivRelation.symm hUVa2))
  have hx := UCond₃_eq_sP hU2.2
  use 0
  rw [← hUV2, ← hx]
  exact hUVa2






end
