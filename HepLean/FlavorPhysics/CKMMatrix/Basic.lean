/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.Polyrith

open Matrix Complex


noncomputable section

@[simp]
def phaseShiftMatrix (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![ Complex.exp (I * a), 0, 0], ![0,  Complex.exp (I * b), 0], ![0, 0, Complex.exp (I * c)]]

lemma phaseShiftMatrix_one : phaseShiftMatrix 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Matrix.one_apply, phaseShiftMatrix]
  rfl

lemma phaseShiftMatrix_star (a b c : ℝ) :
    (phaseShiftMatrix a b c)ᴴ = phaseShiftMatrix (- a) (- b) (- c) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
  simp [← exp_conj, conj_ofReal]
  rfl
  rfl

lemma phaseShiftMatrix_mul (a b c d e f : ℝ) :
    phaseShiftMatrix a b c * phaseShiftMatrix d e f = phaseShiftMatrix (a + d) (b + e) (c + f) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [Matrix.mul_apply, Fin.sum_univ_three]
  any_goals rw [mul_add, exp_add]
  change cexp (I * ↑c)  * 0 = 0
  simp

@[simps!]
def phaseShift (a b c : ℝ) : unitaryGroup (Fin 3) ℂ :=
  ⟨phaseShiftMatrix a b c,
  by
    rw [mem_unitaryGroup_iff]
    change _ * (phaseShiftMatrix a b c)ᴴ = 1
    rw [phaseShiftMatrix_star, phaseShiftMatrix_mul, ← phaseShiftMatrix_one]
    simp only [phaseShiftMatrix, add_right_neg, ofReal_zero, mul_zero, exp_zero]⟩

lemma phaseShift_coe_matrix (a b c : ℝ) : ↑(phaseShift a b c) = phaseShiftMatrix a b c := rfl

def phaseShiftRelation (U V : unitaryGroup (Fin 3) ℂ) : Prop :=
  ∃ a b c e f g , U = phaseShift a b c * V * phaseShift e f g

lemma phaseShiftRelation_refl (U : unitaryGroup (Fin 3) ℂ) : phaseShiftRelation U U := by
  use 0, 0, 0, 0, 0, 0
  rw [Subtype.ext_iff_val]
  simp only [Submonoid.coe_mul, phaseShift_coe_matrix, ofReal_zero, mul_zero, exp_zero]
  rw [phaseShiftMatrix_one]
  simp only [one_mul, mul_one]

lemma phaseShiftRelation_symm {U V : unitaryGroup (Fin 3) ℂ} :
    phaseShiftRelation U V → phaseShiftRelation V U := by
  intro h
  obtain ⟨a, b, c, e, f, g, h⟩ := h
  use (- a), (- b), (- c), (- e), (- f), (- g)
  rw [Subtype.ext_iff_val]
  rw [h]
  repeat rw [mul_assoc]
  simp only [Submonoid.coe_mul, phaseShift_coe_matrix, ofReal_neg, mul_neg]
  rw [phaseShiftMatrix_mul]
  repeat rw [← mul_assoc]
  simp only [phaseShiftMatrix_mul, add_left_neg, phaseShiftMatrix_one, one_mul, add_right_neg,
    mul_one]

lemma phaseShiftRelation_trans {U V W : unitaryGroup (Fin 3) ℂ} :
    phaseShiftRelation U V → phaseShiftRelation V W → phaseShiftRelation U W := by
  intro hUV hVW
  obtain ⟨a, b, c, e, f, g, hUV⟩ := hUV
  obtain ⟨d, i, j, k, l, m, hVW⟩ := hVW
  use (a + d), (b + i), (c + j), (e + k), (f + l), (g + m)
  rw [Subtype.ext_iff_val]
  rw [hUV, hVW]
  simp only [Submonoid.coe_mul, phaseShift_coe_matrix]
  repeat rw [mul_assoc]
  rw [phaseShiftMatrix_mul]
  repeat rw [← mul_assoc]
  rw [phaseShiftMatrix_mul]
  rw [add_comm k e, add_comm l f, add_comm m g]


def phaseShiftEquivRelation : Equivalence phaseShiftRelation where
  refl := phaseShiftRelation_refl
  symm := phaseShiftRelation_symm
  trans := phaseShiftRelation_trans

def CKMMatrix : Type := unitaryGroup (Fin 3) ℂ

instance CKMMatrixSetoid : Setoid CKMMatrix := ⟨phaseShiftRelation, phaseShiftEquivRelation⟩

@[simp]
def VAbs' (V : unitaryGroup (Fin 3) ℂ) (i j : Fin 3) : ℝ := Complex.abs (V i j)

lemma VAbs'_equiv (i j : Fin 3) (V U : CKMMatrix) (h : V ≈ U) :
    VAbs' V i j = VAbs' U i j  := by
  simp
  obtain ⟨a, b, c, e, f, g, h⟩ := h
  rw [h]
  simp only [Submonoid.coe_mul, phaseShift_coe_matrix]
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [phaseShiftMatrix, Fin.isValue, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    vecCons_const, cons_val_one, head_cons, zero_mul, add_zero, cons_val_two, tail_cons,
    head_fin_const, mul_zero]
  fin_cases i <;> fin_cases j <;>
  simp [Complex.abs_exp]
  all_goals change Complex.abs (0 * _ + _) = _
  all_goals simp [Complex.abs_exp]

def VAbs (i j : Fin 3) : Quotient CKMMatrixSetoid → ℝ :=
  Quotient.lift (fun V => VAbs' V i j) (VAbs'_equiv i j)

@[simp]
abbrev VudAbs := VAbs 0 0

@[simp]
abbrev VusAbs := VAbs 0 1

@[simp]
abbrev VubAbs := VAbs 0 2

@[simp]
abbrev VcdAbs := VAbs 1 0

@[simp]
abbrev VcsAbs := VAbs 1 1

@[simp]
abbrev VcbAbs := VAbs 1 2

@[simp]
abbrev VtdAbs := VAbs 2 0

@[simp]
abbrev VtsAbs := VAbs 2 1

@[simp]
abbrev VtbAbs := VAbs 2 2

lemma VAbs_ge_zero  (i j : Fin 3) (V : Quotient CKMMatrixSetoid) : 0 ≤ VAbs i j V := by
  obtain ⟨V, hV⟩ := Quot.exists_rep V
  rw [← hV]
  exact Complex.abs.nonneg _

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


lemma VAbs_leq_one (i j : Fin 3) (V : Quotient CKMMatrixSetoid) : VAbs i j V ≤ 1 := by
  have h := VAbs_sum_sq_row_eq_one V i
  fin_cases j
  change VAbs i 0 V ≤ 1
  nlinarith
  change VAbs i 1 V ≤ 1
  nlinarith
  change VAbs i 2 V ≤ 1
  nlinarith

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

lemma VAbs_thd_neq_one_fst_snd_sq_neq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3}
    (hV : VAbs i 2 V ≠ 1) : (VAbs i 0 V ^ 2 + VAbs i 1 V ^ 2) ≠ 0 := by
  have h1 : 1 - VAbs i 2 V ^ 2 = VAbs i 0 V ^ 2 + VAbs i 1 V ^ 2 := by
    linear_combination - (VAbs_sum_sq_row_eq_one V i)
  rw [← h1]
  by_contra h
  have h2 : VAbs i 2 V ^2 = 1 := by
    nlinarith
  simp only [Fin.isValue, sq_eq_one_iff] at h2
  have h3 : 0 ≤  VAbs i 2 V := VAbs_ge_zero i 2 V
  have h4 : VAbs i 2 V = 1 := by
    nlinarith
  exact hV h4

lemma VAbs_thd_neq_one_sqrt_fst_snd_sq_neq_zero {V : Quotient CKMMatrixSetoid} {i : Fin 3}
    (hV : VAbs i 2 V ≠ 1) : √(VAbs i 0 V ^ 2 + VAbs i 1 V ^ 2) ≠ 0 := by
  rw [Real.sqrt_ne_zero (Left.add_nonneg (sq_nonneg (VAbs i 0 V)) (sq_nonneg (VAbs i 1 V)))]
  exact VAbs_thd_neq_one_fst_snd_sq_neq_zero hV

lemma VcbAbs_sq_add_VtbAbs_sq (V : Quotient CKMMatrixSetoid) :
    VcbAbs V ^ 2 + VtbAbs V ^ 2 = 1 - VubAbs V ^2 := by
  linear_combination (VAbs_sum_sq_col_eq_one V 2)

lemma VudAbs_sq_add_VusAbs_sq : VudAbs V ^ 2 + VusAbs V ^2 = 1 - VubAbs V ^2  := by
  linear_combination (VAbs_sum_sq_row_eq_one V 0)

namespace CKMMatrix
open ComplexConjugate

lemma fst_row_snd_row (V : CKMMatrix) : V.1 1 0 * conj (V.1 0 0) +  V.1 1 1 * conj (V.1 0 1)
    + V.1 1 2 * conj (V.1 0 2) = 0 := by
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  exact ht


lemma fst_row_thd_row (V : CKMMatrix) :  V.1 2 0 * conj (V.1 0 0) +  V.1 2 1 * conj (V.1 0 1)
    + V.1 2 2 * conj (V.1 0 2) = 0 := by
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  exact ht


end CKMMatrix

end
