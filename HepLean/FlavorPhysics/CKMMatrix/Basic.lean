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
  ![![cexp (I * a), 0, 0], ![0,  cexp (I * b), 0], ![0, 0, cexp (I * c)]]

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

lemma CKMMatrix_ext {U V : CKMMatrix} (h : U.val = V.val) : U = V := by
  cases U; cases V
  simp at h
  subst h
  rfl
scoped[CKMMatrix] notation (name := ud_element) "[" V "]ud" => V.1 0 0
scoped[CKMMatrix] notation (name := us_element) "[" V "]us" => V.1 0 1
scoped[CKMMatrix] notation (name := ub_element) "[" V "]ub" => V.1 0 2
scoped[CKMMatrix] notation (name := cd_element) "[" V "]cd" => V.1 1 0
scoped[CKMMatrix] notation (name := cs_element) "[" V "]cs" => V.1 1 1
scoped[CKMMatrix] notation (name := cb_element) "[" V "]cb" => V.1 1 2
scoped[CKMMatrix] notation (name := td_element) "[" V "]td" => V.1 2 0
scoped[CKMMatrix] notation (name := ts_element) "[" V "]ts" => V.1 2 1
scoped[CKMMatrix] notation (name := tb_element) "[" V "]tb" => V.1 2 2

instance CKMMatrixSetoid : Setoid CKMMatrix := ⟨phaseShiftRelation, phaseShiftEquivRelation⟩

@[simps!]
def phaseShiftApply (V : CKMMatrix) (a b c d e f : ℝ) : CKMMatrix :=
    phaseShift a b c * ↑V * phaseShift d e f

namespace phaseShiftApply
lemma equiv (V : CKMMatrix) (a b c d e f : ℝ) :
    V ≈ phaseShiftApply V a b c d e f := by
  symm
  use a, b, c, d, e, f
  rfl

lemma ud (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 0 0 = cexp (a * I + d * I) * V.1 0 0  := by
  simp
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  change _ + _ * _ * 0 = _
  rw [exp_add]
  ring_nf

lemma us (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 0 1 = cexp (a * I + e * I) * V.1 0 1  := by
  simp
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  rw [exp_add]
  ring_nf

lemma ub (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 0 2 = cexp (a * I + f * I) * V.1 0 2  := by
  simp
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  rw [exp_add]
  ring_nf

lemma cd (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 1 0= cexp (b * I + d * I) * V.1 1 0 := by
  simp
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  change _ + _ * _ * 0 = _
  rw [exp_add]
  ring_nf

lemma cs (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 1 1 = cexp (b * I + e * I) * V.1 1 1 := by
  simp
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  rw [exp_add]
  ring_nf

lemma cb (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 1 2 = cexp (b * I + f * I) * V.1 1 2 := by
  simp
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  rw [exp_add]
  ring_nf

lemma td (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 2 0= cexp (c * I + d * I) * V.1 2 0 := by
  simp
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  change (0 * _  + _ ) * _ + (0 * _  + _ ) * 0 = _
  simp
  rw [exp_add]
  ring_nf

lemma ts (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 2 1 = cexp (c * I + e * I) * V.1 2 1 := by
  simp
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  change (0 * _ + _) * _ = _
  rw [exp_add]
  ring_nf

lemma tb (V : CKMMatrix) (a b c d e f : ℝ) :
    (phaseShiftApply V a b c d e f).1 2 2 = cexp (c * I + f * I) * V.1 2 2 := by
  simp
  rw [mul_apply, Fin.sum_univ_three]
  rw [mul_apply, mul_apply, mul_apply, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  change (0 * _ + _) * _ = _
  rw [exp_add]
  ring_nf

end phaseShiftApply



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


namespace CKMMatrix
open ComplexConjugate


section ratios

def Rubud (V : CKMMatrix) : ℂ := [V]ub / [V]ud

scoped[CKMMatrix] notation (name := ub_ud_ratio) "[" V "]ub|ud" => Rubud V

def Rusud (V : CKMMatrix) : ℂ := [V]us / [V]ud

scoped[CKMMatrix] notation (name := us_ud_ratio) "[" V "]us|ud" => Rusud V

def Rudus (V : CKMMatrix) : ℂ := [V]ud / [V]us

scoped[CKMMatrix] notation (name := ud_us_ratio) "[" V "]ud|us" => Rudus V

def Rubus (V : CKMMatrix) : ℂ := [V]ub / [V]us

scoped[CKMMatrix] notation (name := ub_us_ratio) "[" V "]ub|us" => Rubus V

def Rcdcb (V : CKMMatrix) : ℂ := [V]cd / [V]cb

scoped[CKMMatrix] notation (name := cd_cb_ratio) "[" V "]cd|cb" => Rcdcb V

lemma Rcdcb_mul_cb {V : CKMMatrix} (h : [V]cb ≠ 0): [V]cd = Rcdcb V * [V]cb := by
  rw [Rcdcb]
  exact (div_mul_cancel₀ (V.1 1 0) h).symm

def Rcscb (V : CKMMatrix) : ℂ := [V]cs / [V]cb

scoped[CKMMatrix] notation (name := cs_cb_ratio) "[" V "]cs|cb" => Rcscb V

lemma Rcscb_mul_cb {V : CKMMatrix} (h : [V]cb ≠ 0): [V]cs = Rcscb V * [V]cb := by
  rw [Rcscb]
  exact (div_mul_cancel₀ [V]cs h).symm


def Rtb!cbud (V : CKMMatrix) : ℂ := conj [V]tb / ([V]cb * [V]ud)

scoped[CKMMatrix] notation (name := tb_cb_ud_ratio) "[" V "]tb*|cb|ud" => Rtb!cbud V

def Rtb!cbus (V : CKMMatrix) : ℂ := conj [V]tb / ([V]cb * [V]us)

scoped[CKMMatrix] notation (name := tb_cb_us_ratio) "[" V "]tb*|cb|us" => Rtb!cbus V


end ratios


end CKMMatrix

end
