/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Rows
import HepLean.FlavorPhysics.CKMMatrix.Relations
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-!
# Phase freedom of the CKM Matrix

The CKM matrix is only defined up to an equivalence. This leads to a freedom
to shift the phases of the matrices elements of the CKM matrix.

In this file we define two sets of conditions on the CKM matrices
`fstRowThdColRealCond` which we show can be satisfied by any CKM matrix up to equivalence
and `ubOnePhaseCond` which we show can be satisfied by any CKM matrix up to equivalence as long as
the ub element as absolute value 1.


-/
open Matrix Complex


noncomputable section
namespace CKMMatrix
open ComplexConjugate

section phaseShiftApply
variable (u c t d s b : ℝ)

lemma shift_ud_phase_zero (V : CKMMatrix) (h1 : u + d = - arg [V]ud) :
    [phaseShiftApply V u c t d s b]ud = VudAbs ⟦V⟧ := by
  rw [phaseShiftApply.ud]
  rw [← abs_mul_exp_arg_mul_I [V]ud]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg (V.1 0 0)) * I + (↑u * I + ↑d * I) = ↑(arg (V.1 0 0) + (u + d)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma shift_us_phase_zero {V : CKMMatrix} (h1 : u + s = - arg [V]us) :
    [phaseShiftApply V u c t d s b]us = VusAbs ⟦V⟧ := by
  rw [phaseShiftApply.us]
  rw [← abs_mul_exp_arg_mul_I [V]us]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]us) * I + (↑u * I + ↑s * I) = ↑(arg [V]us + (u + s)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma shift_ub_phase_zero {V : CKMMatrix} (h1 : u + b = - arg [V]ub) :
    [phaseShiftApply V u c t d s b]ub = VubAbs ⟦V⟧ := by
  rw [phaseShiftApply.ub]
  rw [← abs_mul_exp_arg_mul_I [V]ub]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]ub) * I + (↑u * I + ↑b * I) = ↑(arg [V]ub + (u + b)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma shift_cs_phase_zero {V : CKMMatrix} (h1 : c + s = - arg [V]cs) :
    [phaseShiftApply V u c t d s b]cs = VcsAbs ⟦V⟧ := by
  rw [phaseShiftApply.cs]
  rw [← abs_mul_exp_arg_mul_I [V]cs]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]cs) * I + (↑c * I + ↑s * I) = ↑(arg [V]cs + (c + s)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma shift_cb_phase_zero {V : CKMMatrix} (h1 : c + b = - arg [V]cb) :
    [phaseShiftApply V u c t d s b]cb = VcbAbs ⟦V⟧ := by
  rw [phaseShiftApply.cb]
  rw [← abs_mul_exp_arg_mul_I [V]cb]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]cb) * I + (↑c * I + ↑b * I) = ↑(arg [V]cb + (c + b)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma shift_tb_phase_zero {V : CKMMatrix} (h1 : t + b = - arg [V]tb) :
    [phaseShiftApply V u c t d s b]tb = VtbAbs ⟦V⟧ := by
  rw [phaseShiftApply.tb]
  rw [← abs_mul_exp_arg_mul_I [V]tb]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]tb) * I + (↑t * I + ↑b * I) = ↑(arg [V]tb + (t + b)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma shift_cd_phase_pi {V : CKMMatrix} (h1 : c + d = Real.pi - arg [V]cd) :
    [phaseShiftApply V u c t d s b]cd = - VcdAbs ⟦V⟧ := by
  rw [phaseShiftApply.cd]
  rw [← abs_mul_exp_arg_mul_I [V]cd]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]cd) * I + (↑c * I + ↑d * I) = ↑(arg [V]cd + (c + d)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma shift_cross_product_phase_zero {V : CKMMatrix} {τ : ℝ}
    (hτ : cexp (τ * I) • (conj [V]u ×₃ conj [V]c) = [V]t) (h1 : τ = - u - c - t - d - s - b) :
    [phaseShiftApply V u c t d s b]t =
    conj [phaseShiftApply V u c t d s b]u ×₃ conj [phaseShiftApply V u c t d s b]c := by
  change _ = phaseShiftApply.ucCross _ _ _ _ _ _ _
  funext i
  fin_cases i
  · simp
    rw [phaseShiftApply.ucCross_fst]
    simp [tRow, phaseShiftApply.td]
    have hτ0 := congrFun hτ 0
    simp [tRow] at hτ0
    rw [← hτ0]
    rw [← mul_assoc,  ← exp_add, h1]
    congr 2
    simp only [ofReal_sub, ofReal_neg]
    ring
  · simp
    rw [phaseShiftApply.ucCross_snd]
    simp [tRow, phaseShiftApply.ts]
    have hτ0 := congrFun hτ 1
    simp [tRow] at hτ0
    rw [← hτ0]
    rw [← mul_assoc, ← exp_add, h1]
    congr 2
    simp only [ofReal_sub, ofReal_neg]
    ring
  · simp
    rw [phaseShiftApply.ucCross_thd]
    simp [tRow, phaseShiftApply.tb]
    have hτ0 := congrFun hτ 2
    simp [tRow] at hτ0
    rw [← hτ0]
    rw [← mul_assoc, ← exp_add, h1]
    congr 2
    simp only [ofReal_sub, ofReal_neg]
    ring

end phaseShiftApply

variable (a b c d e f : ℝ)

/-- A proposition which is satisfied by a CKM matrix if its `ud`, `us`, `cb` and `tb` elements
are positive and real, and there is no phase difference between the `t`th-row and
the cross product of the conjugates of the `u`th and `c`th rows. -/
def fstRowThdColRealCond (U : CKMMatrix) : Prop := [U]ud = VudAbs ⟦U⟧ ∧ [U]us = VusAbs ⟦U⟧
    ∧ [U]cb = VcbAbs ⟦U⟧ ∧ [U]tb = VtbAbs ⟦U⟧ ∧ [U]t = conj [U]u ×₃ conj [U]c

/-- A proposition which is satisfied by a CKM matrix `ub` is one, `ud`, `us` and `cb` are zero,
  there is no phase difference between the `t`th-row and
the cross product of the conjugates of the `u`th and `c`th rows, and the `cd`th and `cs`th
elements are real and related in a set way.
 -/
def ubOnePhaseCond (U : CKMMatrix) :  Prop :=
    [U]ud = 0 ∧ [U]us = 0 ∧ [U]cb = 0 ∧ [U]ub = 1 ∧ [U]t = conj [U]u ×₃ conj [U]c
    ∧ [U]cd = - VcdAbs ⟦U⟧ ∧ [U]cs = √(1 - VcdAbs ⟦U⟧ ^ 2)

lemma fstRowThdColRealCond_shift_solution {V : CKMMatrix} (h1 : a + d = - arg [V]ud)
    (h2 :  a + e = - arg [V]us) (h3 : b + f = - arg [V]cb)
    (h4 : c + f = - arg [V]tb) (h5 : τ = - a - b - c - d - e - f) :
    b = - τ  + arg [V]ud + arg [V]us + arg [V]tb + a ∧
    c = - τ + arg [V]cb  + arg [V]ud + arg [V]us + a ∧
    d = - arg [V]ud - a ∧
    e = - arg [V]us - a ∧
    f = τ - arg [V]ud - arg [V]us - arg [V]cb - arg [V]tb - a := by
  have hd : d = - arg [V]ud - a := by
    linear_combination h1
  subst hd
  have he : e = - arg [V]us - a := by
    linear_combination h2
  subst he
  simp_all
  have hbf : b = - arg [V]cb - f := by
    linear_combination h3
  have hcf : c = - arg [V]tb - f := by
    linear_combination h4
  rw [hbf, hcf] at h5
  simp_all
  ring_nf at h5
  have hf : f = τ - a - arg [V]ud - arg [V]us - arg [V]cb - arg [V]tb := by
    linear_combination -(1 * h5)
  rw [hf] at hbf hcf
  ring_nf at hbf hcf
  subst hf hbf hcf
  ring_nf
  simp

lemma ubOnePhaseCond_shift_solution {V : CKMMatrix} (h1 : a + f = - arg [V]ub)
    (h2 : 0 = - a - b - c - d - e - f)
    (h3 :  b + d = Real.pi - arg [V]cd) (h5 : b + e = - arg [V]cs)  :
    c =  - Real.pi + arg [V]cd + arg [V]cs + arg [V]ub + b  ∧
    d =  Real.pi - arg [V]cd - b ∧
    e =  - arg [V]cs - b  ∧
    f =  - arg [V]ub - a := by
  have hf : f = - arg [V]ub - a := by
    linear_combination h1
  subst hf
  have he : e = - arg [V]cs - b := by
    linear_combination h5
  have hd : d = Real.pi - arg [V]cd - b := by
    linear_combination h3
  subst he hd
  simp_all
  ring_nf at h2
  have hc : c = - Real.pi + arg [V]cd + arg [V]cs + arg [V]ub + b := by
    linear_combination h2
  subst hc
  ring

-- rename
lemma fstRowThdColRealCond_holds_up_to_equiv (V : CKMMatrix) :
    ∃ (U : CKMMatrix), V ≈ U ∧ fstRowThdColRealCond U:= by
  obtain ⟨τ, hτ⟩ := V.uRow_cross_cRow_eq_tRow
  let U : CKMMatrix := phaseShiftApply V
    0
    (- τ  + arg [V]ud + arg [V]us + arg [V]tb )
    (- τ + arg [V]cb  + arg [V]ud + arg [V]us )
    (- arg [V]ud )
    (- arg [V]us)
    (τ - arg [V]ud - arg [V]us - arg [V]cb - arg [V]tb)
  have hUV : ⟦U⟧ = ⟦V⟧ := by
    simp only [Quotient.eq]
    symm
    exact phaseShiftApply.equiv  _ _ _ _ _ _ _
  use U
  apply And.intro
  exact phaseShiftApply.equiv _ _ _ _ _ _ _
  apply And.intro
  rw [hUV]
  apply shift_ud_phase_zero  _ _ _ _ _ _ _
  ring
  apply And.intro
  rw [hUV]
  apply shift_us_phase_zero
  ring
  apply And.intro
  rw [hUV]
  apply shift_cb_phase_zero
  ring
  apply And.intro
  rw [hUV]
  apply shift_tb_phase_zero
  ring
  apply shift_cross_product_phase_zero _ _ _ _ _ _ hτ.symm
  ring


lemma ubOnePhaseCond_hold_up_to_equiv_of_ub_one {V : CKMMatrix} (hb : ¬ ([V]ud ≠ 0 ∨ [V]us ≠ 0))
    (hV : fstRowThdColRealCond V)  :
    ∃ (U : CKMMatrix), V ≈ U ∧ ubOnePhaseCond U:= by
  let U : CKMMatrix := phaseShiftApply V 0 0 (- Real.pi + arg [V]cd + arg [V]cs + arg [V]ub)
    (Real.pi - arg [V]cd ) (- arg [V]cs)  (- arg [V]ub )
  use U
  have hUV : ⟦U⟧ = ⟦V⟧ := by
    simp only [Quotient.eq]
    symm
    exact phaseShiftApply.equiv  _ _ _ _ _ _ _
  apply And.intro
  exact phaseShiftApply.equiv _ _ _ _ _ _ _
  apply And.intro
  · simp [not_or] at hb
    have h1 : VudAbs ⟦U⟧ = 0 := by
      rw [hUV]
      simp [VAbs, hb]
    simp [VAbs] at h1
    exact h1
  apply And.intro
  · simp [not_or] at hb
    have h1 : VusAbs ⟦U⟧ = 0 := by
      rw [hUV]
      simp [VAbs, hb]
    simp [VAbs] at h1
    exact h1
  apply And.intro
  · simp [not_or] at hb
    have h3 := cb_eq_zero_of_ud_us_zero hb
    have h1 : VcbAbs ⟦U⟧ = 0 := by
      rw [hUV]
      simp [VAbs, h3]
    simp [VAbs] at h1
    exact h1
  apply And.intro
  · have hU1 : [U]ub = VubAbs ⟦V⟧ := by
      apply shift_ub_phase_zero  _ _ _ _ _ _ _
      ring
    rw [hU1]
    have h1:= (ud_us_neq_zero_iff_ub_neq_one V).mpr.mt hb
    simpa using h1
  apply And.intro
  · have hτ : [V]t = cexp ((0 : ℝ) * I) • (conj ([V]u) ×₃ conj ([V]c)) := by
      simp only [ofReal_zero, zero_mul, exp_zero, one_smul]
      exact hV.2.2.2.2
    apply shift_cross_product_phase_zero _ _ _ _ _ _ hτ.symm
    ring
  apply And.intro
  · rw [hUV]
    apply shift_cd_phase_pi  _ _ _ _ _ _ _
    ring
  have hcs : [U]cs = VcsAbs ⟦U⟧ := by
    rw [hUV]
    apply shift_cs_phase_zero _ _ _ _ _ _ _
    ring
  rw [hcs, hUV, cs_of_ud_us_zero hb]


lemma cd_of_fstRowThdColRealCond {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0)
    (hV : fstRowThdColRealCond V) :
    [V]cd = (- VtbAbs ⟦V⟧ * VusAbs ⟦V⟧ / (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2)) +
    (- VubAbs ⟦V⟧ * VudAbs ⟦V⟧ * VcbAbs ⟦V⟧ / (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2 ))
    * cexp (- arg [V]ub * I) := by
  have hτ : [V]t = cexp ((0 : ℝ) * I) • (conj ([V]u) ×₃ conj ([V]c)) := by
    simp only [ofReal_zero, zero_mul, exp_zero, one_smul]
    exact hV.2.2.2.2
  rw [cd_of_ud_us_ub_cb_tb hb hτ]
  rw [hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1]
  simp [sq, conj_ofReal]
  have hx := Vabs_sq_add_neq_zero hb
  field_simp
  have h1 : conj [V]ub = VubAbs ⟦V⟧ * cexp (- arg [V]ub * I) := by
    nth_rewrite 1 [← abs_mul_exp_arg_mul_I [V]ub]
    rw [@RingHom.map_mul]
    simp [conj_ofReal, ← exp_conj, VAbs]
  rw [h1]
  ring_nf

lemma cs_of_fstRowThdColRealCond {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0)
    (hV : fstRowThdColRealCond V) :
    [V]cs = (VtbAbs ⟦V⟧ * VudAbs ⟦V⟧ / (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2))
    + (- VubAbs ⟦V⟧ *  VusAbs ⟦V⟧ * VcbAbs ⟦V⟧/ (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2))
    * cexp (- arg [V]ub * I) := by
  have hτ : [V]t = cexp ((0 : ℝ) * I) • (conj ([V]u) ×₃ conj ([V]c)) := by
    simp only [ofReal_zero, zero_mul, exp_zero, one_smul]
    exact hV.2.2.2.2
  rw [cs_of_ud_us_ub_cb_tb hb hτ]
  rw [hV.1, hV.2.1, hV.2.2.1, hV.2.2.2.1]
  simp [sq, conj_ofReal]
  have hx := Vabs_sq_add_neq_zero hb
  field_simp
  have h1 : conj [V]ub = VubAbs ⟦V⟧ * cexp (- arg [V]ub * I) := by
    nth_rewrite 1 [← abs_mul_exp_arg_mul_I [V]ub]
    rw [@RingHom.map_mul]
    simp [conj_ofReal, ← exp_conj, VAbs]
  rw [h1]
  ring_nf

end CKMMatrix
end
