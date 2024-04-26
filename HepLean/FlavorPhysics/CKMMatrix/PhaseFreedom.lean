/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Rows
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Matrix Complex


noncomputable section
namespace CKMMatrix
open ComplexConjugate
variable (a b c d e f : ℝ)

lemma ud_eq_abs (V : CKMMatrix) (h1 : a + d = - arg [V]ud) :
    [phaseShiftApply V a b c d e f]ud = VudAbs ⟦V⟧ := by
  rw [phaseShiftApply.ud]
  rw [← abs_mul_exp_arg_mul_I [V]ud]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg (V.1 0 0)) * I + (↑a * I + ↑d * I) = ↑(arg (V.1 0 0) + (a + d)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma us_eq_abs {V : CKMMatrix} (h1 : a + e = - arg [V]us) :
    [phaseShiftApply V a b c d e f]us = VusAbs ⟦V⟧ := by
  rw [phaseShiftApply.us]
  rw [← abs_mul_exp_arg_mul_I [V]us]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]us) * I + (↑a * I + ↑e * I) = ↑(arg [V]us + (a + e)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma ub_eq_abs {V : CKMMatrix} (h1 : a + f = - arg [V]ub) :
    [phaseShiftApply V a b c d e f]ub = VubAbs ⟦V⟧ := by
  rw [phaseShiftApply.ub]
  rw [← abs_mul_exp_arg_mul_I [V]ub]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]ub) * I + (↑a * I + ↑f * I) = ↑(arg [V]ub + (a + f)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma cs_eq_abs {V : CKMMatrix} (h1 : b + e = - arg [V]cs) :
    [phaseShiftApply V a b c d e f]cs = VcsAbs ⟦V⟧ := by
  rw [phaseShiftApply.cs]
  rw [← abs_mul_exp_arg_mul_I [V]cs]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]cs) * I + (↑b * I + ↑e * I) = ↑(arg [V]cs + (b + e)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma cb_eq_abs {V : CKMMatrix} (h1 : b + f = - arg [V]cb) :
    [phaseShiftApply V a b c d e f]cb = VcbAbs ⟦V⟧ := by
  rw [phaseShiftApply.cb]
  rw [← abs_mul_exp_arg_mul_I [V]cb]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]cb) * I + (↑b * I + ↑f * I) = ↑(arg [V]cb + (b + f)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma tb_eq_abs {V : CKMMatrix} (h1 : c + f = - arg [V]tb) :
    [phaseShiftApply V a b c d e f]tb = VtbAbs ⟦V⟧ := by
  rw [phaseShiftApply.tb]
  rw [← abs_mul_exp_arg_mul_I [V]tb]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]tb) * I + (↑c * I + ↑f * I) = ↑(arg [V]tb + (c + f)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma cd_eq_neg_abs {V : CKMMatrix} (h1 : b + d = Real.pi - arg [V]cd) :
    [phaseShiftApply V a b c d e f]cd = - VcdAbs ⟦V⟧ := by
  rw [phaseShiftApply.cd]
  rw [← abs_mul_exp_arg_mul_I [V]cd]
  rw [mul_comm, mul_assoc, ← exp_add]
  have h2 : ↑(arg [V]cd) * I + (↑b * I + ↑d * I) = ↑(arg [V]cd + (b + d)) * I := by
    simp [add_assoc]
    ring
  rw [h2, h1]
  simp
  rfl

lemma t_eq_conj {V : CKMMatrix} {τ : ℝ} (hτ : cexp (τ * I) • (conj [V]u ×₃ conj [V]c) = [V]t)
  (h1 : τ = - a - b - c - d - e - f) :
    [phaseShiftApply V a b c d e f]t =
    conj [phaseShiftApply V a b c d e f]u ×₃ conj [phaseShiftApply V a b c d e f]c := by
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
    simp
    ring
  · simp
    rw [phaseShiftApply.ucCross_snd]
    simp [tRow, phaseShiftApply.ts]
    have hτ0 := congrFun hτ 1
    simp [tRow] at hτ0
    rw [← hτ0]
    rw [← mul_assoc, ← exp_add, h1]
    congr 2
    simp
    ring
  · simp
    rw [phaseShiftApply.ucCross_thd]
    simp [tRow, phaseShiftApply.tb]
    have hτ0 := congrFun hτ 2
    simp [tRow] at hτ0
    rw [← hτ0]
    rw [← mul_assoc, ← exp_add, h1]
    congr 2
    simp
    ring

-- bad name for this lemma
lemma all_cond_sol {V : CKMMatrix} (h1 : a + d = - arg [V]ud) (h2 :  a + e = - arg [V]us) (h3 : b + f = - arg [V]cb)
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

-- rename
def UCond₁ (U : CKMMatrix) : Prop := [U]ud = VudAbs ⟦U⟧ ∧ [U]us = VusAbs ⟦U⟧
    ∧ [U]cb = VcbAbs ⟦U⟧ ∧ [U]tb = VtbAbs ⟦U⟧ ∧ [U]t = conj [U]u ×₃ conj [U]c

lemma all_eq_abs (V : CKMMatrix) :
    ∃ (U : CKMMatrix), V ≈ U ∧ UCond₁ U:= by
  obtain ⟨τ, hτ⟩ := V.uRow_cross_cRow_eq_tRow
  let U : CKMMatrix := phaseShiftApply V
    0
    (- τ  + arg [V]ud + arg [V]us + arg [V]tb )
    (- τ + arg [V]cb  + arg [V]ud + arg [V]us )
    (- arg [V]ud )
    (- arg [V]us)
    (τ - arg [V]ud - arg [V]us - arg [V]cb - arg [V]tb)
  have hUV : ⟦U⟧ = ⟦V⟧ := by
    simp
    symm
    exact phaseShiftApply.equiv  _ _ _ _ _ _ _
  use U
  apply And.intro
  exact phaseShiftApply.equiv _ _ _ _ _ _ _
  apply And.intro
  rw [hUV]
  apply ud_eq_abs  _ _ _ _ _ _ _
  ring
  apply And.intro
  rw [hUV]
  apply us_eq_abs
  ring
  apply And.intro
  rw [hUV]
  apply cb_eq_abs
  ring
  apply And.intro
  rw [hUV]
  apply tb_eq_abs
  ring
  apply t_eq_conj _ _ _ _ _ _ hτ.symm
  ring






end CKMMatrix
end
