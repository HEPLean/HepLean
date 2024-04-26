/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Rows
import HepLean.FlavorPhysics.CKMMatrix.Relations
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import HepLean.FlavorPhysics.CKMMatrix.PhaseFreedom

open Matrix Complex


noncomputable section

namespace CKMMatrix
open ComplexConjugate

-- A
def Rubud (V : CKMMatrix) : ℂ := [V]ub / [V]ud

scoped[CKMMatrix] notation (name := ub_ud_ratio) "[" V "]ub|ud" => Rubud V
-- B
def Rusud (V : CKMMatrix) : ℂ := [V]us / [V]ud

scoped[CKMMatrix] notation (name := us_ud_ratio) "[" V "]us|ud" => Rusud V

def Rudus (V : CKMMatrix) : ℂ := [V]ud / [V]us

scoped[CKMMatrix] notation (name := ud_us_ratio) "[" V "]ud|us" => Rudus V

def Rubus (V : CKMMatrix) : ℂ := [V]ub / [V]us

scoped[CKMMatrix] notation (name := ub_us_ratio) "[" V "]ub|us" => Rubus V
-- D
def Rcdcb (V : CKMMatrix) : ℂ := [V]cd / [V]cb

scoped[CKMMatrix] notation (name := cd_cb_ratio) "[" V "]cd|cb" => Rcdcb V

lemma Rcdcb_mul_cb {V : CKMMatrix} (h : [V]cb ≠ 0): [V]cd = Rcdcb V * [V]cb := by
  rw [Rcdcb]
  exact (div_mul_cancel₀ (V.1 1 0) h).symm

-- C'
def Rcscb (V : CKMMatrix) : ℂ := [V]cs / [V]cb

scoped[CKMMatrix] notation (name := cs_cb_ratio) "[" V "]cs|cb" => Rcscb V

lemma Rcscb_mul_cb {V : CKMMatrix} (h : [V]cb ≠ 0): [V]cs = Rcscb V * [V]cb := by
  rw [Rcscb]
  exact (div_mul_cancel₀ [V]cs h).symm


def Rtb!cbud (V : CKMMatrix) : ℂ := conj [V]tb / ([V]cb * [V]ud)

scoped[CKMMatrix] notation (name := tb_cb_ud_ratio) "[" V "]tb*|cb|ud" => Rtb!cbud V

def Rtb!cbus (V : CKMMatrix) : ℂ := conj [V]tb / ([V]cb * [V]us)

scoped[CKMMatrix] notation (name := tb_cb_us_ratio) "[" V "]tb*|cb|us" => Rtb!cbus V

lemma orthog_fst_snd_row_ratios {V : CKMMatrix} (hb : [V]ud ≠ 0) (ha : [V]cb ≠ 0) :
    [V]cd|cb + [V]cs|cb  * conj ([V]us|ud) + conj ([V]ub|ud) = 0 := by
  have h1 : ([V]cd * conj ([V]ud) + [V]cs * conj ([V]us)
      + [V]cb * conj ([V]ub)) / ([V]cb * conj ([V]ud)) = 0 := by
    rw [fst_row_snd_row V ]
    simp only [Fin.isValue, zero_div]
  rw [← div_add_div_same, ← div_add_div_same] at h1
  rw [mul_div_mul_comm, mul_div_mul_comm, mul_div_mul_comm] at h1
  rw [div_self, div_self] at h1
  change Rcdcb V * 1 + _ + _ = _ at h1
  have h2 : (starRingEnd ℂ) (V.1 0 2) / (starRingEnd ℂ) (V.1 0 0) = conj (Rubud V) := by
    simp [Rubud]
  have h3 : ((starRingEnd ℂ) (V.1 0 1) / (starRingEnd ℂ) (V.1 0 0)) = conj (Rusud V) := by
    simp [Rusud]
  rw [h2, h3] at h1
  simp at h1
  exact h1
  exact ha
  simpa using hb

lemma orthog_fst_snd_row_ratios_cb_us {V : CKMMatrix} (hb : [V]us ≠ 0) (ha : [V]cb ≠ 0) :
    [V]cd|cb * conj ([V]ud|us) + [V]cs|cb  + conj ([V]ub|us) = 0 := by
  have h1 : ([V]cd * conj ([V]ud) + [V]cs * conj ([V]us)
      + [V]cb * conj ([V]ub)) / ([V]cb * conj ([V]us)) = 0 := by
    rw [fst_row_snd_row V ]
    simp only [Fin.isValue, zero_div]
  rw [← div_add_div_same, ← div_add_div_same] at h1
  rw [mul_div_mul_comm, mul_div_mul_comm, mul_div_mul_comm] at h1
  rw [div_self, div_self] at h1
  change  _ + _ * 1 + _ = _ at h1
  have h2 : (starRingEnd ℂ) (V.1 0 2) / (starRingEnd ℂ) (V.1 0 1) = conj (Rubus V) := by
    simp [Rubus]
  have h3 : ((starRingEnd ℂ) (V.1 0 0) / (starRingEnd ℂ) (V.1 0 1)) = conj (Rudus V) := by
    simp [Rudus]
  rw [h2, h3] at h1
  simp at h1
  exact h1
  exact ha
  simpa using hb

def R' (V : CKMMatrix) : ℂ := [V]cs|cb * (1 + normSq [V]us|ud) + conj ([V]ub|ud) * [V]us|ud

def R's (V : CKMMatrix) : ℂ := [V]cd|cb * (normSq [V]ud|us + 1) + conj ([V]ub|us) * [V]ud|us

lemma R'_eq (V : CKMMatrix) :
    R' V = [V]cs|cb * (1 + normSq ([V]us|ud)) + conj ([V]ub|ud) * [V]us|ud := by rfl

lemma R's_eq (V : CKMMatrix) :
    R's V = [V]cd|cb * (normSq ([V]ud|us) + 1) + conj ([V]ub|us) * [V]ud|us := by rfl

lemma one_plus_normSq_Rusud_neq_zero_ℝ (V : CKMMatrix):
    1 + normSq ([V]us|ud) ≠ 0 := by
  have h1 : 0 ≤ (normSq ([V]us|ud)) := normSq_nonneg ([V]us|ud)
  have h2 : 0 < 1 + normSq ([V]us|ud) := by linarith
  by_contra hn
  have h3 := lt_of_lt_of_eq h2 hn
  simp at h3

lemma normSq_Rudus_plus_one_neq_zero_ℝ (V : CKMMatrix):
    normSq ([V]ud|us) + 1 ≠ 0 := by
  have h1 : 0 ≤ (normSq ([V]ud|us)) := normSq_nonneg ([V]ud|us)
  have h2 : 0 < normSq ([V]ud|us) + 1 := by linarith
  by_contra hn
  have h3 := lt_of_lt_of_eq h2 hn
  simp at h3

lemma one_plus_normSq_Rusud_neq_zero_ℂ  (V : CKMMatrix):
    1 + (normSq ([V]us|ud) : ℂ) ≠ 0 := by
  by_contra hn
  have h1 := one_plus_normSq_Rusud_neq_zero_ℝ V
  simp at h1
  rw [← ofReal_inj] at h1
  simp_all only [ofReal_add, ofReal_one, ofReal_zero, not_true_eq_false]

lemma normSq_Rudus_plus_one_neq_zero_ℂ (V : CKMMatrix):
    (normSq ([V]ud|us) : ℂ) + 1 ≠ 0 := by
  by_contra hn
  have h1 := normSq_Rudus_plus_one_neq_zero_ℝ V
  simp at h1
  rw [← ofReal_inj] at h1
  simp_all only [ofReal_add, ofReal_one, ofReal_zero, not_true_eq_false]

lemma Rcscb_of_R' (V : CKMMatrix) :
    [V]cs|cb = (R' V - conj [V]ub|ud * [V]us|ud) / (1 + normSq [V]us|ud) := by
  have h2 : R' V - conj ([V]ub|ud) * [V]us|ud = [V]cs|cb * (1 + normSq [V]us|ud) := by
    linear_combination R'_eq V
  rw [h2]
  rw [mul_div_cancel_right₀]
  exact one_plus_normSq_Rusud_neq_zero_ℂ V

lemma Rcdcb_of_R's (V : CKMMatrix) :
    [V]cd|cb = (R's V - conj [V]ub|us * [V]ud|us) / (normSq [V]ud|us + 1) := by
  have h2 : R's V - conj ([V]ub|us) * [V]ud|us = [V]cd|cb * (normSq [V]ud|us + 1) := by
    linear_combination R's_eq V
  rw [h2]
  rw [mul_div_cancel_right₀]
  exact normSq_Rudus_plus_one_neq_zero_ℂ V

lemma Rcdcb_R'_orthog {V : CKMMatrix} (hb : [V]ud ≠ 0) (ha : [V]cb ≠ 0) :
    [V]cd|cb + (conj [V]ub|ud + R' V * conj [V]us|ud ) / (1 + normSq [V]us|ud) = 0 := by
  have h1 := orthog_fst_snd_row_ratios hb ha
  rw [Rcscb_of_R'] at h1
  rw [div_mul_eq_mul_div] at h1
  rw [add_assoc] at h1
  rw [div_add'] at h1
  have h2 : (R' V - conj [V]ub|ud * [V]us|ud) * conj [V]us|ud +
      conj [V]ub|ud * (1 + normSq [V]us|ud) = conj [V]ub|ud + R' V * conj [V]us|ud := by
    rw [← mul_conj]
    ring
  rw [h2] at h1
  exact h1
  exact one_plus_normSq_Rusud_neq_zero_ℂ V

lemma Rcdcb_of_R' {V : CKMMatrix}  (hb : [V]ud ≠ 0) (ha : [V]cb ≠ 0) :
    [V]cd|cb = - (conj [V]ub|ud + R' V * conj [V]us|ud ) / (1 + normSq [V]us|ud) := by
  linear_combination (Rcdcb_R'_orthog hb ha)

lemma Rcscb_R's_orthog {V : CKMMatrix} (hb : [V]us ≠ 0) (ha : [V]cb ≠ 0) :
    [V]cs|cb + (conj [V]ub|us + R's V * conj [V]ud|us ) / (normSq [V]ud|us + 1) = 0 := by
  have h1 := orthog_fst_snd_row_ratios_cb_us hb ha
  rw [Rcdcb_of_R's] at h1
  rw [div_mul_eq_mul_div] at h1
  rw [add_assoc, add_comm [V]cs|cb, ← add_assoc] at h1
  rw [div_add', add_comm] at h1
  have h2 : (R's V - conj [V]ub|us * [V]ud|us) * conj [V]ud|us +
        (starRingEnd ℂ) [V]ub|us * ((normSq [V]ud|us) + 1)= conj [V]ub|us + R's V * conj [V]ud|us := by
    rw [← mul_conj]
    ring
  rw [h2] at h1
  exact h1
  exact normSq_Rudus_plus_one_neq_zero_ℂ V

lemma Rcscb_of_R's {V : CKMMatrix}  (hb : [V]us ≠ 0) (ha : [V]cb ≠ 0) :
   [V]cs|cb = - (conj [V]ub|us + R's V * conj [V]ud|us ) / (normSq [V]ud|us + 1) := by
  linear_combination (Rcscb_R's_orthog hb ha)

lemma R'_of_Rcscb_Rcdcb  {V : CKMMatrix}  (hb : [V]ud ≠ 0) (ha : [V]cb ≠ 0) :
    R' V = [V]cs|cb - [V]us|ud * [V]cd|cb := by
  rw [Rcdcb_of_R' hb ha, Rcscb_of_R']
  have h1 := one_plus_normSq_Rusud_neq_zero_ℂ V
  have h2 : conj [V]ud ≠ 0 := (AddEquivClass.map_ne_zero_iff starRingAut).mpr hb
  field_simp
  rw [Rubud, map_div₀, Rusud, map_div₀, map_div₀]
  simp
  rw [normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
  field_simp
  ring

lemma R's_of_Rcscb_Rcdcb  {V : CKMMatrix}  (hb : [V]us ≠ 0) (ha : [V]cb ≠ 0) :
    R's V = [V]cd|cb - [V]ud|us * [V]cs|cb := by
  rw [Rcscb_of_R's hb ha, Rcdcb_of_R's]
  have h1 := normSq_Rudus_plus_one_neq_zero_ℂ V
  have h2 : conj [V]us ≠ 0 := (AddEquivClass.map_ne_zero_iff starRingAut).mpr hb
  field_simp
  rw [Rubus, map_div₀, Rudus, map_div₀, map_div₀]
  simp
  rw [normSq_eq_conj_mul_self, normSq_eq_conj_mul_self]
  field_simp
  ring

lemma R'_of_Rtb!cbud {V : CKMMatrix}  (hb : [V]ud ≠ 0) (ha : [V]cb ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    R' V = cexp (τ * I) * [V]tb*|cb|ud  := by
  have h1 : cexp (- τ * I) = conj (cexp (τ * I)) := by
    rw [← exp_conj]
    simp only [neg_mul, _root_.map_mul, conj_I, mul_neg]
    rw [conj_ofReal]
  have h2 : [V]tb*|cb|ud = cexp (- τ * I) * R' V  := by
    rw [h1, R'_of_Rcscb_Rcdcb hb ha]
    have h1 := congrFun hτ 2
    simp [crossProduct, tRow, uRow, cRow] at h1
    apply congrArg conj at h1
    simp at h1
    rw [Rtb!cbud, Rcscb, Rusud, Rcdcb, h1]
    field_simp
    ring
  rw [h2, ← mul_assoc, ← exp_add]
  simp


lemma R's_of_Rtb!cbus {V : CKMMatrix}  (hb : [V]us ≠ 0) (ha : [V]cb ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    R's V = - cexp (τ * I) * [V]tb*|cb|us  := by
  have h1 : cexp (- τ * I) = conj (cexp (τ * I)) := by
    rw [← exp_conj]
    simp only [neg_mul, _root_.map_mul, conj_I, mul_neg]
    rw [conj_ofReal]
  have h2 : [V]tb*|cb|us = - cexp (- τ * I) * R's V  := by
    rw [h1, R's_of_Rcscb_Rcdcb hb ha]
    have h1 := congrFun hτ 2
    simp [crossProduct, tRow, uRow, cRow] at h1
    apply congrArg conj at h1
    simp at h1
    rw [Rtb!cbus, Rcscb, Rudus, Rcdcb, h1]
    field_simp
    ring
  rw [h2]
  simp
  rw [← mul_assoc, ← exp_add]
  simp

lemma over_normSq_Rusud (V : CKMMatrix) (hb : [V]ud ≠ 0) (a : ℂ) : a / (1 + normSq [V]us|ud) =
    (a * normSq [V]ud) / (normSq [V]ud + normSq [V]us) := by
  rw [Rusud]
  field_simp
  rw [one_add_div]
  field_simp
  simp
  exact hb

lemma over_normSq_Rudus (V : CKMMatrix) (hb : [V]us ≠ 0) (a : ℂ) : a / (normSq [V]ud|us + 1) =
    (a * normSq [V]us) / (normSq [V]ud + normSq [V]us) := by
  rw [Rudus]
  field_simp
  rw [div_add_one]
  field_simp
  simp
  exact hb

lemma cd_of_ud_neq_zero {V : CKMMatrix}  (hb : [V]ud ≠ 0) (ha : [V]cb ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    [V]cd = - (conj [V]ub * [V]ud * [V]cb  + cexp (τ * I) * conj [V]tb  * conj [V]us) /
      (normSq [V]ud + normSq [V]us) := by
  obtain hτ2 := R'_of_Rtb!cbud hb ha hτ
  rw [Rcdcb_mul_cb ha]
  rw [Rcdcb_of_R' hb ha, hτ2]
  rw [over_normSq_Rusud V hb, div_mul_eq_mul_div]
  congr 1
  rw [normSq_eq_conj_mul_self, Rubud, map_div₀, Rusud, map_div₀, Rtb!cbud]
  have h1 : conj [V]ud ≠ 0 := (AddEquivClass.map_ne_zero_iff starRingAut).mpr hb
  field_simp
  ring

lemma cs_of_ud_neq_zero {V : CKMMatrix}  (hb : [V]ud ≠ 0) (ha : [V]cb ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    [V]cs = (- conj [V]ub * [V]us  * [V]cb +
      cexp (τ * I) * conj [V]tb * conj [V]ud ) /(normSq [V]ud + normSq [V]us) := by
  have hτ2 := R'_of_Rtb!cbud hb ha hτ
  rw [Rcscb_mul_cb ha]
  rw [Rcscb_of_R', hτ2]
  rw [over_normSq_Rusud V hb, div_mul_eq_mul_div]
  congr 1
  rw [normSq_eq_conj_mul_self, Rusud, Rtb!cbud, Rubud, map_div₀]
  have h1 : conj [V]ud ≠ 0 := (AddEquivClass.map_ne_zero_iff starRingAut).mpr hb
  field_simp
  ring



lemma cd_of_us_neq_zero {V : CKMMatrix}  (hb : [V]us ≠ 0) (ha : [V]cb ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    [V]cd =
      - (conj [V]ub * [V]ud * [V]cb + cexp (τ * I) * conj [V]tb  * conj [V]us) /
      (normSq [V]ud + normSq [V]us) := by
  have hτ2 := R's_of_Rtb!cbus hb ha hτ
  rw [Rcdcb_mul_cb ha]
  rw [Rcdcb_of_R's, hτ2]
  rw [over_normSq_Rudus V hb, div_mul_eq_mul_div]
  congr 1
  rw [normSq_eq_conj_mul_self, Rubus, map_div₀, Rudus, Rtb!cbus]
  have h1 : conj [V]us ≠ 0 := (AddEquivClass.map_ne_zero_iff starRingAut).mpr hb
  field_simp
  ring

lemma cs_of_us_neq_zero {V : CKMMatrix}  (hb : [V]us ≠ 0) (ha : [V]cb ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    [V]cs = ( - conj [V]ub * [V]us  * [V]cb +
      cexp (τ * I) * conj [V]tb * conj [V]ud ) / (normSq [V]ud + normSq [V]us) := by
  have hτ2 := R's_of_Rtb!cbus hb ha hτ
  rw [Rcscb_mul_cb ha]
  rw [Rcscb_of_R's hb ha, hτ2]
  rw [over_normSq_Rudus V hb, div_mul_eq_mul_div]
  congr 1
  rw [normSq_eq_conj_mul_self, Rudus, map_div₀, Rtb!cbus, Rubus, map_div₀]
  have h1 : conj [V]us ≠ 0 := (AddEquivClass.map_ne_zero_iff starRingAut).mpr hb
  field_simp
  ring

lemma cd_of_us_or_ud_neq_zero {V : CKMMatrix}  (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    [V]cd = - (conj [V]ub * [V]ud * [V]cb  + cexp (τ * I) * conj [V]tb  * conj [V]us) /
      (normSq [V]ud + normSq [V]us) := by
  cases' hb with hb hb
  exact cd_of_ud_neq_zero hb ha hτ
  exact cd_of_us_neq_zero hb ha hτ


lemma cs_of_us_or_ud_neq_zero {V : CKMMatrix}  (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb ≠ 0)
    {τ : ℝ} (hτ : [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))) :
    [V]cs = (- conj [V]ub * [V]us * [V]cb +
      cexp (τ * I) * conj [V]tb * conj [V]ud ) / (normSq [V]ud + normSq [V]us) := by
  cases' hb with hb hb
  exact cs_of_ud_neq_zero hb ha hτ
  exact cs_of_us_neq_zero hb ha hτ



lemma cd_of_us_or_ud_neq_zero_UCond {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb ≠ 0)
    (hV : UCond₁ V) : [V]cd = (- VtbAbs ⟦V⟧ * VusAbs ⟦V⟧ / (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2)) +
    (- VubAbs ⟦V⟧ * VudAbs ⟦V⟧ * VcbAbs ⟦V⟧ / (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2 )) * cexp (- arg [V]ub * I)
      := by
  have hτ : [V]t = cexp ((0 : ℝ) * I) • (conj ([V]u) ×₃ conj ([V]c)) := by
    simp
    exact hV.2.2.2.2
  rw [cd_of_us_or_ud_neq_zero hb ha hτ]
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

lemma cs_of_us_or_ud_neq_zero_UCond {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb ≠ 0)
    (hV : UCond₁ V) : [V]cs = (VtbAbs ⟦V⟧ * VudAbs ⟦V⟧ / (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2))
      + (- VubAbs ⟦V⟧ *  VusAbs ⟦V⟧ * VcbAbs ⟦V⟧/ (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2)) * cexp (- arg [V]ub * I)
      := by
  have hτ : [V]t = cexp ((0 : ℝ) * I) • (conj ([V]u) ×₃ conj ([V]c)) := by
    simp
    exact hV.2.2.2.2
  rw [cs_of_us_or_ud_neq_zero hb ha hτ]
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

lemma cd_of_cb_zero {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb = 0)
  {κ : ℝ} (hκ :  [V]u = cexp (κ * I) • (conj [V]c ×₃ conj [V]t)) :
    [V]cd = - cexp (κ * I)  * conj [V]tb  * conj [V]us / (normSq [V]ud + normSq [V]us) := by
  have h2 : [V]cd = - cexp (κ * I) * conj [V]us / [V]tb := by
    have h1 := congrFun hκ 1
    simp [crossProduct, tRow, uRow, cRow] at h1
    rw [ha] at h1
    apply congrArg conj at h1
    simp at h1
    rw [h1]
    have hx := tb_neq_zero_of_cb_zero_ud_us_neq_zero ha hb
    field_simp
    have h1 : conj (cexp (↑κ * I)) = cexp (- κ * I) := by
      simp [← exp_conj, conj_ofReal]
    rw [h1]
    rw [← mul_assoc]
    rw [← exp_add]
    simp
  rw [div_td_of_cb_zero_ud_us_neq_zero ha hb] at h2
  rw [h2]
  congr 1
  ring

lemma cs_of_cb_zero {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb = 0)
     {κ : ℝ} (hκ1 : [V]u = cexp (κ * I) • (conj [V]c ×₃ conj [V]t)) :
    [V]cs = cexp (κ * I) * conj [V]tb * conj [V]ud / (normSq [V]ud + normSq [V]us) := by
  have h2 : [V]cs = cexp (κ * I) * conj [V]ud / [V]tb := by
    have h1 := congrFun hκ1 0
    simp [crossProduct, tRow, uRow, cRow] at h1
    rw [ha] at h1
    apply congrArg conj at h1
    simp at h1
    rw [h1]
    have hx := tb_neq_zero_of_cb_zero_ud_us_neq_zero ha hb
    field_simp
    have h1 : conj (cexp (↑κ * I)) = cexp (- κ * I) := by
      rw [← exp_conj]
      simp only [neg_mul, _root_.map_mul, conj_I, mul_neg]
      rw [conj_ofReal]
    rw [h1]
    rw [← mul_assoc]
    rw [← exp_add]
    simp
  rw [div_td_of_cb_zero_ud_us_neq_zero ha hb] at h2
  rw [h2]
  congr 1
  ring

lemma cd_of_cb_zero_UCond {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb = 0)
    (hV : UCond₁ V) {κ : ℝ} (hκ1 : [V]u = cexp (κ * I) • (conj [V]c ×₃ conj [V]t)) :
    [V]cd =  (- VtbAbs ⟦V⟧  * VusAbs ⟦V⟧ / (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2)) * cexp (κ * I) := by
  rw [cd_of_cb_zero hb ha hκ1]
  rw [hV.1, hV.2.1, hV.2.2.2.1]
  simp [sq, conj_ofReal]
  have hx := Vabs_sq_add_neq_zero hb
  field_simp
  ring_nf
  simp

lemma cs_of_cb_zero_UCond {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb = 0)
    (hV : UCond₁ V) {κ : ℝ} (hκ1 : [V]u = cexp (κ * I) • (conj [V]c ×₃ conj [V]t)) :
    [V]cs =  (VtbAbs ⟦V⟧  * VudAbs ⟦V⟧ / (VudAbs ⟦V⟧ ^2 + VusAbs ⟦V⟧ ^2)) * cexp (κ * I) := by
  rw [cs_of_cb_zero hb ha hκ1]
  rw [hV.1, hV.2.1, hV.2.2.2.1]
  simp [sq, conj_ofReal]
  have hx := Vabs_sq_add_neq_zero hb
  field_simp
  ring_nf

def UCond₂ (U : CKMMatrix) : Prop := [U]ud = VudAbs ⟦U⟧ ∧ [U]us = VusAbs ⟦U⟧
    ∧ [U]ub = VubAbs ⟦U⟧ ∧ [U]t = conj [U]u ×₃ conj [U]c
    ∧  [U]cd = (- VtbAbs ⟦U⟧  * VusAbs ⟦U⟧ / (VudAbs ⟦U⟧ ^2 + VusAbs ⟦U⟧ ^2)) ∧
     [U]cs = (VtbAbs ⟦U⟧  * VudAbs ⟦U⟧ / (VudAbs ⟦U⟧ ^2 + VusAbs ⟦U⟧ ^2))

lemma UCond₂_solv {V : CKMMatrix} (h1 : a + d = 0) (h2 :  a + e = 0) (h3 : a + f = - arg [V]ub)
    (h4 : 0 = - a - b - c - d - e - f) (h5 : b + d = - κ) (h6 : b + e = - κ) :
    b = - κ + a ∧
    c =  κ + arg [V]ub + a ∧
    d =  - a ∧
    e =  - a ∧
    f = - arg [V]ub - a := by
  have hd : d = - a := by
    linear_combination h1
  subst hd
  have he : e = - a := by
    linear_combination h2
  subst he
  simp_all
  have hb : b = - κ + a := by
    linear_combination h6
  subst hb
  simp_all
  have hf : f = - arg [V]ub - a := by
    linear_combination h3
  subst hf
  simp_all
  ring_nf at h4
  have hc : c = κ + arg [V]ub + a := by
    linear_combination h4
  simp_all


lemma UCond₂_exists {V : CKMMatrix} (hb : [V]ud ≠ 0 ∨ [V]us ≠ 0) (ha : [V]cb = 0)
    (hV : UCond₁ V) : ∃ (U : CKMMatrix), V ≈ U ∧ UCond₂ U:= by
  obtain ⟨κ, hκ⟩ := V.cRow_cross_tRow_eq_uRow
  let U : CKMMatrix := phaseShiftApply V 0 (- κ) (κ + arg [V]ub) 0 0 (- arg [V]ub)
  use U
  have hUV : ⟦U⟧ = ⟦V⟧ := by
    simp
    symm
    exact phaseShiftApply.equiv  _ _ _ _ _ _ _
  apply And.intro
  exact phaseShiftApply.equiv _ _ _ _ _ _ _
  apply And.intro
  · rw [hUV]
    apply ud_eq_abs  _ _ _ _ _ _ _
    rw [hV.1, arg_ofReal_of_nonneg]
    simp
    exact Complex.abs.nonneg _
  apply And.intro
  · rw [hUV]
    apply us_eq_abs  _ _ _ _ _ _ _
    rw [hV.2.1, arg_ofReal_of_nonneg]
    simp
    exact Complex.abs.nonneg _
  apply And.intro
  · rw [hUV]
    apply ub_eq_abs  _ _ _ _ _ _ _
    ring
  apply And.intro
  · have hτ : [V]t = cexp ((0 : ℝ) * I) • (conj ([V]u) ×₃ conj ([V]c)) := by
      simp
      exact hV.2.2.2.2
    apply t_eq_conj _ _ _ _ _ _ hτ.symm
    ring
  apply And.intro
  · rw [phaseShiftApply.cd]
    rw [cd_of_cb_zero_UCond hb ha hV hκ]
    rw [mul_comm, mul_assoc, ← exp_add, hUV]
    simp
  · rw [phaseShiftApply.cs]
    rw [cs_of_cb_zero_UCond hb ha hV hκ]
    rw [mul_comm, mul_assoc, ← exp_add, hUV]
    simp


section zero

def UCond₃ (U : CKMMatrix) :  Prop :=
    [U]ud = 0 ∧ [U]us = 0 ∧ [U]cb = 0 ∧
    [U]ub = 1 ∧ [U]t = conj [U]u ×₃ conj [U]c
    ∧ [U]cd = - VcdAbs ⟦U⟧ ∧ [U]cs = √(1 - VcdAbs ⟦U⟧ ^ 2)

lemma UCond₃_solv {V : CKMMatrix} (h1 : a + f = - arg [V]ub) (h2 : 0 = - a - b - c - d - e - f)
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
  simp
  rw [@abs_le]
  have h1 := VAbs_leq_one 1 0 ⟦V⟧
  have h0 := VAbs_ge_zero 1 0 ⟦V⟧
  simp_all
  have hn : -1 ≤ (0 : ℝ) := by simp
  exact hn.trans h0
  exact VAbs_ge_zero _ _ ⟦V⟧


lemma UCond₃_exists {V : CKMMatrix} (hb :¬ ([V]ud ≠ 0 ∨ [V]us ≠ 0)) (hV : UCond₁ V)  :
    ∃ (U : CKMMatrix), V ≈ U ∧ UCond₃ U:= by
  let U : CKMMatrix := phaseShiftApply V 0 0 (- Real.pi + arg [V]cd + arg [V]cs + arg [V]ub)
    (Real.pi - arg [V]cd ) (- arg [V]cs)  (- arg [V]ub )
  use U
  have hUV : ⟦U⟧ = ⟦V⟧ := by
    simp
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
      apply ub_eq_abs  _ _ _ _ _ _ _
      ring
    rw [hU1]
    have h1:= (ud_us_neq_zero_iff_ub_neq_one V).mpr.mt hb
    simpa using h1
  apply And.intro
  · have hτ : [V]t = cexp ((0 : ℝ) * I) • (conj ([V]u) ×₃ conj ([V]c)) := by
      simp
      exact hV.2.2.2.2
    apply t_eq_conj _ _ _ _ _ _ hτ.symm
    ring
  apply And.intro
  · rw [hUV]
    apply cd_eq_neg_abs  _ _ _ _ _ _ _
    ring
  have hcs : [U]cs = VcsAbs ⟦U⟧ := by
    rw [hUV]
    apply cs_eq_abs _ _ _ _ _ _ _
    ring
  rw [hcs, hUV, cs_of_ud_us_zero hb]




end zero

end CKMMatrix
end
