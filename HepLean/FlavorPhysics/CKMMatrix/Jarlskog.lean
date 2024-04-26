/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import HepLean.FlavorPhysics.CKMMatrix.Rows
import HepLean.FlavorPhysics.CKMMatrix.PhaseFreedom
import HepLean.FlavorPhysics.CKMMatrix.Ratios
import HepLean.FlavorPhysics.CKMMatrix.StandardParameters
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Matrix Complex
open ComplexConjugate
open CKMMatrix


noncomputable section

@[simps!]
def jarlskogComplexCKM (V : CKMMatrix) : ℂ :=
  [V]us * [V]cb * conj [V]ub * conj [V]cs

lemma jarlskogComplexCKM_equiv  (V U : CKMMatrix) (h : V ≈ U) :
    jarlskogComplexCKM V = jarlskogComplexCKM U := by
  obtain ⟨a, b, c, e, f, g, h⟩ := h
  change V = phaseShiftApply U a b c e f g  at h
  rw [h]
  simp only [jarlskogComplexCKM, Fin.isValue, phaseShiftApply.ub,
  phaseShiftApply.us, phaseShiftApply.cb, phaseShiftApply.cs]
  simp [← exp_conj, conj_ofReal, exp_add, exp_neg]
  have ha : cexp (↑a * I) ≠ 0 := exp_ne_zero _
  have hb : cexp (↑b * I) ≠ 0 := exp_ne_zero _
  have hf : cexp (↑f * I) ≠ 0 := exp_ne_zero _
  have hg : cexp (↑g * I) ≠ 0 := exp_ne_zero _
  field_simp
  ring

def inv₁  (V : Quotient CKMMatrixSetoid) : ℝ  :=
    VusAbs V ^ 2 * VubAbs V ^ 2  * VcbAbs V ^2 /(VudAbs V ^ 2 + VusAbs V ^2)

lemma inv₁_sP (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) (h1 : 0 ≤ Real.sin θ₁₂)
  (h2 : 0 ≤ Real.cos θ₁₃) (h3 : 0 ≤ Real.sin θ₂₃) (h4 : 0 ≤ Real.cos θ₁₂) :
    inv₁ ⟦sP θ₁₂ θ₁₃ θ₂₃ δ₁₃⟧ =
    Real.sin θ₁₂ ^ 2 * Real.cos θ₁₃ ^ 2 * Real.sin θ₁₃ ^ 2 * Real.sin θ₂₃ ^ 2 := by
  simp only [inv₁, VusAbs, VAbs, VAbs', Fin.isValue, sP, standardParameterizationAsMatrix,
     neg_mul, Quotient.lift_mk, cons_val', cons_val_one, head_cons,
    empty_val', cons_val_fin_one, cons_val_zero, _root_.map_mul, VubAbs, cons_val_two, tail_cons,
    VcbAbs, VudAbs, Complex.abs_ofReal]
  by_cases hx : Real.cos θ₁₃ ≠ 0
  ·
    rw [Complex.abs_exp]
    simp
    rw [_root_.abs_of_nonneg h1, _root_.abs_of_nonneg h3, _root_.abs_of_nonneg h2,
      _root_.abs_of_nonneg h4]
    simp [sq]
    ring_nf
    nth_rewrite 2 [Real.sin_sq θ₁₂]
    ring_nf
    field_simp
    ring
  · simp at hx
    rw [hx]
    simp



@[simp]
def jarlskogComplex : Quotient CKMMatrixSetoid → ℂ :=
  Quotient.lift jarlskogComplexCKM jarlskogComplexCKM_equiv

-- bad name
def expδ₁₃ (V : Quotient CKMMatrixSetoid) : ℂ :=
    jarlskogComplex V + inv₁ V

lemma expδ₁₃_sP (θ₁₂ θ₁₃ θ₂₃ δ₁₃ : ℝ) (h1 : 0 ≤ Real.sin θ₁₂)
  (h2 : 0 ≤ Real.cos θ₁₃) (h3 : 0 ≤ Real.sin θ₂₃) (h4 : 0 ≤ Real.cos θ₁₂)  :
    expδ₁₃ ⟦sP θ₁₂ θ₁₃ θ₂₃ δ₁₃⟧ =
      sin θ₁₂ * cos θ₁₃ ^ 2 * sin θ₂₃ * sin θ₁₃ * cos θ₁₂ * cos θ₂₃ * cexp (I * δ₁₃)  := by
  rw [expδ₁₃]
  rw [inv₁_sP _ _ _ _ h1 h2 h3 h4 ]
  simp only [expδ₁₃, jarlskogComplex, sP, standardParameterizationAsMatrix, neg_mul,
    Quotient.lift_mk, jarlskogComplexCKM, Fin.isValue, cons_val', cons_val_one, head_cons,
    empty_val', cons_val_fin_one, cons_val_zero, cons_val_two, tail_cons, _root_.map_mul, ←
    exp_conj, map_neg, conj_I, conj_ofReal, neg_neg, map_sub]
  simp
  ring_nf
  rw [exp_neg]
  have h1 : cexp (I * δ₁₃) ≠ 0 := exp_ne_zero _
  field_simp


lemma expδ₁₃_sP_V (V : CKMMatrix) (δ₁₃ : ℝ) :
    expδ₁₃ ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃⟧ =
    sin (θ₁₂ ⟦V⟧) * cos (θ₁₃ ⟦V⟧) ^ 2 * sin (θ₂₃ ⟦V⟧) * sin (θ₁₃ ⟦V⟧)
    * cos (θ₁₂ ⟦V⟧) * cos (θ₂₃ ⟦V⟧) * cexp (I * δ₁₃)  := by
  refine expδ₁₃_sP _ _ _ _ ?_ ?_ ?_ ?_
  rw [S₁₂_eq_sin_θ₁₂]
  exact S₁₂_nonneg _
  exact Real.cos_arcsin_nonneg _
  rw [S₂₃_eq_sin_θ₂₃]
  exact S₂₃_nonneg _
  exact Real.cos_arcsin_nonneg _


lemma expδ₁₃_eq_zero (V : CKMMatrix) (δ₁₃ : ℝ) :
    expδ₁₃ ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃⟧ = 0 ↔
     VudAbs ⟦V⟧ = 0 ∨ VubAbs ⟦V⟧ = 0 ∨ VusAbs ⟦V⟧ = 0 ∨ VcbAbs ⟦V⟧ = 0 ∨ VtbAbs ⟦V⟧ = 0 := by
  rw [VudAbs_eq_C₁₂_mul_C₁₃, VubAbs_eq_S₁₃, VusAbs_eq_S₁₂_mul_C₁₃, VcbAbs_eq_S₂₃_mul_C₁₃,  VtbAbs_eq_C₂₃_mul_C₁₃,
  ← ofReal_inj,
  ← ofReal_inj, ← ofReal_inj,  ← ofReal_inj, ← ofReal_inj]
  simp only [ofReal_mul]
  rw [← S₁₃_eq_ℂsin_θ₁₃, ← S₁₂_eq_ℂsin_θ₁₂, ← S₂₃_eq_ℂsin_θ₂₃,
  ← C₁₃_eq_ℂcos_θ₁₃, ← C₂₃_eq_ℂcos_θ₂₃,← C₁₂_eq_ℂcos_θ₁₂]
  simp
  rw [expδ₁₃_sP_V]
  simp
  have h1 := exp_ne_zero (I * δ₁₃)
  simp_all
  aesop

lemma inv₂_V_arg (V : CKMMatrix) (δ₁₃ : ℝ)
    (h1 : expδ₁₃ ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃⟧ ≠ 0 ) :
    cexp (arg (expδ₁₃ ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃⟧) * I) =
    cexp (δ₁₃ * I) := by
  have h1a := expδ₁₃_sP_V V δ₁₃
  have habs : Complex.abs (expδ₁₃  ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃⟧) =
      sin (θ₁₂ ⟦V⟧) * cos (θ₁₃ ⟦V⟧) ^ 2 * sin (θ₂₃ ⟦V⟧) * sin (θ₁₃ ⟦V⟧)
      * cos (θ₁₂ ⟦V⟧) * cos (θ₂₃ ⟦V⟧) := by
    rw [h1a]
    simp [abs_exp]
    rw [complexAbs_sin_θ₁₃, complexAbs_cos_θ₁₃, complexAbs_sin_θ₁₂, complexAbs_cos_θ₁₂,
    complexAbs_sin_θ₂₃, complexAbs_cos_θ₂₃]
  have h2 : expδ₁₃  ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃⟧ =
      Complex.abs (expδ₁₃  ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃⟧) * exp (δ₁₃ * I) := by
    rw [habs, h1a]
    ring_nf
  nth_rewrite 1 [← abs_mul_exp_arg_mul_I (expδ₁₃  ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃⟧ )] at h2
  have habs_neq_zero : (Complex.abs (expδ₁₃  ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃⟧) : ℂ) ≠ 0 := by
    simp
    exact h1
  rw [← mul_right_inj' habs_neq_zero]
  rw [← h2]

def δ₁₃ (V : Quotient CKMMatrixSetoid) : ℝ := arg (expδ₁₃ V)

theorem eq_standardParameterization_δ₃ (V : CKMMatrix) :
    V ≈ sP (θ₁₂ ⟦V⟧) (θ₁₃ ⟦V⟧) (θ₂₃ ⟦V⟧) (δ₁₃ ⟦V⟧) := by
  obtain ⟨δ₁₃', hδ₃⟩ := exists_standardParameterization V
  have hSV := (Quotient.eq.mpr (hδ₃))
  by_cases h : expδ₁₃ ⟦sP (θ₁₂ ⟦V⟧) (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃'⟧ ≠ 0
  have h1 := inv₂_V_arg V δ₁₃' h
  have h2 := eq_phases_sP (θ₁₂ ⟦V⟧)  (θ₁₃  ⟦V⟧) (θ₂₃  ⟦V⟧) δ₁₃'
    (δ₁₃ ⟦V⟧) (by  rw [← h1, ← hSV, δ₁₃])
  rw [h2] at hδ₃
  exact hδ₃
  simp at h
  have h1 : δ₁₃ ⟦V⟧ = 0 := by
    rw [hSV, δ₁₃, h]
    simp
  rw [h1]
  rw [expδ₁₃_eq_zero, Vs_zero_iff_cos_sin_zero] at h
  cases' h with h h
  exact phaseShiftEquivRelation.trans hδ₃ (sP_cos_θ₁₂_eq_zero δ₁₃' h )
  cases' h with h h
  exact phaseShiftEquivRelation.trans hδ₃ (sP_cos_θ₁₃_eq_zero δ₁₃' h )
  cases' h with h h
  exact phaseShiftEquivRelation.trans hδ₃ (sP_cos_θ₂₃_eq_zero δ₁₃' h )
  cases' h with h h
  exact phaseShiftEquivRelation.trans hδ₃ (sP_sin_θ₁₂_eq_zero δ₁₃' h )
  cases' h with h h
  exact phaseShiftEquivRelation.trans hδ₃ (sP_sin_θ₁₃_eq_zero δ₁₃' h )
  exact phaseShiftEquivRelation.trans hδ₃ (sP_sin_θ₂₃_eq_zero δ₁₃' h )


end
