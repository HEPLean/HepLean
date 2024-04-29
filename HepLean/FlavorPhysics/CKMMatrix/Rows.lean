/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.FlavorPhysics.CKMMatrix.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.CrossProduct


open Matrix Complex

open ComplexConjugate
noncomputable section

namespace CKMMatrix


def uRow (V : CKMMatrix) : Fin 3 → ℂ := ![[V]ud, [V]us, [V]ub]
scoped[CKMMatrix] notation (name := u_row) "[" V "]u" => uRow V

def cRow (V : CKMMatrix) : Fin 3 → ℂ := ![[V]cd, [V]cs, [V]cb]
scoped[CKMMatrix] notation (name := c_row) "[" V "]c" => cRow V

def tRow (V : CKMMatrix) : Fin 3 → ℂ := ![[V]td, [V]ts, [V]tb]
scoped[CKMMatrix] notation (name := t_row) "[" V "]t" => tRow V

lemma uRow_normalized (V : CKMMatrix) : conj [V]u ⬝ᵥ [V]u = 1 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm (V.1 0 0) _, mul_comm (V.1 0 1) _, mul_comm (V.1 0 2) _] at ht
  exact ht

lemma cRow_normalized (V : CKMMatrix) : conj [V]c ⬝ᵥ [V]c = 1 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm (V.1 1 0) _, mul_comm (V.1 1 1) _, mul_comm (V.1 1 2) _] at ht
  exact ht

lemma uRow_cRow_orthog (V : CKMMatrix) : conj [V]u ⬝ᵥ [V]c = 0 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

lemma uRow_tRow_orthog (V : CKMMatrix) : conj [V]u ⬝ᵥ [V]t = 0 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 2) 0
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

lemma cRow_uRow_orthog (V : CKMMatrix) : conj [V]c ⬝ᵥ [V]u = 0 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

lemma cRow_tRow_orthog (V : CKMMatrix) : conj [V]c ⬝ᵥ [V]t = 0 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

lemma tRow_normalized (V : CKMMatrix) : conj [V]t ⬝ᵥ [V]t = 1 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm (V.1 2 0) _, mul_comm (V.1 2 1) _, mul_comm (V.1 2 2) _] at ht
  exact ht

lemma tRow_uRow_orthog (V : CKMMatrix) : conj [V]t ⬝ᵥ [V]u = 0 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 0) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

lemma tRow_cRow_orthog (V : CKMMatrix) : conj [V]t ⬝ᵥ [V]c = 0 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [mul_comm (V.1 _ 0) _, mul_comm (V.1 _ 1) _, mul_comm (V.1 _ 2) _] at ht
  exact ht

lemma uRow_cross_cRow_conj (V : CKMMatrix) : conj (conj [V]u ×₃ conj [V]c) =  [V]u ×₃ [V]c := by
  simp [crossProduct]
  funext i
  fin_cases i <;> simp

lemma cRow_cross_tRow_conj (V : CKMMatrix) : conj (conj [V]c ×₃ conj [V]t) =  [V]c ×₃ [V]t := by
  simp [crossProduct]
  funext i
  fin_cases i <;> simp

lemma uRow_cross_cRow_normalized (V : CKMMatrix) :
     conj (conj [V]u ×₃ conj [V]c) ⬝ᵥ (conj [V]u ×₃ conj [V]c) = 1 := by
  rw [uRow_cross_cRow_conj, cross_dot_cross]
  rw [dotProduct_comm, uRow_normalized, dotProduct_comm, cRow_normalized]
  rw [dotProduct_comm, cRow_uRow_orthog, dotProduct_comm, uRow_cRow_orthog]
  simp

lemma cRow_cross_tRow_normalized (V : CKMMatrix) :
     conj (conj [V]c ×₃ conj [V]t) ⬝ᵥ (conj [V]c ×₃ conj [V]t) = 1 := by
  rw [cRow_cross_tRow_conj, cross_dot_cross]
  rw [dotProduct_comm, cRow_normalized, dotProduct_comm, tRow_normalized]
  rw [dotProduct_comm, tRow_cRow_orthog, dotProduct_comm, cRow_tRow_orthog]
  simp

@[simp]
def rows (V : CKMMatrix) : Fin 3 → Fin 3 → ℂ := fun i =>
  match i with
  | 0 => uRow V
  | 1 => cRow V
  | 2 => tRow V

def rowsLinearlyIndependent (V : CKMMatrix) : LinearIndependent ℂ (rows V) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp at hg
  have h0 := congrArg (fun X => conj [V]u  ⬝ᵥ X) hg
  have h1 := congrArg (fun X => conj [V]c  ⬝ᵥ X) hg
  have h2 := congrArg (fun X => conj [V]t  ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_add, dotProduct_smul, Pi.conj_apply,
    smul_eq_mul, dotProduct_zero] at h0 h1 h2
  rw [uRow_normalized, uRow_cRow_orthog, uRow_tRow_orthog] at h0
  rw [cRow_normalized, cRow_uRow_orthog, cRow_tRow_orthog] at h1
  rw [tRow_normalized, tRow_uRow_orthog, tRow_cRow_orthog] at h2
  simp at h0 h1 h2
  intro i
  fin_cases i
  exact h0
  exact h1
  exact h2

lemma rows_card :  Fintype.card (Fin 3) = FiniteDimensional.finrank ℂ (Fin 3 → ℂ) := by
  simp only [Fintype.card_fin, FiniteDimensional.finrank_fintype_fun_eq_card]

@[simps!]
noncomputable def rowBasis (V : CKMMatrix) : Basis (Fin 3) ℂ (Fin 3 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (rowsLinearlyIndependent V) rows_card

lemma cRow_cross_tRow_eq_uRow (V : CKMMatrix) :
    ∃ (κ : ℝ), [V]u = cexp (κ * I) • (conj [V]c ×₃ conj [V]t) := by
  obtain ⟨g, hg⟩ := (mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span (rowBasis V)
    (conj [V]c ×₃ conj [V]t))
  rw [Fin.sum_univ_three, rowBasis] at hg
  simp at hg
  have h0 := congrArg (fun X => conj [V]c  ⬝ᵥ X) hg
  have h1 := congrArg (fun X => conj [V]t  ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_add, dotProduct_smul, Pi.conj_apply,
    smul_eq_mul, dotProduct_zero] at h0 h1
  rw [cRow_normalized, cRow_uRow_orthog, cRow_tRow_orthog, dot_self_cross] at h0
  rw [tRow_normalized, tRow_uRow_orthog, tRow_cRow_orthog, dot_cross_self] at h1
  simp at h0 h1
  rw [h0, h1] at hg
  simp at hg
  have h2 := congrArg (fun X => conj X  ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_smul, Pi.conj_apply, Pi.smul_apply,
    smul_eq_mul, _root_.map_mul] at h2
  rw [cRow_cross_tRow_normalized] at h2
  have h3 : conj (g 0 • [V]u)  = conj (g 0) • conj [V]u := by
    funext i
    fin_cases i <;> simp
  rw [h3] at h2
  simp only [Fin.isValue, smul_dotProduct, Pi.conj_apply, smul_eq_mul] at h2
  rw [uRow_normalized] at h2
  simp at h2
  rw [mul_conj] at h2
  rw [← Complex.sq_abs] at h2
  simp at h2
  cases' h2  with h2 h2
  swap
  have hx : Complex.abs (g 0) = -1 := by
    rw [← ofReal_inj]
    simp
    exact h2
  have h3 := Complex.abs.nonneg (g 0)
  simp_all
  have h4 : (0 : ℝ) < 1 := by norm_num
  exact False.elim (lt_iff_not_le.mp h4 h3)
  have hx : [V]u =  (g 0)⁻¹ • (conj ([V]c) ×₃ conj ([V]t)) := by
    rw [← hg]
    rw [@smul_smul]
    rw [inv_mul_cancel]
    simp
    by_contra hn
    rw [hn] at h2
    simp at h2
  have hg2 : Complex.abs (g 0)⁻¹ = 1 := by
    rw [@map_inv₀, h2]
    simp
  have hg22 : ∃ (τ : ℝ), (g 0)⁻¹ = Complex.exp (τ * I) := by
    rw [← abs_mul_exp_arg_mul_I (g 0)⁻¹]
    rw [hg2]
    use arg (g 0)⁻¹
    simp
  obtain ⟨τ, hτ⟩ := hg22
  use τ
  rw [hx, hτ]

lemma uRow_cross_cRow_eq_tRow (V : CKMMatrix) :
    ∃ (τ : ℝ), [V]t = cexp (τ * I) • (conj ([V]u) ×₃ conj ([V]c))  := by
  obtain ⟨g, hg⟩ := (mem_span_range_iff_exists_fun ℂ).mp (Basis.mem_span (rowBasis V)
    (conj ([V]u) ×₃ conj ([V]c)) )
  rw [Fin.sum_univ_three, rowBasis] at hg
  simp at hg
  have h0 := congrArg (fun X => conj [V]u  ⬝ᵥ X) hg
  have h1 := congrArg (fun X => conj [V]c  ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_add, dotProduct_smul, Pi.conj_apply,
    smul_eq_mul, dotProduct_zero] at h0 h1
  rw [uRow_normalized, uRow_cRow_orthog, uRow_tRow_orthog, dot_self_cross] at h0
  rw [cRow_normalized, cRow_uRow_orthog, cRow_tRow_orthog, dot_cross_self] at h1
  simp at h0 h1
  rw [h0, h1] at hg
  simp at hg
  have h2 := congrArg (fun X => conj X  ⬝ᵥ X) hg
  simp only [Fin.isValue, dotProduct_smul, Pi.conj_apply, Pi.smul_apply,
    smul_eq_mul, _root_.map_mul] at h2
  rw [uRow_cross_cRow_normalized] at h2
  have h3 : conj (g 2 • [V]t)  = conj (g 2) • conj [V]t := by
    funext i
    fin_cases i <;> simp
  rw [h3] at h2
  simp only [Fin.isValue, smul_dotProduct, Pi.conj_apply, smul_eq_mul] at h2
  rw [tRow_normalized] at h2
  simp at h2
  rw [mul_conj] at h2
  rw [← Complex.sq_abs] at h2
  simp at h2
  cases' h2  with h2 h2
  swap
  have hx : Complex.abs (g 2) = -1 := by
    rw [← ofReal_inj]
    simp
    exact h2
  have h3 := Complex.abs.nonneg (g 2)
  simp_all
  have h4 : (0 : ℝ) < 1 := by norm_num
  exact False.elim (lt_iff_not_le.mp h4 h3)
  have hx : [V]t =  (g 2)⁻¹ • (conj ([V]u) ×₃ conj ([V]c)) := by
    rw [← hg]
    rw [@smul_smul]
    rw [inv_mul_cancel]
    simp
    by_contra hn
    rw [hn] at h2
    simp at h2
  have hg2 : Complex.abs (g 2)⁻¹ = 1 := by
    rw [@map_inv₀, h2]
    simp
  have hg22 : ∃ (τ : ℝ), (g 2)⁻¹ = Complex.exp (τ * I) := by
    rw [← abs_mul_exp_arg_mul_I (g 2)⁻¹]
    rw [hg2]
    use arg (g 2)⁻¹
    simp
  obtain ⟨τ, hτ⟩ := hg22
  use τ
  rw [hx, hτ]


def uRow₁₂ (V : CKMMatrix) : Fin 2 → ℂ := ![[V]ud, [V]us]

def cRow₁₂ (V : CKMMatrix) : Fin 2 → ℂ := ![[V]cd, [V]cs]
scoped[CKMMatrix] notation (name := c₁₂_row) "[" V "]c₁₂" => cRow₁₂ V

lemma cRow₁₂_normalized_of_cb_zero {V : CKMMatrix} (hcb : [V]cb = 0) :
    conj [V]c₁₂ ⬝ᵥ [V]c₁₂ = 1 := by
  simp
  have hV := V.prop
  rw [mem_unitaryGroup_iff] at hV
  have ht := congrFun (congrFun hV 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at ht
  rw [hcb] at ht
  rw [mul_comm (V.1 1 0) _, mul_comm (V.1 1 1) _] at ht
  simp at ht
  exact ht

lemma ext_Rows {U V : CKMMatrix} (hu : [U]u = [V]u) (hc : [U]c = [V]c) (ht : [U]t = [V]t) :
    U = V := by
  apply CKMMatrix_ext
  funext i j
  fin_cases i
  have h1 := congrFun hu j
  fin_cases j <;> simpa using h1
  have h1 := congrFun hc j
  fin_cases j <;> simpa using h1
  have h1 := congrFun ht j
  fin_cases j <;> simpa using h1

end CKMMatrix

namespace phaseShiftApply
open CKMMatrix

variable (V : CKMMatrix) (a b c d e f : ℝ)


def ucCross  : Fin 3 → ℂ :=
  conj [phaseShiftApply V a b c d e f]u ×₃ conj [phaseShiftApply V a b c d e f]c

lemma ucCross_fst (V : CKMMatrix) : (ucCross V a b c d e f) 0 =
    cexp ((- a * I) +  (- b * I) + ( - e * I) +  (- f * I)) * (conj [V]u ×₃ conj [V]c) 0 := by
  simp [ucCross, crossProduct]
  simp [uRow, us, ub, cRow, cs, cb]
  rw [exp_add, exp_add]
  simp [exp_add, exp_sub, ← exp_conj, conj_ofReal]
  ring

lemma ucCross_snd (V : CKMMatrix) : (ucCross V a b c d e f) 1 =
    cexp ((- a * I) +  (- b * I) + ( - d * I) +  (- f * I)) * (conj [V]u ×₃ conj [V]c) 1 := by
  simp [ucCross, crossProduct]
  simp [uRow, us, ub, cRow, cs, cb, ud, cd]
  rw [exp_add, exp_add]
  simp [exp_add, exp_sub, ← exp_conj, conj_ofReal]
  ring

lemma ucCross_thd (V : CKMMatrix) : (ucCross V a b c d e f) 2 =
    cexp ((- a * I) +  (- b * I) + ( - d * I) +  (- e * I)) * (conj [V]u ×₃ conj [V]c) 2 := by
  simp [ucCross, crossProduct]
  simp [uRow, us, ub, cRow, cs, cb, ud, cd]
  rw [exp_add, exp_add]
  simp [exp_add, exp_sub, ← exp_conj, conj_ofReal]
  ring

lemma uRow_mul (V : CKMMatrix) (a b c : ℝ) :
    [phaseShiftApply V a b c 0 0 0]u = cexp (a * I) • [V]u  := by
  funext i
  simp
  fin_cases i <;>
    change (phaseShiftApply V a b c 0 0 0).1 0 _ = _
  rw [ud, uRow]
  simp
  rw [us, uRow]
  simp
  rw [ub, uRow]
  simp

lemma cRow_mul (V : CKMMatrix) (a b c : ℝ) :
    [phaseShiftApply V a b c 0 0 0]c = cexp (b * I) • [V]c  := by
  funext i
  simp
  fin_cases i <;>
    change (phaseShiftApply V a b c 0 0 0).1 1 _ = _
  rw [cd, cRow]
  simp
  rw [cs, cRow]
  simp
  rw [cb, cRow]
  simp

lemma tRow_mul (V : CKMMatrix) (a b c : ℝ) :
    [phaseShiftApply V a b c 0 0 0]t = cexp (c * I) • [V]t  := by
  funext i
  simp
  fin_cases i <;>
    change (phaseShiftApply V a b c 0 0 0).1 2 _ = _
  rw [td, tRow]
  simp
  rw [ts, tRow]
  simp
  rw [tb, tRow]
  simp



end  phaseShiftApply

end
