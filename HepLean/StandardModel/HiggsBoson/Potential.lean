/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.QuadraticDiscriminant
import HepLean.StandardModel.HiggsBoson.PointwiseInnerProd
/-!
# The potential of the Higgs field

We define the potential of the Higgs field.

We show that the potential is a smooth function on spacetime.

-/

noncomputable section

namespace StandardModel

namespace HiggsField

open Manifold
open Matrix
open Complex
open ComplexConjugate
open SpaceTime

/-!

## The Higgs potential

-/

/-- The Higgs potential of the form `- μ² * |φ|² + 𝓵 * |φ|⁴`. -/
@[simp]
def potential (μ2 𝓵 : ℝ) (φ : HiggsField) (x : SpaceTime) : ℝ :=
  - μ2 * ‖φ‖_H ^ 2 x + 𝓵 * ‖φ‖_H ^ 2 x * ‖φ‖_H ^ 2 x

/-!

## Smoothness of the potential

-/

lemma potential_smooth (μSq lambda : ℝ) (φ : HiggsField) :
    Smooth 𝓘(ℝ, SpaceTime) 𝓘(ℝ, ℝ) (fun x => φ.potential μSq lambda x) := by
  simp only [potential, normSq, neg_mul]
  exact (smooth_const.smul φ.normSq_smooth).neg.add
    ((smooth_const.smul φ.normSq_smooth).smul φ.normSq_smooth)

namespace potential
/-!

## Basic properties

-/

lemma complete_square (μ2 𝓵 : ℝ) (h : 𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    potential μ2 𝓵 φ x = 𝓵 * (‖φ‖_H ^ 2 x - μ2 / (2 * 𝓵)) ^ 2 - μ2 ^ 2 / (4 * 𝓵) := by
  simp only [potential]
  field_simp
  ring

lemma as_quad (μ2 𝓵 : ℝ) (φ : HiggsField) (x : SpaceTime) :
    𝓵 * ‖φ‖_H ^ 2 x * ‖φ‖_H ^ 2 x + (- μ2) * ‖φ‖_H ^ 2 x + (- potential μ2 𝓵 φ x) = 0 := by
  simp only [normSq, neg_mul, potential, neg_add_rev, neg_neg]
  ring

/-- The discriminant of the quadratic formed by the potential is non-negative. -/
lemma discrim_nonneg (μ2 : ℝ) {𝓵 : ℝ} (h : 𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    0 ≤ discrim 𝓵 (- μ2) (- potential μ2 𝓵 φ x) := by
  have h1 := as_quad μ2 𝓵 φ x
  rw [quadratic_eq_zero_iff_discrim_eq_sq] at h1
  · simp only [h1, ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
    exact sq_nonneg (2 * 𝓵 * ‖φ‖_H ^ 2 x + - μ2)
  · exact h

lemma discrim_eq_sqrt_discrim_mul_self (μ2 : ℝ) {𝓵 : ℝ} (h : 𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime) :
    discrim 𝓵 (- μ2) (- potential μ2 𝓵 φ x) = Real.sqrt (discrim 𝓵 (- μ2) (- potential μ2 𝓵 φ x)) *
      Real.sqrt (discrim 𝓵 (- μ2) (- potential μ2 𝓵 φ x)) := by
  refine Eq.symm (Real.mul_self_sqrt ?h)
  exact discrim_nonneg μ2 h φ x

lemma eq_zero_at (μ2 : ℝ) {𝓵 : ℝ} (h : 𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime)
    (hV : potential μ2 𝓵 φ x = 0) : φ x = 0 ∨ ‖φ‖_H ^ 2 x = μ2 / 𝓵 := by
  have h1 := as_quad μ2 𝓵 φ x
  rw [hV] at h1
  have h2 : ‖φ‖_H ^ 2 x * (𝓵 * ‖φ‖_H ^ 2 x + - μ2) = 0 := by
    linear_combination h1
  simp at h2
  cases' h2 with h2 h2
  · simp_all
  · apply Or.inr
    field_simp at h2 ⊢
    ring_nf
    linear_combination h2

/-- When `0 < 𝓵`, the potential has a lower bound. -/
lemma bounded_below (μ2 : ℝ) {𝓵 : ℝ} (h𝓵 : 0 < 𝓵) (φ : HiggsField) (x : SpaceTime) :
    - μ2 ^ 2 / (4 * 𝓵) ≤ potential μ2 𝓵 φ x := by
  have h1 := discrim_nonneg μ2 (ne_of_lt h𝓵).symm φ x
  simp only [discrim, even_two, Even.neg_pow, normSq, neg_mul, neg_add_rev, neg_neg] at h1
  ring_nf at h1
  rw [← neg_le_iff_add_nonneg'] at h1
  rw [show 𝓵 * potential μ2 𝓵 φ x * 4 = (4 * 𝓵) * potential μ2 𝓵 φ x by ring] at h1
  have h2 := (div_le_iff₀' (by simp [h𝓵] : 0 < 4 * 𝓵)).mpr h1
  ring_nf at h2 ⊢
  exact h2

/-- When `𝓵 < 0`, the potential has an upper bound. -/
lemma bounded_above (μ2 : ℝ) {𝓵 : ℝ} (h𝓵 : 𝓵 < 0) (φ : HiggsField) (x : SpaceTime) :
    potential μ2 𝓵 φ x ≤ - μ2 ^ 2 / (4 * 𝓵) := by
  have h1 := discrim_nonneg μ2 (ne_of_lt h𝓵) φ x
  simp only [discrim, even_two, Even.neg_pow, normSq, neg_mul, neg_add_rev, neg_neg] at h1
  ring_nf at h1
  rw [← neg_le_iff_add_nonneg'] at h1
  rw [show 𝓵 * potential μ2 𝓵 φ x * 4 = (- 4 * 𝓵) * (- potential μ2 𝓵 φ x) by ring] at h1
  have h2 := le_neg_of_le_neg <| (div_le_iff₀' (by linarith : 0 < - 4 * 𝓵)).mpr h1
  ring_nf at h2 ⊢
  exact h2

lemma discrim_eq_zero_of_eq_bound (μ2 : ℝ) {𝓵 : ℝ} (h : 𝓵 ≠ 0) (φ : HiggsField) (x : SpaceTime)
    (hV : potential μ2 𝓵 φ x = - μ2 ^ 2 / (4 * 𝓵)) :
    discrim 𝓵 (- μ2) (- potential μ2 𝓵 φ x) = 0 := by
  rw [discrim, hV]
  field_simp

lemma discrim_ge_zero_of_neg_𝓵 (μ2 : ℝ) {𝓵 : ℝ} (h : 𝓵 < 0) (c : ℝ) :
    0 ≤ discrim 𝓵 (- μ2) (- c) ↔ c ≤ - μ2 ^ 2 / (4 * 𝓵) := by
  rw [discrim]
  simp only [even_two, Even.neg_pow, mul_neg, sub_neg_eq_add]
  rw [← neg_le_iff_add_nonneg', show 4 * 𝓵 * c = (- 4 * 𝓵) * (- c) by ring,
    ← (div_le_iff₀' (by linarith : 0 < - 4 * 𝓵)), le_neg]
  ring_nf

example (a b c : ℝ ) (hc : c < 0) :  a ≤ b / c ↔ b ≤ c * a := by
  exact le_div_iff_of_neg' hc
lemma pot_le_zero_of_neg_𝓵 (μ2 : ℝ) {𝓵 : ℝ} (h : 𝓵 < 0) (φ : HiggsField) (x : SpaceTime) :
    (0 < μ2 ∧ potential μ2 𝓵 φ x ≤ 0) ∨ μ2 ≤ 0 := by
  by_cases hμ2 : μ2 ≤ 0
  · simp [hμ2]
  simp [potential, hμ2]
  apply And.intro (lt_of_not_ge hμ2)
  have h1 : 0 ≤  μ2 * ‖φ x‖ ^ 2 := by
    refine Left.mul_nonneg ?ha ?hb
    · exact le_of_not_ge hμ2
    · exact sq_nonneg ‖φ x‖
  refine le_trans ?_ h1
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (le_of_lt h)
    (sq_nonneg ‖φ x‖)) (sq_nonneg ‖φ x‖)

lemma exist_sol_iff_of_neg_𝓵 (μ2 : ℝ) {𝓵 : ℝ} (h𝓵 : 𝓵 < 0) (c : ℝ) :
    (∃ φ x, potential μ2 𝓵 φ x = c) ↔ (0 < μ2 ∧ c ≤ 0) ∨
    (μ2 ≤ 0 ∧ c ≤ - μ2 ^ 2 / (4 * 𝓵)) := by
  refine Iff.intro (fun ⟨φ, x, hV⟩ => ?_) (fun h => ?_)
  · rcases pot_le_zero_of_neg_𝓵 μ2 h𝓵 φ x with hr | hr
    · rw [← hV]
      exact Or.inl hr
    · rw [← hV]
      exact Or.inr (And.intro hr (bounded_above μ2 h𝓵 φ x))
  · simp only [potential, neg_mul]
    simp only [← sub_eq_zero, sub_zero]
    ring_nf
    let a := (μ2 - Real.sqrt (discrim 𝓵 (- μ2) (- c))) / (2 * 𝓵)
    have ha : 0 ≤ a := by
      simp [a, discrim]
      rw [div_nonneg_iff]
      refine Or.inr (And.intro ?_ ?_)
      · rw [sub_nonpos]
        by_cases hμ : μ2 < 0
        · have h1 : 0 ≤ √(μ2 ^ 2 + 4 * 𝓵 * c) := Real.sqrt_nonneg (μ2 ^ 2 + 4 * 𝓵 * c)
          linarith
        · refine Real.le_sqrt_of_sq_le ?_
          rw [le_add_iff_nonneg_right]
          refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
          · refine mul_nonpos_of_nonneg_of_nonpos ?_ ?_
            · linarith
            · linarith
          · rcases h with h | h
            · linarith
            · have h1 : μ2 = 0 := by linarith
              rw [h1] at h
              simpa using h.2
      · linarith
    use (ofReal a)
    use 0
    rw [ofReal_normSq ha]
    trans 𝓵 * a * a + (- μ2) * a + (- c)
    · ring
    have hd : 0 ≤ (discrim 𝓵 (-μ2) (-c)) := by
      simp [discrim]
      rcases h with h | h
      · refine Left.add_nonneg (sq_nonneg μ2) ?_
        refine mul_nonneg_of_nonpos_of_nonpos ?_ h.2
        linarith
      · rw [← @neg_le_iff_add_nonneg']
        rw [← le_div_iff_of_neg']
        · exact h.2
        · linarith
    have hdd : discrim 𝓵 (-μ2) (-c) = Real.sqrt (discrim 𝓵 (-μ2) (-c)) * Real.sqrt (discrim 𝓵 (-μ2) (-c)) := by
      exact (Real.mul_self_sqrt hd).symm
    refine (quadratic_eq_zero_iff (ne_of_gt h𝓵).symm hdd _).mpr ?_
    simp only [neg_neg, or_true, a]

/-!

## Boundness of the potential

-/

/-- The proposition on the coefficents for a potential to be bounded. -/
def IsBounded (μ2 𝓵 : ℝ) : Prop :=
  ∃ c, ∀ Φ x, c ≤ potential μ2 𝓵 Φ x

lemma isBounded_𝓵_nonneg {μ2 𝓵 : ℝ} (h : IsBounded μ2 𝓵) :
    0 ≤ 𝓵 := by
  by_contra hl
  simp at hl
  obtain ⟨c, hc⟩ := h
  by_cases hμ : μ2 ≤ 0
  · by_cases hcz : c ≤ -μ2 ^ 2 / (4 * 𝓵)
    · have hcm1 : ∃ φ x, potential μ2 𝓵 φ x = c - 1 := by
        rw [propext (exist_sol_iff_of_neg_𝓵 μ2 hl (c - 1))]
        apply Or.inr
        simp_all
        linarith
      obtain ⟨φ, x, hφ⟩ := hcm1
      have hc2 := hc φ x
      rw [hφ] at hc2
      linarith
    · simp at hcz
      have hcm1 : ∃ φ x, potential μ2 𝓵 φ x = -μ2 ^ 2 / (4 * 𝓵) - 1 := by
        rw [propext (exist_sol_iff_of_neg_𝓵 μ2 hl _)]
        apply Or.inr
        simp_all
      obtain ⟨φ, x, hφ⟩ := hcm1
      have hc2 := hc φ x
      rw [hφ] at hc2
      linarith
  · simp at hμ
    by_cases hcz : c ≤ 0
    · have hcm1 : ∃ φ x, potential μ2 𝓵 φ x = c - 1 := by
        rw [propext (exist_sol_iff_of_neg_𝓵 μ2 hl (c - 1))]
        apply Or.inl
        simp_all
        linarith
      obtain ⟨φ, x, hφ⟩ := hcm1
      have hc2 := hc φ x
      rw [hφ] at hc2
      linarith
    · have hcm1 : ∃ φ x, potential μ2 𝓵 φ x = 0 := by
        rw [propext (exist_sol_iff_of_neg_𝓵 μ2 hl 0)]
        apply Or.inl
        simp_all
      obtain ⟨φ, x, hφ⟩ := hcm1
      have hc2 := hc φ x
      rw [hφ] at hc2
      linarith



section lowerBound
/-!

## Lower bound on potential

-/

variable (μ2 : ℝ) {𝓵 : ℝ} (h𝓵 : 0 < 𝓵)

include h𝓵
/-- The second term of the potential is non-negative. -/
lemma snd_term_nonneg (φ : HiggsField) (x : SpaceTime) :
    0 ≤ 𝓵 * ‖φ‖_H ^ 2 x * ‖φ‖_H ^ 2 x := by
  rw [mul_nonneg_iff]
  apply Or.inl
  simp_all only [normSq, gt_iff_lt, mul_nonneg_iff_of_pos_left, ge_iff_le, norm_nonneg, pow_nonneg,
    and_self]

lemma eq_zero_at_of_μSq_nonpos {μ2 : ℝ} (hμ2 : μ2 ≤ 0)
    (φ : HiggsField) (x : SpaceTime) (hV : potential μ2 𝓵 φ x = 0) : φ x = 0 := by
  cases' (eq_zero_at μ2 (ne_of_lt h𝓵).symm φ x hV) with h1 h1
  · exact h1
  · by_cases hμSqZ : μ2 = 0
    · simpa [hμSqZ] using h1
    · refine ((?_ : ¬ 0 ≤ μ2 / 𝓵) (?_)).elim
      · simp_all [div_nonneg_iff]
        intro h
        exact lt_imp_lt_of_le_imp_le (fun _ => h) (lt_of_le_of_ne hμ2 hμSqZ)
      · rw [← h1]
        exact normSq_nonneg φ x

lemma bounded_below_of_μSq_nonpos {μ2 : ℝ}
    (hμSq : μ2 ≤ 0) (φ : HiggsField) (x : SpaceTime) : 0 ≤ potential μ2 𝓵 φ x := by
  refine add_nonneg ?_ (snd_term_nonneg h𝓵 φ x)
  field_simp [mul_nonpos_iff]
  simp_all [ge_iff_le, norm_nonneg, pow_nonneg, and_self, or_true]

end lowerBound

section MinimumOfPotential
variable {𝓵 : ℝ}
variable (μ2 : ℝ)
variable (h𝓵 : 0 < 𝓵)

/-!

## Minima of potential

-/


include h𝓵
lemma normSq_of_eq_bound (φ : HiggsField) (x : SpaceTime)
    (hV : potential μ2 𝓵 φ x = - μ2 ^ 2 / (4 * 𝓵)) :
    ‖φ‖_H ^ 2 x = μ2 / (2 * 𝓵) := by
  have h1 := as_quad μ2 𝓵 φ x
  rw [quadratic_eq_zero_iff_of_discrim_eq_zero _
    (discrim_eq_zero_of_eq_bound μ2 (ne_of_lt h𝓵).symm φ x hV)] at h1
  · simp_rw [h1, neg_neg]
  · exact ne_of_gt h𝓵

lemma eq_bound_iff (φ : HiggsField) (x : SpaceTime) :
    potential μ2 𝓵 φ x = - μ2 ^ 2 / (4 * 𝓵) ↔ ‖φ‖_H ^ 2 x = μ2 / (2 * 𝓵) :=
  Iff.intro (normSq_of_eq_bound μ2 h𝓵 φ x)
    (fun h ↦ by
      rw [potential, h]
      field_simp
      ring_nf)

lemma eq_bound_iff_of_μSq_nonpos {μ2 : ℝ}
    (hμ2 : μ2 ≤ 0) (φ : HiggsField) (x : SpaceTime) :
    potential μ2 𝓵 φ x = 0 ↔ φ x = 0 :=
  Iff.intro (fun h ↦ eq_zero_at_of_μSq_nonpos h𝓵 hμ2 φ x h)
  (fun h ↦ by simp [potential, h])

lemma eq_bound_IsMinOn (φ : HiggsField) (x : SpaceTime)
    (hv : potential μ2 𝓵 φ x = - μ2 ^ 2 / (4 * 𝓵)) :
    IsMinOn (fun (φ, x) => potential μ2 𝓵 φ x) Set.univ (φ, x) := by
  rw [isMinOn_univ_iff]
  simp only [normSq, neg_mul, le_neg_add_iff_add_le, ge_iff_le, hv]
  exact fun (φ', x') ↦ bounded_below μ2 h𝓵 φ' x'

lemma eq_bound_IsMinOn_of_μSq_nonpos {μ2 : ℝ}
    (hμ2 : μ2 ≤ 0) (φ : HiggsField) (x : SpaceTime) (hv : potential μ2 𝓵 φ x = 0) :
    IsMinOn (fun (φ, x) => potential μ2 𝓵 φ x) Set.univ (φ, x) := by
  rw [isMinOn_univ_iff]
  simp only [normSq, neg_mul, le_neg_add_iff_add_le, ge_iff_le, hv]
  exact fun (φ', x') ↦ bounded_below_of_μSq_nonpos h𝓵 hμ2 φ' x'

lemma bound_reached_of_μSq_nonneg {μ2 : ℝ} (hμ2 : 0 ≤ μ2) :
    ∃ (φ : HiggsField) (x : SpaceTime),
    potential μ2 𝓵 φ x = - μ2 ^ 2 / (4 * 𝓵) := by
  use HiggsVec.toField ![√(μ2/(2 * 𝓵)), 0], 0
  refine (eq_bound_iff μ2 h𝓵 (HiggsVec.toField ![√(μ2/(2 * 𝓵)), 0]) 0).mpr ?_
  simp only [normSq, HiggsVec.toField, ContMDiffSection.coeFn_mk, PiLp.norm_sq_eq_of_L2,
    Nat.succ_eq_add_one, Nat.reduceAdd, norm_eq_abs, Fin.sum_univ_two, Fin.isValue, cons_val_zero,
    abs_ofReal, _root_.sq_abs, cons_val_one, head_cons, map_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero]
  field_simp [mul_pow]

lemma IsMinOn_iff_of_μSq_nonneg {μ2 : ℝ} (hμ2 : 0 ≤ μ2) :
    IsMinOn (fun (φ, x) => potential μ2 𝓵 φ x) Set.univ (φ, x) ↔
    ‖φ‖_H ^ 2 x = μ2 /(2 * 𝓵) := by
  apply Iff.intro <;> rw [← eq_bound_iff μ2 h𝓵 φ]
  · intro h
    obtain ⟨φm, xm, hφ⟩ := bound_reached_of_μSq_nonneg h𝓵 hμ2
    have hm := isMinOn_univ_iff.mp h (φm, xm)
    simp only at hm
    rw [hφ] at hm
    exact (Real.partialOrder.le_antisymm _ _ (bounded_below μ2 h𝓵 φ x) hm).symm
  · exact eq_bound_IsMinOn μ2 h𝓵 φ x

lemma IsMinOn_iff_of_μSq_nonpos {μ2 : ℝ} (hμ2 : μ2 ≤ 0) :
    IsMinOn (fun (φ, x) => potential μ2 𝓵 φ x) Set.univ (φ, x) ↔ φ x = 0 := by
  apply Iff.intro <;> rw [← eq_bound_iff_of_μSq_nonpos h𝓵 hμ2 φ]
  · intro h
    have h0 := isMinOn_univ_iff.mp h 0
    have h1 := bounded_below_of_μSq_nonpos h𝓵 hμ2 φ x
    simp only at h0
    rw [(eq_bound_iff_of_μSq_nonpos h𝓵 hμ2 0 0).mpr (by rfl)] at h0
    exact (Real.partialOrder.le_antisymm _ _ h1 h0).symm
  · exact eq_bound_IsMinOn_of_μSq_nonpos h𝓵 hμ2 φ x

end MinimumOfPotential

end potential

end HiggsField

end StandardModel
end
