/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import Mathlib.Analysis.Convolution
import Mathlib.Algebra.Star.Basic
/-!

# Hilbert space for one dimension quantum mechanics

-/

namespace QuantumMechanics

namespace OneDimension
noncomputable section

/-- The Hilbert space for a one dimensional quantum system is defined as
  the space of almost-everywhere equal equivalence classes of square integrable functions
  from `ℝ` to `ℂ`. -/
noncomputable abbrev HilbertSpace := MeasureTheory.Lp (α := ℝ) ℂ 2

namespace HilbertSpace
open MeasureTheory

/-- The proposition `MemHS f` for a function `f : ℝ → ℂ` is defined
  to be true if the function `f` can be lifted to the Hilbert space. -/
def MemHS (f : ℝ → ℂ) : Prop := Memℒp f 2 MeasureTheory.volume

lemma aeStronglyMeasurable_of_memHS {f : ℝ → ℂ} (h : MemHS f) :
    AEStronglyMeasurable f := by
  exact h.1

/-- A function `f` statisfies `MemHS f` if and only if it is almost everywhere
  strongly measurable, and square integrable. -/
lemma memHS_iff {f : ℝ → ℂ} : MemHS f ↔
    AEStronglyMeasurable f ∧ Integrable (fun x => ‖f x‖ ^ 2) := by
  rw [MemHS]
  simp only [Memℒp, Complex.norm_eq_abs, and_congr_right_iff]
  intro h1
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top
    (Ne.symm (NeZero.ne' 2)) ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable
    (fun x => Complex.abs (f x) ^ 2) MeasureTheory.volume := by
    apply MeasureTheory.AEStronglyMeasurable.pow
    exact Continuous.comp_aestronglyMeasurable Complex.continuous_abs h1
  simp only [h0, true_and]
  simp only [HasFiniteIntegral, enorm_pow]
  simp only [enorm, nnnorm, Complex.norm_eq_abs, Real.norm_eq_abs, Complex.abs_abs]

lemma aeEqFun_mk_mem_iff (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
    AEEqFun.mk f hf ∈ HilbertSpace ↔ MemHS f := by
  rw [MemHS, HilbertSpace]
  rw [MeasureTheory.Lp.mem_Lp_iff_memℒp]
  apply MeasureTheory.memℒp_congr_ae
  exact AEEqFun.coeFn_mk f hf

/-- Given a function `f : ℝ → ℂ` such that `MemHS f` is true via `hf`, then `HilbertSpace.mk hf`
  is the element of the `HilbertSpace` defined by `f`. -/
def mk {f : ℝ → ℂ} (hf : MemHS f) : HilbertSpace :=
  ⟨AEEqFun.mk f hf.1, (aeEqFun_mk_mem_iff f hf.1).mpr hf⟩

lemma coe_hilbertSpace_memHS (f : HilbertSpace) : MemHS (f : ℝ → ℂ) := by
  rw [← aeEqFun_mk_mem_iff f.1 (Lp.aestronglyMeasurable f)]
  have hf : f = AEEqFun.mk f.1 (Lp.aestronglyMeasurable f) := by
    exact Eq.symm (AEEqFun.mk_coeFn _)
  rw [← hf]
  exact f.2

lemma mk_surjective (f : HilbertSpace) : ∃ (g : ℝ → ℂ), ∃ (hg : MemHS g), mk hg = f := by
  use f
  use coe_hilbertSpace_memHS f
  simp [mk]

lemma coe_mk_ae {f : ℝ → ℂ} (hf : MemHS f) : (mk hf : ℝ → ℂ) =ᵐ[MeasureTheory.volume] f := by
  exact AEEqFun.coeFn_mk f hf.1

lemma inner_mk_mk {f g : ℝ → ℂ} {hf : MemHS f} {hg : MemHS g} :
    inner (mk hf) (mk hg) = ∫ x : ℝ, starRingEnd ℂ (f x) * g x := by
  apply MeasureTheory.integral_congr_ae
  have hn_ae := coe_mk_ae hf
  have hm_ae := coe_mk_ae hg
  filter_upwards [hn_ae, hm_ae] with _ hf hg
  rw [hf, hg]
  simp [inner]

@[simp]
lemma eLpNorm_mk {f : ℝ → ℂ} {hf : MemHS f} :
    eLpNorm (mk hf) 2 volume = eLpNorm f 2 volume := by
  apply MeasureTheory.eLpNorm_congr_ae
  exact coe_mk_ae hf

lemma mem_iff' {f : ℝ → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.AEEqFun.mk f hf ∈ HilbertSpace
    ↔ MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := by
  rw [HilbertSpace]
  rw [MeasureTheory.Lp.mem_Lp_iff_memℒp]
  simp only [Memℒp, eLpNorm_aeeqFun, Complex.norm_eq_abs]
  have h1 : MeasureTheory.AEStronglyMeasurable
    (MeasureTheory.AEEqFun.mk f hf) MeasureTheory.volume := by
    apply MeasureTheory.AEEqFun.aestronglyMeasurable
  simp only [h1, true_and]
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top (Ne.symm (NeZero.ne' 2))
    ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable
    (fun x => Complex.abs (f x) ^ 2) MeasureTheory.volume := by
    apply MeasureTheory.AEStronglyMeasurable.pow
    refine Continuous.comp_aestronglyMeasurable ?_ hf
    exact Complex.continuous_abs
  simp only [h0, true_and]
  simp only [HasFiniteIntegral, enorm_pow]
  simp only [enorm, nnnorm, Complex.norm_eq_abs, Real.norm_eq_abs, Complex.abs_abs]

/-!

## Gaussians

-/
open MeasureTheory

lemma gaussian_integrable {b : ℝ} (c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => (Real.exp (- b * (x - c)^ 2) : ℂ)) := by
  apply MeasureTheory.Integrable.ofReal
  have hf : (fun x => (Real.exp (-b * (x - c) ^ 2))) =
    fun y => (fun x => (Real.exp (-b * x ^ 2))) (y - c) := by
    exact rfl
  erw [hf]
  apply Integrable.comp_sub_right (f := (fun x => Real.exp (- b * x ^ 2)))
  exact integrable_exp_neg_mul_sq hb

lemma gaussian_aestronglyMeasurable {b : ℝ} (c : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (fun x => (Real.exp (- b * (x - c) ^2) : ℂ)) volume := by
  apply MeasureTheory.Integrable.aestronglyMeasurable
  exact gaussian_integrable c hb

lemma gaussian_memHS {b : ℝ} (c : ℝ) (hb : 0 < b) :
    MemHS (fun x => (Real.exp (- b * (x - c) ^2) : ℂ)) := by
  rw [memHS_iff]
  apply And.intro
  · exact gaussian_aestronglyMeasurable c hb
  simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.norm_eq_abs, Complex.abs_exp, Complex.neg_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h1 : (fun (x : ℝ) => Real.exp (-(b * ((x - c : ℂ) ^ 2).re)) ^ 2) =
    fun y => (fun x => Real.exp (- (2 * b) * x ^ 2)) (y - c) := by
    ext x
    simp only [neg_mul]
    trans Real.exp (-(b * ((x - c: ℂ) ^ 2).re)) ^ (2 : ℝ)
    · simp
    rw [← Real.exp_mul]
    simp only [neg_mul, Real.exp_eq_exp, neg_inj]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  rw [h1]
  apply Integrable.comp_sub_right (f := fun x => Real.exp (- (2 * b) * x ^ 2))
  apply integrable_exp_neg_mul_sq
  linarith

lemma exp_mul_gaussian_integrable (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Real.exp (c * x) * Real.exp (- b * x ^ 2)) := by
  have h1 : (fun x => Real.exp (c * x) * Real.exp (- b * x ^ 2))
      = (fun x => Real.exp (c^2 /(4 * b)) * Real.exp (- b * (x - c/(2 * b)) ^ 2)) := by
    funext x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h1]
  apply MeasureTheory.Integrable.const_mul
  have h1 :(fun x => Real.exp (- b * (x - c/(2 * b)) ^ 2))
      = fun y => (fun x => Real.exp (- b * x ^ 2)) (y - c/(2 * b)) := by
    funext x
    rw [sub_sq]
    ring_nf
  rw [h1]
  apply Integrable.comp_sub_right (f := (fun x => Real.exp (- b * x ^ 2)))
  exact integrable_exp_neg_mul_sq hb

lemma exp_abs_mul_gaussian_integrable (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Real.exp (|c * x|) * Real.exp (- b * x ^ 2)) := by
  rw [← MeasureTheory.integrableOn_univ]
  have h1 : Set.univ (α := ℝ) = (Set.Iic 0) ∪ Set.Ici 0 := by
    exact Eq.symm Set.Iic_union_Ici
  rw [h1]
  apply MeasureTheory.IntegrableOn.union
  · let g := fun x => Real.exp ((- |c|) * x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Iic]
    · apply MeasureTheory.IntegrableOn.left_of_union (t := Set.Ici 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_gaussian_integrable b (- |c|) hb
    · intro x hx
      simp only [Set.mem_Iic] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, Real.exp_ne_zero, or_false, g]
      rw [abs_mul]
      rw [abs_of_nonpos hx]
      ring
  · let g := fun x => Real.exp (|c| * x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Ici]
    · apply MeasureTheory.IntegrableOn.right_of_union (s := Set.Iic 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_gaussian_integrable b (|c|) hb
    · intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, Real.exp_ne_zero, or_false, g]
      rw [abs_mul]
      rw [abs_of_nonneg hx]

lemma mul_gaussian_mem_Lp_one (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Memℒp (fun x => f x * Real.exp (- b * (x - c) ^ 2)) 1 volume := by
  refine memℒp_one_iff_integrable.mpr ?_
  let g : HilbertSpace := mk (gaussian_memHS c hb)
  have h1 := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) g (mk hf)
  refine (integrable_congr ?_).mp h1
  simp only [RCLike.inner_apply, neg_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub]
  conv_lhs =>
    enter [x]
    rw [mul_comm]
  apply Filter.EventuallyEq.mul
  · exact coe_mk_ae hf
  trans (fun x => (starRingEnd ℂ) (Real.exp (- b * (x - c) ^2)))
  · apply Filter.EventuallyEq.fun_comp
    simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sub, g]
    exact AEEqFun.coeFn_mk _ _
  · apply Filter.EventuallyEq.of_eq
    funext x
    rw [Complex.conj_ofReal]
    simp

lemma mul_gaussian_mem_Lp_two (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Memℒp (fun x => f x * Real.exp (- b * (x - c) ^ 2)) 2 volume := by
  apply MeasureTheory.Memℒp.mul_of_top_left (p := 2)
  · apply MeasureTheory.memℒp_top_of_bound (C := Real.exp (0))
    · exact gaussian_aestronglyMeasurable c hb
    · apply Filter.Eventually.of_forall
      intro x
      simp only [neg_mul, Complex.norm_eq_abs, zero_sub, even_two, Even.neg_pow]
      rw [Complex.abs_ofReal]
      rw [abs_of_nonneg]
      · simp only [Real.exp_zero, Real.exp_le_one_iff, Left.neg_nonpos_iff]
        apply mul_nonneg
        · exact le_of_lt hb
        · exact sq_nonneg (x - c)
      · exact Real.exp_nonneg (-(b * (x - c) ^ 2))
  · exact hf

lemma abs_mul_gaussian_integrable (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Complex.abs (f x) * Real.exp (- b * (x - c)^2)) := by
  have h1 : (fun x => Complex.abs (f x) * Real.exp (- b * (x - c)^2)) =
      (fun x => Complex.abs (f x * Real.exp (- b *(x - c)^2))) := by
    funext x
    simp only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sub, AbsoluteValue.map_mul, Complex.abs_exp,
      Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      mul_eq_mul_left_iff, Real.exp_eq_exp, neg_inj, map_eq_zero]
    left
    left
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow]
    rw [Complex.ofReal_re]
  rw [h1]
  have h2 : MeasureTheory.Memℒp (fun x => f x * Real.exp (- b * (x- c)^2)) 1 volume := by
    exact mul_gaussian_mem_Lp_one f hf b c hb
  simpa using MeasureTheory.Memℒp.integrable_norm_rpow h2 (by simp) (by simp)

lemma exp_mul_abs_mul_gaussian_integrable (f : ℝ → ℂ) (hf : MemHS f)
    (b c : ℝ) (hb : 0 < b) : MeasureTheory.Integrable
    (fun x => Real.exp (c * x) * Complex.abs (f x) * Real.exp (- b * x ^ 2)) := by
  have h1 : (fun x => Real.exp (c * x) *
  Complex.abs (f x) * Real.exp (- b * x ^ 2))
      = (fun x => Real.exp (c^2 /(4 * b)) *
      (Complex.abs (f x) * Real.exp (- b * (x - c/(2 * b)) ^ 2))) := by
    funext x
    rw [mul_comm,← mul_assoc]
    trans (Real.exp (c ^ 2 / (4 * b)) * Real.exp (-b * (x - c / (2 * b)) ^ 2)) * Complex.abs (f x)
    swap
    · ring
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h1]
  apply MeasureTheory.Integrable.const_mul
  exact abs_mul_gaussian_integrable f hf b (c / (2 * b)) hb

lemma exp_abs_mul_abs_mul_gaussian_integrable (f : ℝ → ℂ) (hf : MemHS f) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable
    (fun x => Real.exp (|c * x|) * Complex.abs (f x) * Real.exp (- b * x ^ 2)) := by
  rw [← MeasureTheory.integrableOn_univ]
  have h1 : Set.univ (α := ℝ) = (Set.Iic 0) ∪ Set.Ici 0 := by
    exact Eq.symm Set.Iic_union_Ici
  rw [h1]
  apply MeasureTheory.IntegrableOn.union
  · let g := fun x => Real.exp ((- |c|) * x) * Complex.abs (f x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Iic]
    · apply MeasureTheory.IntegrableOn.left_of_union (t := Set.Ici 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_abs_mul_gaussian_integrable f hf b (-|c|) hb
    · intro x hx
      simp only [Set.mem_Iic] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, map_eq_zero, Real.exp_ne_zero,
        or_false, g]
      left
      rw [abs_mul]
      rw [abs_of_nonpos hx]
      ring
  · let g := fun x => Real.exp (|c| * x) * Complex.abs (f x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Ici]
    · apply MeasureTheory.IntegrableOn.right_of_union (s := Set.Iic 0)
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_abs_mul_gaussian_integrable f hf b |c| hb
    · intro x hx
      simp only [Set.mem_Ici] at hx
      simp only [neg_mul, mul_eq_mul_right_iff, Real.exp_eq_exp, map_eq_zero, Real.exp_ne_zero,
        or_false, g]
      left
      rw [abs_mul]
      rw [abs_of_nonneg hx]

end HilbertSpace
