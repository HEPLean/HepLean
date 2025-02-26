/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Eigenfunction
/-!

# Completeness of the eigenfunctions of the Harmonic Oscillator

Completeness of the eigenfunctions follows from Plancherel's theorem.

The steps of this proof are:

1. Prove that if `f` is orthogonal to all eigenvectors then the Fourier transform of
  it muliplied by `exp(-c x^2)` for a `0<c` is zero.
  Part of this is using the concept of `dominated_convergence`.
2. Use 'Plancherel's theorem' to show that `f` is zero.

-/

namespace QuantumMechanics

namespace OneDimension
namespace HarmonicOscillator
variable (Q : HarmonicOscillator)

open Nat
open PhysLean
open MeasureTheory HilbertSpace InnerProductSpace

/-

Integrability conditions related to eigenfunctions.

-/

lemma mul_eigenfunction_integrable (f : ℝ → ℂ) (hf : MemHS f) :
    MeasureTheory.Integrable (fun x => Q.eigenfunction n x * f x) := by
  have h1 := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (HilbertSpace.mk (Q.eigenfunction_memHS n))
    (HilbertSpace.mk hf)
  refine (integrable_congr ?_).mp h1
  simp
  apply Filter.EventuallyEq.mul
  swap
  · exact coe_mk_ae hf
  trans (fun x => (starRingEnd ℂ) (Q.eigenfunction n x))
  · apply Filter.EventuallyEq.fun_comp
    exact coe_mk_ae (eigenfunction_memHS Q n)
  · apply Filter.EventuallyEq.of_eq
    funext x
    simp

lemma mul_physHermiteFun_integrable (f : ℝ → ℂ) (hf : MemHS f) (n : ℕ) :
    MeasureTheory.Integrable (fun x => (physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x)) *
      (f x * ↑(Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ))))) := by
  have h2 : (1 / ↑√(2 ^ n * ↑n !) * ↑√√(Q.m * Q.ω / (Real.pi * Q.ℏ)) : ℂ) • (fun (x : ℝ ) =>
      (physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x) *
      (f x  * Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ))))) = fun x =>
      Q.eigenfunction n x * f x := by
    funext x
    simp [eigenfunction_eq]
    ring
  have h1 := Q.mul_eigenfunction_integrable f hf (n := n)
  rw [← h2] at h1
  rw [IsUnit.integrable_smul_iff] at h1
  exact h1
  simp
  apply And.intro
  · exact factorial_ne_zero n
  · apply Real.sqrt_ne_zero'.mpr
    refine div_pos ?_ ?_
    · exact mul_pos Q.hm Q.hω
    · apply mul_pos Real.pi_pos Q.hℏ

lemma mul_polynomial_integrable (f : ℝ → ℂ) (hf : MemHS f) (P : Polynomial ℤ) :
    MeasureTheory.Integrable (fun x => ((fun x => P.aeval  x) (√(Q.m * Q.ω / Q.ℏ)  * x)) *
      (f x * Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ)))) volume := by
  have h1 := polynomial_mem_physHermiteFun_span P
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h1
  obtain ⟨a, ha⟩ := h1
  have h2 : (fun x => ↑((fun x => P.aeval  x) (√(Q.m * Q.ω / Q.ℏ)  * x)) * (f x * ↑(Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ)))))
    = (fun x => ∑ r ∈ a.support, a r * (physHermiteFun r (√(Q.m * Q.ω / Q.ℏ) * x)) * (f x * Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ)))) := by
    funext x
    rw [← ha]
    rw [← Finset.sum_mul]
    congr
    rw [Finsupp.sum]
    simp
  rw [h2]
  apply MeasureTheory.integrable_finset_sum
  intro i hi
  simp only [mul_assoc]
  have hf' : (fun a_1 =>
    ↑(a i) * (↑(physHermiteFun i (√(Q.m * Q.ω / Q.ℏ) * a_1)) * (f a_1 * ↑(Real.exp (- Q.m * (Q.ω * a_1 ^ 2) / (2 * Q.ℏ))))))
    = fun x => (a i) • ((physHermiteFun i (√(Q.m * Q.ω / Q.ℏ) * x)) *
      (f x * ↑(Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ))))) := by
    funext x
    simp
    ring_nf
    simp_all
  rw [hf']
  apply MeasureTheory.Integrable.smul
  exact Q.mul_physHermiteFun_integrable f hf i

lemma mul_power_integrable (f : ℝ → ℂ) (hf : MemHS f)  (r : ℕ) :
    MeasureTheory.Integrable (fun x => x ^ r *
      (f x * Real.exp (- Q.m * Q.ω * x^2 / (2 * Q.ℏ)))) volume := by
  by_cases hr : r ≠ 0
  · have h1 := Q.mul_polynomial_integrable f hf  (Polynomial.X ^ r)
    simp at h1
    have h2 : (fun x => (↑√(Q.m * Q.ω / Q.ℏ) * ↑x) ^ r * (f x * Complex.exp (-(↑Q.m * ↑Q.ω * ↑x ^ 2) / (2 * ↑Q.ℏ))))
      =   (↑√(Q.m * Q.ω / Q.ℏ)  : ℂ) ^ r •  (fun x => (↑x ^r * (f x * Real.exp (-(↑Q.m * ↑Q.ω * ↑x ^ 2) / (2 * ↑Q.ℏ))))) := by
      funext x
      simp
      ring
    rw [h2] at h1
    rw [IsUnit.integrable_smul_iff] at h1
    simpa using h1
    simp
    have h1 :  √(Q.m * Q.ω / Q.ℏ) ≠ 0 := by
      refine Real.sqrt_ne_zero'.mpr ?_
      refine div_pos ?_ ?_
      · exact mul_pos Q.hm Q.hω
      · exact Q.hℏ
    simp [h1]
  · simp at hr
    subst hr
    simpa using Q.mul_physHermiteFun_integrable f hf  0

/-!

## Orthogonality conditions

-/

lemma orthogonal_eigenfunction_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n) , HilbertSpace.mk hf⟫_ℂ = 0)
    (n : ℕ) : ∫ (x : ℝ), Q.eigenfunction n x * f x = 0 := by
  rw [← hOrth n]
  rw [inner_mk_mk]
  simp

local notation "m" => Q.m
local notation "ℏ" => Q.ℏ
local notation "ω" => Q.ω
local notation "hm" => Q.hm
local notation "hℏ" => Q.hℏ
local notation "hω" => Q.hω

lemma orthogonal_physHermiteFun_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n) , HilbertSpace.mk hf⟫_ℂ = 0)
    (n : ℕ) :
    ∫ (x : ℝ), (physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x)) * (f x * ↑(Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ))))
    = 0 := by
  have h1 := Q.orthogonal_eigenfunction_of_mem_orthogonal f hf hOrth n
  have h2 : (fun (x : ℝ ) =>
          (1 / ↑√(2 ^ n * ↑n !) * ↑√√(Q.m * Q.ω / (Real.pi * Q.ℏ)) : ℂ) *
            (physHermiteFun n (√(Q.m * Q.ω / Q.ℏ) * x) * f x  * Real.exp (- Q.m * Q.ω * x ^ 2 / (2 * Q.ℏ))))
    = fun x => Q.eigenfunction n x * f x := by
    funext x
    simp [eigenfunction_eq]
    ring
  rw [← h2] at h1
  rw [MeasureTheory.integral_mul_left] at h1
  simp at h1
  have h0 : n ! ≠ 0 := by
    exact factorial_ne_zero n
  have h0' : √(Q.m * Q.ω / (Real.pi * Q.ℏ)) ≠ 0 := by
    simp
    refine Real.sqrt_ne_zero'.mpr ?_
    refine div_pos ?_ ?_
    · exact mul_pos hm hω
    · apply mul_pos Real.pi_pos hℏ
  simp [h0, h0'] at h1
  rw [← h1]
  congr
  funext x
  simp
  ring

lemma orthogonal_polynomial_of_mem_orthogonal  (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n) , HilbertSpace.mk hf⟫_ℂ = 0)
    (P : Polynomial ℤ) :
    ∫ x : ℝ, ((fun x => P.aeval  x) (√(m * ω / ℏ)  * x)) *
      (f x * Real.exp (- m * ω * x^2 / (2 * ℏ))) = 0 := by
  have h1 := polynomial_mem_physHermiteFun_span P
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h1
  obtain ⟨a, ha⟩ := h1
  have h2 : (fun x => ↑((fun x => P.aeval  x) (√(m * ω / ℏ)  * x)) * (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))))
    = (fun x => ∑ r ∈ a.support, a r * (physHermiteFun r (√(m * ω / ℏ) * x)) * (f x * Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))) := by
    funext x
    rw [← ha]
    rw [← Finset.sum_mul]
    congr
    rw [Finsupp.sum]
    simp
  rw [h2]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro x hx
    simp [mul_assoc]
    rw [integral_mul_left]
    simp
    right
    rw [← Q.orthogonal_physHermiteFun_of_mem_orthogonal f hf hOrth x]
    congr
    funext x
    simp
    left
    left
    congr 1
    ring
  · /- Integrablility -/
    intro i hi
    have hf' :
      (fun x => ↑(a i) * ↑(physHermiteFun i (√(m * ω / ℏ) * x)) * (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))))
        =  a i  • (fun x => (physHermiteFun i (√(m * ω / ℏ) * x)) * (f x * ↑(Real.exp (-m * ω * x ^ 2 / (2 * ℏ))))) := by
        funext x
        simp
        ring
    rw [hf']
    apply Integrable.smul
    exact Q.mul_physHermiteFun_integrable f hf i

lemma orthogonal_power_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n) , HilbertSpace.mk hf⟫_ℂ = 0)
    (r : ℕ) :
    ∫ x : ℝ, (x ^ r * (f x * Real.exp (- m * ω * x^2 / (2 * ℏ)))) = 0 := by
  by_cases hr : r ≠ 0
  · have h1 := Q.orthogonal_polynomial_of_mem_orthogonal f hf hOrth (Polynomial.X ^ r)
    simp at h1
    have h2 : (fun x => (↑√(m * ω / ℏ) * ↑x) ^ r * (f x * Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))))
      =  (fun x => (↑√(m * ω / ℏ)  : ℂ) ^ r * (↑x ^r * (f x * Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))))) := by
      funext x
      ring
    rw [h2] at h1
    rw [MeasureTheory.integral_mul_left] at h1
    simp at h1
    have h0 : r ≠ 0 := by
      exact hr
    have h0' : √(m * ω / (ℏ)) ≠ 0 := by
      simp
      refine Real.sqrt_ne_zero'.mpr ?_
      refine div_pos ?_ ?_
      · exact mul_pos hm hω
      · exact hℏ
    simp [h0, h0'] at h1
    rw [← h1]
    congr
    funext x
    simp
  · simp at hr
    subst hr
    simp
    rw [← Q.orthogonal_physHermiteFun_of_mem_orthogonal f hf hOrth 0]
    congr
    funext x
    simp

open Finset

lemma orthogonal_exp_of_mem_orthogonal (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n) , HilbertSpace.mk hf⟫_ℂ = 0)
    (c : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * c * x) * (f x * Real.exp (- m * ω * x^2 / (2 * ℏ))) = 0 := by
  /- Rewriting the intergrand as a limit. -/
  have h1 (y : ℝ) : Filter.Tendsto (fun n =>  ∑ r ∈ range n,
        (Complex.I * ↑c * ↑y) ^ r / r ! * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))
      Filter.atTop (nhds (Complex.exp (Complex.I * c * y) * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))) := by
    have h11 : (fun n =>  ∑ r ∈ range n,
        (Complex.I * ↑c * ↑y) ^ r / r !
        * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ)))) =
        fun n => (∑ r ∈ range n,
        (Complex.I * ↑c * ↑y) ^ r / r !)
        * ((f y * Real.exp (- m * ω * y^2 / (2 * ℏ)))) := by
      funext s
      simp [Finset.sum_mul]
    rw [h11]
    have h12 :  (Complex.exp (Complex.I * c * y) * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))
      = ( Complex.exp (Complex.I * c * y)) * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))):= by
      simp
    rw [h12]
    apply Filter.Tendsto.mul_const
    simp [Complex.exp, Complex.exp']
    haveI hi : CauSeq.IsComplete ℂ norm :=
      inferInstanceAs (CauSeq.IsComplete ℂ Complex.abs)
    exact CauSeq.tendsto_limit (Complex.exp' (Complex.I * c * y))
  /- End of rewritting the intergrand as a limit. -/
  /- Rewritting the integral as a limit using dominated_convergence -/
  have h1' : Filter.Tendsto (fun n => ∫ y : ℝ, ∑ r ∈ range n,
      (Complex.I * ↑c * ↑y) ^ r / r ! * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))
      Filter.atTop (nhds (∫ y : ℝ, Complex.exp (Complex.I * c * y) * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ))))) := by
    let bound : ℝ → ℝ := fun x => Real.exp (|c * x|) * Complex.abs (f x) *
      (Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))
    apply MeasureTheory.tendsto_integral_of_dominated_convergence bound
    · intro n
      apply Finset.aestronglyMeasurable_sum
      intro r hr
      have h1 : (fun a => (Complex.I * ↑c * ↑a) ^ r / ↑r ! * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ)))))
        =  fun a => (Complex.I * ↑c) ^ r / ↑r ! * (f a * Complex.ofReal (a ^ r * (Real.exp (-m * ω * a ^ 2 / (2 * ℏ))))) := by
        funext a
        simp
        ring
      rw [h1]
      apply MeasureTheory.AEStronglyMeasurable.const_mul
      apply MeasureTheory.AEStronglyMeasurable.mul
      · exact aeStronglyMeasurable_of_memHS hf
      · apply MeasureTheory.Integrable.aestronglyMeasurable
        apply MeasureTheory.Integrable.ofReal
        change Integrable (fun x =>  (x ^ r) * (Real.exp (-m * ω * x ^ 2 / (2 * ℏ))))
        have h1 : (fun x => (x ^ r)*(Real.exp (-m * ω * x ^ 2 / (2 * ℏ)))) =
            (fun x => (Polynomial.X ^ r : Polynomial ℤ).aeval x  *
            (Real.exp (- (m * ω / (2* ℏ)) * x ^ 2))) := by
          funext x
          simp  [neg_mul, mul_eq_mul_left_iff, Real.exp_eq_exp]
          left
          field_simp
        rw [h1]
        apply guassian_integrable_polynomial
        simp
    · /- Prove the bound is integrable. -/
      have hbound : bound =
        (fun x => Real.exp |c * x| * Complex.abs (f x) * Real.exp (-(m * ω / (2 * ℏ)) * x ^ 2))
         := by
         simp [bound]
         funext x
         congr
         field_simp
      rw [hbound]
      apply HilbertSpace.exp_abs_mul_abs_mul_gaussian_integrable
      · refine (aeEqFun_mk_mem_iff f ?_).mpr hf
        exact aeStronglyMeasurable_of_memHS hf
      · refine div_pos ?_ ?_
        · exact mul_pos hm hω
        · have h1 := Q.hℏ
          linarith
    · intro n
      apply Filter.Eventually.of_forall
      intro y
      rw [← Finset.sum_mul]
      simp [bound]
      rw [mul_assoc]
      conv_rhs =>
        rw [mul_assoc]
      have h1 : (Complex.abs (f y) * Complex.abs (Complex.exp (-(↑m * ↑ω * ↑y ^ 2) / (2 * ↑ℏ))))
        = Complex.abs (f y) * Real.exp (-(m * ω * y ^ 2) / (2 * ℏ)) := by
        simp
        left
        rw [Complex.abs_exp]
        congr
        trans (Complex.ofReal (-(m * ω * y ^ 2) / (2 * ℏ))).re
        · congr
          simp
        · rw [Complex.ofReal_re]
      rw [h1]
      by_cases hf : Complex.abs (f y) = 0
      · simp [hf]
      rw [_root_.mul_le_mul_right]
      · have h1 := Real.sum_le_exp_of_nonneg (x := |c * y|) (abs_nonneg (c * y)) n
        refine le_trans ?_ h1
        have h2 :  Complex.abs (∑ i ∈ range n, (Complex.I * (↑c * ↑y)) ^ i / ↑i !) ≤
          ∑ i ∈ range n, Complex.abs ((Complex.I * (↑c * ↑y)) ^ i / ↑i !) := by
          exact AbsoluteValue.sum_le _ _ _
        refine le_trans h2 ?_
        apply le_of_eq
        congr
        funext i
        simp
        congr
        rw [abs_mul]
      · refine mul_pos ?_ ?_
        have h1 : 0 ≤  Complex.abs (f y) := by exact AbsoluteValue.nonneg Complex.abs (f y)
        apply lt_of_le_of_ne h1 (fun a => hf (id (Eq.symm a)))
        exact Real.exp_pos (-(m * ω * y ^ 2) / (2 * ℏ))
    · apply Filter.Eventually.of_forall
      intro y
      exact h1 y
  have h3b  : (fun n => ∫ y : ℝ, ∑ r ∈ range n,
      (Complex.I * ↑c * ↑y) ^ r / r ! * (f y * Real.exp (- m * ω * y^2 / (2 * ℏ)))) = fun (n : ℕ) => 0 := by
    funext n
    rw [MeasureTheory.integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro r hr
      have hf' : (fun a => (Complex.I * ↑c * ↑a) ^ r / ↑r ! * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ)))))
        = fun a => ((Complex.I * ↑c) ^ r / ↑r !) * (a^ r * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ))))) := by
        funext a
        simp
        ring
      rw [hf']
      rw [MeasureTheory.integral_mul_left]
      rw [Q.orthogonal_power_of_mem_orthogonal f hf hOrth r]
      simp
    · intro r hr
      have hf' : (fun a => (Complex.I * ↑c * ↑a) ^ r / ↑r ! * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ)))))
        = ((Complex.I * ↑c) ^ r / ↑r !)  • fun a => (a^ r * (f a * ↑(Real.exp (-m * ω * a ^ 2 / (2 * ℏ))))) := by
        funext a
        simp
        ring
      rw [hf']
      apply MeasureTheory.Integrable.smul
      exact Q.mul_power_integrable f hf  r
  rw [h3b] at h1'
  apply tendsto_nhds_unique h1'
  rw [tendsto_const_nhds_iff]


open FourierTransform MeasureTheory Real Lp Memℒp Filter Complex Topology ComplexInnerProductSpace ComplexConjugate


lemma fourierIntegral_zero_of_mem_orthogonal  (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n) , HilbertSpace.mk hf⟫_ℂ = 0) :
    𝓕 (fun x => f x * Real.exp (- m * ω * x^2 / (2 * ℏ))) = 0 := by
  funext c
  rw [Real.fourierIntegral_eq]
  simp
  rw [← Q.orthogonal_exp_of_mem_orthogonal f hf hOrth (- 2 * Real.pi * c)]
  congr
  funext x
  simp [Real.fourierChar, Circle.exp]
  change Complex.exp (-(2 * ↑Real.pi * (↑x * ↑c) * Complex.I)) *
    (f x * Complex.exp (-(↑m * ↑ω * ↑x ^ 2) / (2 * ↑ℏ))) = _
  congr 2
  ring

lemma zero_of_orthogonal_mk  (f : ℝ → ℂ) (hf : MemHS f)
    (hOrth : ∀ n : ℕ, ⟪HilbertSpace.mk (Q.eigenfunction_memHS n) , HilbertSpace.mk hf⟫_ℂ = 0)
    (plancherel_theorem: ∀ {f : ℝ → ℂ} (hf : Integrable f volume) (_ : Memℒp f 2),
       eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume):
    HilbertSpace.mk hf = 0 := by
  have hf' : (fun x => f x * ↑(rexp (-m * ω * x ^ 2 / (2 * ℏ))))
        = (fun x => f x * ↑(rexp (- (m * ω / (2 * ℏ)) * (x - 0) ^ 2 ))) := by
        funext x
        simp
        left
        congr
        field_simp
  have h1 : eLpNorm (fun x => f x * Real.exp (- m * ω * x^2 / (2 * ℏ))) 2 volume = 0 := by
    rw [← plancherel_theorem]
    rw [Q.fourierIntegral_zero_of_mem_orthogonal f hf hOrth]
    simp
    · /-  f x * Real.exp (- m * ω * x^2 / (2 * ℏ)) is integrable -/
      rw [hf']
      rw [← memℒp_one_iff_integrable]
      apply HilbertSpace.mul_gaussian_mem_Lp_one f hf hb (m * ω / (2 * ℏ)) 0
      refine div_pos ?_ ?_
      · exact mul_pos hm hω
      · linarith
    ·  /-  f x * Real.exp (- m * ω * x^2 / (2 * ℏ)) is square-integrable -/
      rw [hf']
      refine HilbertSpace.mul_gaussian_mem_Lp_two f hf hb (m * ω / (2 * ℏ)) 0 ?_
      refine div_pos ?_ ?_
      · exact mul_pos hm hω
      · linarith
  refine (norm_eq_zero_iff (by simp)).mp ?_
  simp [Norm.norm]
  have h2 : eLpNorm f 2 volume = 0 := by
    rw [MeasureTheory.eLpNorm_eq_zero_iff]  at h1 ⊢
    rw [Filter.eventuallyEq_iff_all_subsets] at h1 ⊢
    have h3 (x : ℝ) :  f x * ↑(rexp (-m * ω * x ^ 2 / (2 * ℏ))) = 0  ↔
      f x = 0 := by simp
    simp [h3] at h1
    exact h1
    exact hf
    simp
    ·  /-  f x * Real.exp (- m * ω * x^2 / (2 * ℏ)) is strongly measurable -/
      rw [hf']
      apply Integrable.aestronglyMeasurable
      rw [← memℒp_one_iff_integrable]
      apply HilbertSpace.mul_gaussian_mem_Lp_one f hf hb (m * ω / (2 * ℏ)) 0
      refine div_pos ?_ ?_
      · exact mul_pos hm hω
      · linarith
    · simp
  rw [h2]
  simp

lemma zero_of_orthogonal_eigenVector   {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (f : HilbertSpace)
    (hOrth : ∀ n : ℕ, ⟪eigenVector hℏ hm hω n, f⟫_ℂ = 0)
    (plancherel_theorem: ∀ {f : ℝ → ℂ} (hf : Integrable f volume) (_ : Memℒp f 2),
       eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume) : f = 0 := by
  have hf : f.1 = AEEqFun.mk (f : ℝ → ℂ) (Lp.aestronglyMeasurable f) := by
    exact Eq.symm (AEEqFun.mk_coeFn _)
  have hf2 : f = ⟨AEEqFun.mk (f : ℝ → ℂ) (Lp.aestronglyMeasurable f) , by
    rw [← hf]
    exact f.2⟩ := by
    simp
  rw [hf2]
  apply zero_of_orthogonal_mk
  · rw [← hf2]
    exact hOrth
  · exact plancherel_theorem

lemma completness_eigenvector  {m ℏ ω : ℝ} (hℏ : 0 < ℏ) (hm : 0 < m)
    (hω : 0 < ω) (plancherel_theorem : ∀ {f : ℝ → ℂ} (hf : Integrable f volume) (_ : Memℒp f 2),
       eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume)  :
    (Submodule.span ℂ (Set.range (eigenVector hℏ hm hω))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff]
  refine (Submodule.eq_bot_iff (Submodule.span ℂ (Set.range (eigenVector hℏ hm hω)))ᗮ).mpr ?_
  intro f hf
  apply zero_of_orthogonal_eigenVector hℏ hm hω f ?_ plancherel_theorem
  intro n
  rw [@Submodule.mem_orthogonal'] at hf
  rw [← inner_conj_symm]
  have hl : ⟪f, eigenVector hℏ hm hω n⟫_ℂ = 0 := by
    apply hf
    refine Finsupp.mem_span_range_iff_exists_finsupp.mpr ?_
    use Finsupp.single n 1
    simp
  rw [hl]
  simp

end HarmonicOscillator
end OneDimension
end QuantumMechanics
