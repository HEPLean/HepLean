/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
/-!

# Hilbert space for one dimension quantum mechanics

-/

namespace QuantumMechanics

namespace OneDimension

/-- The Hilbert space in 1d corresponding to square integbrable (equivalence classes)
  of functions. -/
noncomputable abbrev HilbertSpace := MeasureTheory.Lp (α := ℝ) ℂ 2

namespace HilbertSpace

lemma mem_iff {f : ℝ →ₘ[MeasureTheory.volume] ℂ} : f ∈ HilbertSpace
    ↔ MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := by
  rw [HilbertSpace]
  rw [MeasureTheory.Lp.mem_Lp_iff_memℒp]
  simp [MeasureTheory.Memℒp]
  have h1 : MeasureTheory.AEStronglyMeasurable (↑f) MeasureTheory.volume := by
    exact MeasureTheory.AEEqFun.aestronglyMeasurable f
  simp [h1]
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top]
  simp [MeasureTheory.Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable
    (fun x => Complex.abs (f x) ^ 2) MeasureTheory.volume := by
    apply MeasureTheory.AEStronglyMeasurable.pow
    refine Continuous.comp_aestronglyMeasurable ?_ h1
    exact Complex.continuous_abs
  simp [h0]
  simp [MeasureTheory.HasFiniteIntegral]
  simp [enorm, nnnorm]
  exact Ne.symm (NeZero.ne' 2)
  exact ENNReal.ofNat_ne_top

lemma mem_iff' {f : ℝ → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.AEEqFun.mk f hf ∈ HilbertSpace
    ↔ MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := by
  rw [HilbertSpace]
  rw [MeasureTheory.Lp.mem_Lp_iff_memℒp]
  simp [MeasureTheory.Memℒp]
  have h1 : MeasureTheory.AEStronglyMeasurable
    (MeasureTheory.AEEqFun.mk f hf) MeasureTheory.volume := by
    apply MeasureTheory.AEEqFun.aestronglyMeasurable
  simp [h1]
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top]
  simp [MeasureTheory.Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable
    (fun x => Complex.abs (f x) ^ 2) MeasureTheory.volume := by
    apply MeasureTheory.AEStronglyMeasurable.pow
    refine Continuous.comp_aestronglyMeasurable ?_ hf
    exact Complex.continuous_abs
  simp [h0]
  simp [MeasureTheory.HasFiniteIntegral]
  simp [enorm, nnnorm]
  exact Ne.symm (NeZero.ne' 2)
  exact ENNReal.ofNat_ne_top

/-- An element of the Hilbert space from a function `f : ℝ → ℂ` which is square
  integrable and almost everywhere strongly measurable. -/
def ofSqIntegrable (f : ℝ → ℂ) (h : MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2))
    (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) : HilbertSpace :=
  ⟨MeasureTheory.AEEqFun.mk f hf, (mem_iff' hf).mpr h⟩

end HilbertSpace

end OneDimension

end QuantumMechanics
