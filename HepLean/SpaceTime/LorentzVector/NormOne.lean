/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Basic
import HepLean.SpaceTime.MinkowskiMetric
/-!

# Lorentz vectors with norm one

-/

open minkowskiMetric

/-- The set of Lorentz vectors with norm 1. -/
@[simp]
def NormOneLorentzVector (d : ℕ) : Set (LorentzVector d) :=
  fun x => ⟪x, x⟫ₘ = 1

instance : TopologicalSpace (NormOneLorentzVector d) := instTopologicalSpaceSubtype

namespace NormOneLorentzVector

variable {d : ℕ}

section
variable (v w : NormOneLorentzVector d)

lemma mem_iff {x : LorentzVector d} : x ∈ NormOneLorentzVector d ↔ ⟪x, x⟫ₘ = 1 := by
  rfl

/-- The negative of a `NormOneLorentzVector` as a `NormOneLorentzVector`. -/
def neg : NormOneLorentzVector d := ⟨- v, by
  rw [mem_iff]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact v.2⟩

lemma time_sq : v.1.time ^ 2 = 1 + ‖v.1.space‖ ^ 2 := by
  rw [time_sq_eq_metric_add_space, v.2]

lemma abs_time_ge_one : 1 ≤ |v.1.time| := by
  have h1 := leq_time_sq v.1
  rw [v.2] at h1
  exact (one_le_sq_iff_one_le_abs _).mp h1

lemma norm_space_le_abs_time : ‖v.1.space‖ < |v.1.time| := by
  rw [(abs_norm _).symm, ← @sq_lt_sq, time_sq]
  exact lt_one_add (‖(v.1).space‖ ^ 2)

lemma norm_space_leq_abs_time : ‖v.1.space‖ ≤ |v.1.time| :=
  le_of_lt (norm_space_le_abs_time v)

lemma time_le_minus_one_or_ge_one : v.1.time ≤ -1 ∨ 1 ≤ v.1.time :=
  le_abs'.mp (abs_time_ge_one v)

lemma time_nonpos_iff : v.1.time ≤ 0 ↔ v.1.time ≤ - 1 := by
  apply Iff.intro
  · intro h
    cases' time_le_minus_one_or_ge_one v with h1 h1
    exact h1
    linarith
  · intro h
    linarith

lemma time_nonneg_iff : 0 ≤ v.1.time ↔ 1 ≤ v.1.time := by
  apply Iff.intro
  · intro h
    cases' time_le_minus_one_or_ge_one v with h1 h1
    linarith
    exact h1
  · intro h
    linarith

lemma time_pos_iff : 0 < v.1.time ↔ 1 ≤ v.1.time := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · exact (time_nonneg_iff v).mp (le_of_lt h)
  · linarith

lemma time_abs_sub_space_norm :
    0 ≤ |v.1.time| * |w.1.time| - ‖v.1.space‖ * ‖w.1.space‖ := by
  apply sub_nonneg.mpr
  apply mul_le_mul (norm_space_leq_abs_time v) (norm_space_leq_abs_time w) ?_ ?_
  exact norm_nonneg w.1.space
  exact abs_nonneg (v.1 _)

/-!

# Future pointing norm one Lorentz vectors

-/

/-- The future pointing Lorentz vectors with Norm one. -/
def FuturePointing (d : ℕ) : Set (NormOneLorentzVector d) :=
  fun x => 0 < x.1.time

instance : TopologicalSpace (FuturePointing d) := instTopologicalSpaceSubtype

namespace FuturePointing

section
variable (f f' : FuturePointing d)

lemma mem_iff : v ∈ FuturePointing d ↔ 0 < v.1.time := by
  rfl

lemma mem_iff_time_nonneg : v ∈ FuturePointing d ↔ 0 ≤ v.1.time := by
  refine Iff.intro (fun h => le_of_lt h) (fun h => ?_)
  rw [time_nonneg_iff] at h
  rw [mem_iff]
  linarith

lemma not_mem_iff : v ∉ FuturePointing d ↔ v.1.time ≤ 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  exact le_of_not_lt ((mem_iff v).mp.mt h)
  have h1 := (mem_iff v).mp.mt
  simp at h1
  exact h1 h

lemma not_mem_iff_neg : v ∉ FuturePointing d ↔ neg v ∈ FuturePointing d := by
  rw [not_mem_iff, mem_iff_time_nonneg]
  simp only [Fin.isValue, neg]
  change _ ↔ 0 ≤ - v.1 _
  exact Iff.symm neg_nonneg

lemma time_nonneg : 0 ≤ f.1.1.time := le_of_lt f.2

lemma abs_time : |f.1.1.time| = f.1.1.time := abs_of_nonneg (time_nonneg f)

lemma time_eq_sqrt : f.1.1.time = √(1 + ‖f.1.1.space‖ ^ 2) := by
  symm
  rw [Real.sqrt_eq_cases]
  apply Or.inl
  rw [← time_sq, sq]
  exact ⟨rfl, time_nonneg f⟩

/-!

# The sign of ⟪v, w.1⟫ₘ different v and w

-/

lemma metric_nonneg : 0 ≤ ⟪f, f'.1.1⟫ₘ := by
  apply le_trans (time_abs_sub_space_norm f f'.1)
  rw [abs_time f, abs_time f']
  exact ge_sub_norm f.1.1 f'.1.1

lemma one_add_metric_non_zero : 1 + ⟪f, f'.1.1⟫ₘ ≠ 0 := by
  linarith [metric_nonneg f f']

/-!

# The sign of ⟪v, w.1.spaceReflection⟫ₘ different v and w

-/

section
variable {v w : NormOneLorentzVector d}

lemma metric_reflect_mem_mem (h : v ∈ FuturePointing d) (hw : w ∈ FuturePointing d) :
    0 ≤ ⟪v.1, w.1.spaceReflection⟫ₘ := by
  apply le_trans (time_abs_sub_space_norm v w)
  rw [abs_time ⟨v, h⟩, abs_time ⟨w, hw⟩ , sub_eq_add_neg, right_spaceReflection]
  apply (add_le_add_iff_left _).mpr
  rw [neg_le]
  apply le_trans (neg_le_abs _ : _ ≤ |⟪(v.1).space, (w.1).space⟫_ℝ|) ?_
  exact abs_real_inner_le_norm (v.1).space (w.1).space

lemma metric_reflect_not_mem_not_mem (h : v ∉ FuturePointing d) (hw : w ∉ FuturePointing d) :
    0 ≤ ⟪v.1, w.1.spaceReflection⟫ₘ := by
  have h1 := metric_reflect_mem_mem ((not_mem_iff_neg v).mp h) ((not_mem_iff_neg w).mp hw)
  apply le_of_le_of_eq h1 ?_
  simp [neg]

lemma metric_reflect_mem_not_mem (h : v ∈ FuturePointing d) (hw : w ∉ FuturePointing d) :
    ⟪v.1, w.1.spaceReflection⟫ₘ ≤ 0 := by
  rw [show (0 : ℝ) = - 0 from zero_eq_neg.mpr rfl, le_neg]
  have h1 := metric_reflect_mem_mem h ((not_mem_iff_neg w).mp hw)
  apply le_of_le_of_eq h1 ?_
  simp [neg]

lemma metric_reflect_not_mem_mem (h : v ∉ FuturePointing d) (hw : w ∈ FuturePointing d) :
    ⟪v.1, w.1.spaceReflection⟫ₘ ≤ 0 := by
  rw [show (0 : ℝ) = - 0 from zero_eq_neg.mpr rfl, le_neg]
  have h1 := metric_reflect_mem_mem ((not_mem_iff_neg v).mp h) hw
  apply le_of_le_of_eq h1 ?_
  simp [neg]

end
end

end FuturePointing
end

namespace FuturePointing
/-!

# Topology

-/
open LorentzVector

/-- The `FuturePointing d` which has all space components zero. -/
@[simps!]
noncomputable def timeVecNormOneFuture : FuturePointing d := ⟨⟨timeVec, by
  rw [NormOneLorentzVector.mem_iff, on_timeVec]⟩, by
  rw [mem_iff, timeVec_time]; exact Real.zero_lt_one⟩

/-- A continuous path from `timeVecNormOneFuture` to any other. -/
noncomputable def pathFromTime (u : FuturePointing d) : Path timeVecNormOneFuture u where
  toFun t := ⟨
    ⟨fun i => match i with
      | Sum.inl 0 => √(1 + t ^ 2 * ‖u.1.1.space‖ ^ 2)
      | Sum.inr i => t * u.1.1.space i,
    by
      rw [NormOneLorentzVector.mem_iff, minkowskiMetric.eq_time_minus_inner_prod]
      simp only [time, space, Function.comp_apply, PiLp.inner_apply, RCLike.inner_apply, map_mul,
        conj_trivial]
      rw [Real.mul_self_sqrt, ← @real_inner_self_eq_norm_sq, @PiLp.inner_apply]
      simp only [Function.comp_apply, RCLike.inner_apply, conj_trivial]
      refine Eq.symm (eq_sub_of_add_eq (congrArg (HAdd.hAdd 1) ?_))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
      exact Right.add_nonneg (zero_le_one' ℝ) $ mul_nonneg (sq_nonneg _) (sq_nonneg _) ⟩,
    by
      simp only [space, Function.comp_apply, mem_iff_time_nonneg, time, Real.sqrt_pos]
      exact Real.sqrt_nonneg _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    apply (continuous_pi_iff).mpr
    intro i
    match i with
    | Sum.inl 0 =>
      continuity
    | Sum.inr i =>
      continuity
  source' := by
    ext
    funext i
    match i with
    | Sum.inl 0 =>
      simp only [Set.Icc.coe_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, space,
        zero_mul, add_zero, Real.sqrt_one, Fin.isValue, timeVecNormOneFuture_coe_coe]
      exact Eq.symm timeVec_time
    | Sum.inr i =>
      simp only [Set.Icc.coe_zero, space, Function.comp_apply, zero_mul,
        timeVecNormOneFuture_coe_coe]
      change _ = timeVec.space i
      rw [timeVec_space]
      rfl
  target' := by
    ext
    funext i
    match i with
    | Sum.inl 0 =>
      simp only [Set.Icc.coe_one, one_pow, space, one_mul, Fin.isValue]
      exact (time_eq_sqrt u).symm
    | Sum.inr i =>
      simp only [Set.Icc.coe_one, one_pow, space, one_mul, Fin.isValue]
      exact rfl

lemma isPathConnected : IsPathConnected (@Set.univ (FuturePointing d)) := by
  use timeVecNormOneFuture
  apply And.intro trivial ?_
  intro y a
  use pathFromTime y
  exact fun _ => a

lemma metric_continuous (u : LorentzVector d) :
    Continuous (fun (a : FuturePointing d) => ⟪u, a.1.1⟫ₘ) := by
  simp only [minkowskiMetric.eq_time_minus_inner_prod]
  refine Continuous.add ?_ ?_
  · refine Continuous.comp' (continuous_mul_left _) $ Continuous.comp'
      (continuous_apply (Sum.inl 0))
      (Continuous.comp' continuous_subtype_val continuous_subtype_val)
  · refine Continuous.comp' continuous_neg $ Continuous.inner
     (Continuous.comp' (Pi.continuous_precomp Sum.inr) continuous_const)
     (Continuous.comp' (Pi.continuous_precomp Sum.inr) (Continuous.comp'
      continuous_subtype_val continuous_subtype_val))

end FuturePointing

end NormOneLorentzVector
