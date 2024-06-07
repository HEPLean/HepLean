/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Metric
/-!
# Four velocity

We define

- `PreFourVelocity` : as a space-time element with norm 1.
- `FourVelocity` : as a space-time element with norm 1 and future pointing.

-/
open spaceTime

/-- A `spaceTime` vector for which `ηLin x x = 1`. -/
@[simp]
def PreFourVelocity : Set spaceTime :=
  fun x => ηLin x x = 1

instance : TopologicalSpace PreFourVelocity := by
  exact instTopologicalSpaceSubtype

namespace PreFourVelocity
lemma mem_PreFourVelocity_iff {x : spaceTime} : x ∈ PreFourVelocity ↔ ηLin x x = 1 := by
  rfl

/-- The negative of a `PreFourVelocity` as a `PreFourVelocity`. -/
def neg (v : PreFourVelocity) : PreFourVelocity := ⟨-v, by
  rw [mem_PreFourVelocity_iff]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact v.2 ⟩

lemma zero_sq (v : PreFourVelocity) : v.1 0 ^ 2 = 1 + ‖v.1.space‖ ^ 2  := by
  rw [time_elm_sq_of_ηLin, v.2]

lemma zero_abs_ge_one (v : PreFourVelocity) : 1 ≤ |v.1 0| := by
  have h1 := ηLin_leq_time_sq v.1
  rw [v.2] at h1
  exact (one_le_sq_iff_one_le_abs _).mp h1


lemma zero_abs_gt_norm_space (v : PreFourVelocity) : ‖v.1.space‖ < |v.1 0| := by
  rw [(abs_norm _).symm, ← @sq_lt_sq, zero_sq]
  simp only [space, Fin.isValue, lt_add_iff_pos_left, zero_lt_one]

lemma zero_abs_ge_norm_space (v : PreFourVelocity) : ‖v.1.space‖ ≤ |v.1 0| :=
  le_of_lt (zero_abs_gt_norm_space v)

lemma zero_le_minus_one_or_ge_one (v : PreFourVelocity) : v.1 0 ≤ -1 ∨ 1 ≤ v.1 0 :=
  le_abs'.mp (zero_abs_ge_one v)

lemma zero_nonpos_iff (v : PreFourVelocity) : v.1 0 ≤ 0 ↔ v.1 0 ≤ - 1 := by
  apply Iff.intro
  · intro h
    cases' zero_le_minus_one_or_ge_one v with h1 h1
    exact h1
    linarith
  · intro h
    linarith

lemma zero_nonneg_iff (v : PreFourVelocity) : 0 ≤ v.1 0 ↔ 1 ≤ v.1 0 := by
  apply Iff.intro
  · intro h
    cases' zero_le_minus_one_or_ge_one v with h1 h1
    linarith
    exact h1
  · intro h
    linarith

/-- A `PreFourVelocity` is a `FourVelocity` if its time component is non-negative. -/
def IsFourVelocity (v : PreFourVelocity) : Prop := 0 ≤ v.1 0


lemma IsFourVelocity_abs_zero {v : PreFourVelocity} (hv : IsFourVelocity v) :
    |v.1 0| = v.1 0 := abs_of_nonneg hv

lemma not_IsFourVelocity_iff (v : PreFourVelocity) : ¬ IsFourVelocity v ↔ v.1 0 ≤ 0 := by
  rw [IsFourVelocity, not_le]
  apply Iff.intro
  intro h
  exact le_of_lt h
  intro h
  have h1 := (zero_nonpos_iff v).mp h
  linarith

lemma not_IsFourVelocity_iff_neg {v : PreFourVelocity} : ¬ IsFourVelocity v ↔
    IsFourVelocity (neg v):= by
  rw [not_IsFourVelocity_iff, IsFourVelocity]
  simp only [Fin.isValue, neg]
  change _ ↔ 0 ≤ - v.1 0
  simp

lemma zero_abs_mul_sub_norm_space (v v' : PreFourVelocity) :
    0 ≤ |v.1 0| * |v'.1 0| - ‖v.1.space‖ * ‖v'.1.space‖ := by
  apply sub_nonneg.mpr
  apply mul_le_mul (zero_abs_ge_norm_space v) (zero_abs_ge_norm_space v') ?_ ?_
  exact norm_nonneg v'.1.space
  exact abs_nonneg (v.1 0)


lemma euclid_norm_IsFourVelocity_IsFourVelocity {v v' : PreFourVelocity}
    (h : IsFourVelocity v) (h' : IsFourVelocity v') :
    0 ≤ (v.1 0) * (v'.1 0) + ⟪v.1.space, v'.1.space⟫_ℝ := by
  apply le_trans (zero_abs_mul_sub_norm_space v v')
  rw [IsFourVelocity_abs_zero h, IsFourVelocity_abs_zero h', sub_eq_add_neg]
  apply (add_le_add_iff_left _).mpr
  rw [@neg_le]
  apply le_trans (neg_le_abs _ : _ ≤ |⟪(v.1).space, (v'.1).space⟫_ℝ|) ?_
  exact abs_real_inner_le_norm (v.1).space (v'.1).space

lemma euclid_norm_not_IsFourVelocity_not_IsFourVelocity {v v' : PreFourVelocity}
    (h : ¬ IsFourVelocity v) (h' : ¬ IsFourVelocity v') :
    0 ≤ (v.1 0) * (v'.1 0) + ⟪v.1.space, v'.1.space⟫_ℝ := by
  have h1 := euclid_norm_IsFourVelocity_IsFourVelocity (not_IsFourVelocity_iff_neg.mp h)
    (not_IsFourVelocity_iff_neg.mp h')
  apply le_of_le_of_eq h1 ?_
  simp [neg, Fin.sum_univ_three, neg]
  repeat rw [show (- v.1) _ = - v.1 _ from rfl]
  repeat rw [show (- v'.1) _ = - v'.1 _ from rfl]
  ring

lemma euclid_norm_IsFourVelocity_not_IsFourVelocity {v v' : PreFourVelocity}
    (h : IsFourVelocity v) (h' : ¬ IsFourVelocity v') :
    (v.1 0) * (v'.1 0) + ⟪v.1.space, v'.1.space⟫_ℝ ≤ 0 := by
  rw [show (0 : ℝ) = - 0 by simp, le_neg]
  have h1 := euclid_norm_IsFourVelocity_IsFourVelocity h (not_IsFourVelocity_iff_neg.mp h')
  apply le_of_le_of_eq h1 ?_
  simp [neg, Fin.sum_univ_three, neg]
  repeat rw [show (- v'.1) _ = - v'.1 _ from rfl]
  ring

lemma euclid_norm_not_IsFourVelocity_IsFourVelocity {v v' : PreFourVelocity}
    (h : ¬ IsFourVelocity v) (h' : IsFourVelocity v') :
    (v.1 0) * (v'.1 0) + ⟪v.1.space, v'.1.space⟫_ℝ ≤ 0 := by
  rw [show (0 : ℝ) = - 0 by simp, le_neg]
  have h1 := euclid_norm_IsFourVelocity_IsFourVelocity h' (not_IsFourVelocity_iff_neg.mp h)
  apply le_of_le_of_eq h1 ?_
  simp [neg, Fin.sum_univ_three, neg]
  repeat rw [show (- v.1) _ = - v.1 _ from rfl]
  ring

end PreFourVelocity

/-- The set of `PreFourVelocity`'s which are four velocities. -/
def FourVelocity : Set PreFourVelocity :=
  fun x => PreFourVelocity.IsFourVelocity x

instance : TopologicalSpace FourVelocity := instTopologicalSpaceSubtype

namespace FourVelocity
open PreFourVelocity

lemma mem_FourVelocity_iff {x : PreFourVelocity} : x ∈ FourVelocity ↔ 0 ≤ x.1 0 := by
  rfl

lemma time_comp (x : FourVelocity) : x.1.1 0 = √(1 + ‖x.1.1.space‖ ^ 2) := by
  symm
  rw [Real.sqrt_eq_cases]
  refine Or.inl (And.intro ?_ x.2)
  rw [← PreFourVelocity.zero_sq x.1, sq]

/-- The `FourVelocity` which has all space components zero. -/
def zero : FourVelocity := ⟨⟨![1, 0, 0, 0], by
  rw [mem_PreFourVelocity_iff, ηLin_expand]; simp⟩, by
  rw [mem_FourVelocity_iff]; simp⟩


/-- A continuous path from the zero `FourVelocity` to any other. -/
noncomputable def pathFromZero (u : FourVelocity) : Path zero u where
  toFun t := ⟨
    ⟨![√(1 + t ^ 2 * ‖u.1.1.space‖ ^ 2), t * u.1.1 1, t * u.1.1 2, t * u.1.1 3],
    by
      rw [mem_PreFourVelocity_iff, ηLin_expand]
      simp only [space, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons,
        Matrix.cons_val_three]
      rw [Real.mul_self_sqrt, ← @real_inner_self_eq_norm_sq, @PiLp.inner_apply, Fin.sum_univ_three]
      simp only [Fin.isValue, Matrix.cons_val_zero, RCLike.inner_apply, conj_trivial,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Nat.succ_eq_add_one,
        Nat.reduceAdd, Matrix.tail_cons]
      ring
      refine Right.add_nonneg (zero_le_one' ℝ) $
            mul_nonneg (sq_nonneg _) (sq_nonneg _) ⟩,
    by
      rw [mem_FourVelocity_iff]
      exact Real.sqrt_nonneg _⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    apply (continuous_pi_iff).mpr
    intro i
    fin_cases i
      <;> continuity
  source' := by
    simp only [Set.Icc.coe_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, space,
      Fin.isValue, zero_mul, add_zero, Real.sqrt_one]
    rfl
  target' := by
    simp only [Set.Icc.coe_one, one_pow, space, Fin.isValue, one_mul]
    refine SetCoe.ext ?_
    refine SetCoe.ext ?_
    funext i
    fin_cases i
    simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero]
    exact (time_comp _).symm
    all_goals rfl

lemma isPathConnected_FourVelocity : IsPathConnected (@Set.univ FourVelocity) := by
  use zero
  apply And.intro trivial  ?_
  intro y _
  use pathFromZero y
  simp only [Set.mem_univ, implies_true]

lemma η_pos (u v : FourVelocity) : 0 < ηLin u v := by
  refine lt_of_lt_of_le ?_ (ηLin_ge_sub_norm u v)
  apply sub_pos.mpr
  refine mul_lt_mul_of_nonneg_of_pos ?_ ?_ ?_ ?_
  simpa [IsFourVelocity_abs_zero u.2] using zero_abs_gt_norm_space u.1
  simpa [IsFourVelocity_abs_zero v.2] using zero_abs_ge_norm_space v.1
  exact norm_nonneg u.1.1.space
  have h2 := (mem_FourVelocity_iff).mp v.2
  rw [zero_nonneg_iff] at h2
  linarith

lemma one_plus_ne_zero (u v : FourVelocity) :  1 + ηLin u v ≠ 0 := by
  linarith [η_pos u v]

lemma η_continuous (u : spaceTime) : Continuous (fun (a : FourVelocity) => ηLin u a) := by
  simp only [ηLin_expand]
  refine Continuous.add ?_ ?_
  refine Continuous.add ?_ ?_
  refine Continuous.add ?_ ?_
  refine Continuous.comp' (continuous_mul_left _) ?_
  apply (continuous_pi_iff).mp
  exact Isometry.continuous fun x1 => congrFun rfl
  all_goals apply Continuous.neg
  all_goals apply Continuous.comp' (continuous_mul_left _)
  all_goals apply (continuous_pi_iff).mp
  all_goals exact Isometry.continuous fun x1 => congrFun rfl





end FourVelocity
