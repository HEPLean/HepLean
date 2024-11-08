/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Real.Contraction
import Mathlib.GroupTheory.GroupAction.Blocks
/-!

# Lorentz vectors with norm one

-/

open TensorProduct

namespace Lorentz

namespace Contr

variable {d : ℕ}

/-- The set of Lorentz vectors with norm 1. -/
def NormOne (d : ℕ) : Set (Contr d) := fun v => ⟪v, v⟫ₘ = (1 : ℝ)

noncomputable  section

namespace NormOne

lemma mem_iff {v : Contr d} : v ∈ NormOne d ↔ ⟪v, v⟫ₘ = (1 : ℝ) := by
  rfl

lemma mem_mulAction (g : LorentzGroup d) (v : Contr d) :
    v ∈ NormOne d ↔ (Contr d).ρ g v ∈ NormOne d := by
  rw [mem_iff, mem_iff, contrContrContract.action_tmul]

instance : TopologicalSpace (NormOne d) := instTopologicalSpaceSubtype

variable (v w : NormOne d)

/-- The negative of a `NormOne` as a `NormOne`. -/
def neg : NormOne d := ⟨- v, by
  rw [mem_iff]
  simp only [Action.instMonoidalCategory_tensorUnit_V, Action.instMonoidalCategory_tensorObj_V,
    CategoryTheory.Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, tmul_neg, neg_tmul, neg_neg]
  exact v.2⟩

/-- The first column of a Lorentz matrix as a `NormOneLorentzVector`. -/
@[simps!]
def _root_.LorentzGroup.toNormOne (Λ : LorentzGroup d) : NormOne d :=
  ⟨(Contr d).ρ Λ (ContrMod.stdBasis (Sum.inl 0)), by
    rw [mem_iff, contrContrContract.action_tmul, contrContrContract.stdBasis_inl]⟩

lemma _root_.LorentzGroup.toNormOne_inl (Λ : LorentzGroup d) :
    (LorentzGroup.toNormOne Λ).val.val (Sum.inl 0) = Λ.1 (Sum.inl 0) (Sum.inl 0) := by
  simp only [Fin.isValue, LorentzGroup.toNormOne_coe_val, Finsupp.single, one_ne_zero, ↓reduceIte,
    Finsupp.coe_mk, Matrix.mulVec_single, mul_one]

lemma _root_.LorentzGroup.toNormOne_inr (Λ : LorentzGroup d) (i : Fin d) :
    (LorentzGroup.toNormOne Λ).val.val (Sum.inr i) = Λ.1 (Sum.inr i) (Sum.inl 0) := by
  simp only [LorentzGroup.toNormOne_coe_val, Finsupp.single, one_ne_zero, ↓reduceIte, Fin.isValue,
    Finsupp.coe_mk, Matrix.mulVec_single, mul_one]

lemma _root_.LorentzGroup.inl_inl_mul (Λ Λ' : LorentzGroup d) : (Λ * Λ').1 (Sum.inl 0) (Sum.inl 0) =
    ⟪(LorentzGroup.toNormOne (LorentzGroup.transpose Λ)).1,
      (Contr d).ρ LorentzGroup.parity (LorentzGroup.toNormOne Λ').1⟫ₘ := by
  rw [contrContrContract.right_parity]
  simp  only [Fin.isValue, lorentzGroupIsGroup_mul_coe, Matrix.mul_apply, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
    LorentzGroup.transpose, PiLp.inner_apply, Function.comp_apply,
    RCLike.inner_apply, conj_trivial]
  congr
  · rw [LorentzGroup.toNormOne_inl]
    rfl
  · rw [LorentzGroup.toNormOne_inl]
  · funext x
    rw [LorentzGroup.toNormOne_inr, LorentzGroup.toNormOne_inr]
    rfl

lemma inl_sq : v.val.val (Sum.inl 0) ^ 2 = 1 + ‖ContrMod.toSpace v.val‖ ^ 2  := by
  rw [contrContrContract.inl_sq_eq, v.2]
  congr
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  congr
  funext x
  exact pow_two ((v.val).val (Sum.inr x))

lemma one_le_abs_inl : 1 ≤ |v.val.val (Sum.inl 0)| := by
  have h1 := contrContrContract.le_inl_sq v.val
  rw [v.2] at h1
  exact (one_le_sq_iff_one_le_abs _).mp h1

lemma inl_le_neg_one_or_one_le_inl : v.val.val (Sum.inl 0) ≤ -1 ∨ 1 ≤ v.val.val (Sum.inl 0) :=
  le_abs'.mp (one_le_abs_inl v)

lemma norm_space_le_abs_inl : ‖v.1.toSpace‖ < |v.val.val (Sum.inl 0)| := by
  rw [(abs_norm _).symm, ← @sq_lt_sq, inl_sq]
  change  ‖ContrMod.toSpace v.val‖ ^ 2 < 1 + ‖ContrMod.toSpace v.val‖ ^ 2
  exact lt_one_add (‖(v.1).toSpace‖ ^ 2)

lemma norm_space_leq_abs_inl : ‖v.1.toSpace‖ ≤ |v.val.val (Sum.inl 0)| :=
  le_of_lt (norm_space_le_abs_inl v)

lemma inl_abs_sub_space_norm :
    0 ≤ |v.val.val (Sum.inl 0)| * |w.val.val (Sum.inl 0)| - ‖v.1.toSpace‖  * ‖w.1.toSpace‖ := by
  apply sub_nonneg.mpr
  apply mul_le_mul (norm_space_leq_abs_inl v) (norm_space_leq_abs_inl w) ?_ ?_
  · exact norm_nonneg _
  · exact abs_nonneg _

/-!

# Future pointing norm one Lorentz vectors

-/

/-- The future pointing Lorentz vectors with Norm one. -/
def FuturePointing (d : ℕ) : Set (NormOne d) :=
  fun x => 0 < x.val.val (Sum.inl 0)

namespace FuturePointing

lemma mem_iff : v ∈ FuturePointing d ↔ 0 < v.val.val (Sum.inl 0) := by
  rfl

lemma mem_iff_inl_nonneg : v ∈ FuturePointing d ↔ 0 ≤ v.val.val (Sum.inl 0) := by
  refine Iff.intro (fun h => le_of_lt h) (fun h => ?_)
  rw [mem_iff]
  rcases inl_le_neg_one_or_one_le_inl v with (h | h)
  · linarith
  · linarith

lemma mem_iff_inl_one_le_inl : v ∈ FuturePointing d ↔ 1 ≤ v.val.val (Sum.inl 0) := by
  rw [mem_iff_inl_nonneg]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rcases inl_le_neg_one_or_one_le_inl v with (h | h)
    · linarith
    · linarith
  · linarith

lemma mem_iff_parity_mem : v ∈ FuturePointing d ↔ ⟨(Contr d).ρ LorentzGroup.parity v.1,
    (NormOne.mem_mulAction _ _).mp v.2⟩ ∈ FuturePointing d := by
  rw [mem_iff, mem_iff]
  change _ ↔ 0 < (minkowskiMatrix.mulVec v.val.val) (Sum.inl 0)
  simp only [Fin.isValue, minkowskiMatrix.mulVec_inl_0]


lemma not_mem_iff_inl_le_zero : v ∉ FuturePointing d ↔ v.val.val (Sum.inl 0) ≤ 0 := by
  rw [mem_iff]
  simp

lemma not_mem_iff_inl_lt_zero : v ∉ FuturePointing d ↔ v.val.val (Sum.inl 0) < 0 := by
  rw [mem_iff_inl_nonneg]
  simp

lemma not_mem_iff_inl_le_neg_one : v ∉ FuturePointing d ↔ v.val.val (Sum.inl 0) ≤ -1 := by
  rw [not_mem_iff_inl_le_zero]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rcases inl_le_neg_one_or_one_le_inl v with (h | h)
    · linarith
    · linarith
  · linarith

lemma not_mem_iff_neg : v ∉ FuturePointing d ↔ neg v ∈ FuturePointing d := by
  rw [not_mem_iff_inl_le_zero, mem_iff_inl_nonneg]
  simp only [Fin.isValue, neg]
  change (v).val.val (Sum.inl 0) ≤ 0 ↔ 0 ≤ - (v.val).val (Sum.inl 0)
  simp

variable (f f' : FuturePointing d)

lemma inl_nonneg : 0 ≤ f.val.val.val (Sum.inl 0):= le_of_lt f.2

lemma abs_inl : |f.val.val.val (Sum.inl 0)| = f.val.val.val (Sum.inl 0) :=
  abs_of_nonneg (inl_nonneg f)

open InnerProductSpace
lemma metric_nonneg : 0 ≤ toField d ⟪f.1.1, f'.1.1⟫ₘ := by
  apply le_trans (inl_abs_sub_space_norm f f'.1)
  rw [abs_inl f, abs_inl f']
  exact contrContrContract.ge_sub_norm f.1.1 f'.1.1

variable {v w : NormOne d}

lemma metric_reflect_mem_mem (h : v ∈ FuturePointing d) (hw : w ∈ FuturePointing d) :
    0 ≤ toField d ⟪v.val, (Contr d).ρ LorentzGroup.parity w.1⟫ₘ :=
  metric_nonneg ⟨v, h⟩ ⟨⟨(Contr d).ρ LorentzGroup.parity w.1,
    (NormOne.mem_mulAction _ _).mp w.2⟩, (mem_iff_parity_mem w).mp hw⟩

lemma metric_reflect_not_mem_not_mem (h : v ∉ FuturePointing d) (hw : w ∉ FuturePointing d) :
    0 ≤ toField d ⟪v.val, (Contr d).ρ LorentzGroup.parity w.1⟫ₘ := by
  have h1 := metric_reflect_mem_mem ((not_mem_iff_neg v).mp h) ((not_mem_iff_neg w).mp hw)
  apply le_of_le_of_eq h1 ?_
  simp [neg, neg_tmul, tmul_neg]

lemma metric_reflect_mem_not_mem (h : v ∈ FuturePointing d) (hw : w ∉ FuturePointing d) :
   toField d ⟪v.val, (Contr d).ρ LorentzGroup.parity w.1⟫ₘ ≤ 0 := by
  rw [show (0 : ℝ) = - 0 from zero_eq_neg.mpr rfl, le_neg]
  have h1 := metric_reflect_mem_mem h ((not_mem_iff_neg w).mp hw)
  apply le_of_le_of_eq h1 ?_
  simp [neg, neg_tmul, tmul_neg]

lemma metric_reflect_not_mem_mem (h : v ∉ FuturePointing d) (hw : w ∈ FuturePointing d) :
    toField d ⟪v.val, (Contr d).ρ LorentzGroup.parity w.1⟫ₘ ≤ 0 := by
  rw [show (0 : ℝ) = - 0 from zero_eq_neg.mpr rfl, le_neg]
  have h1 := metric_reflect_mem_mem ((not_mem_iff_neg v).mp h) hw
  apply le_of_le_of_eq h1 ?_
  simp [neg, neg_tmul, tmul_neg]

end FuturePointing

end NormOne

end

end Contr
end Lorentz
