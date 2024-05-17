/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Metric
import Mathlib.GroupTheory.SpecificGroups.KleinFour
/-!
# The Lorentz Group

We define the Lorentz group.

## TODO

- Show that the Lorentz is a Lie group.
- Prove that the restricted Lorentz group is equivalent to the connected component of the
identity.
- Define the continuous maps from `ℝ³` to `restrictedLorentzGroup` defining boosts.

## References

- http://home.ku.edu.tr/~amostafazadeh/phys517_518/phys517_2016f/Handouts/A_Jaffi_Lorentz_Group.pdf
- A proof that the restricted Lorentz group is connected can be found at:
  https://diposit.ub.edu/dspace/bitstream/2445/68763/2/memoria.pdf
  The proof involves the introduction of boosts.

-/

noncomputable section

namespace spaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The Lorentz group as a subgroup of the general linear group over the reals. -/
def lorentzGroup : Subgroup (GeneralLinearGroup (Fin 4) ℝ) where
  carrier := {Λ | ∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y}
  mul_mem' {a b} := by
    intros ha hb x y
    simp only [Units.val_mul, mulVec_mulVec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ha, hb]
  one_mem' := by
    intros x y
    simp
  inv_mem' {a} := by
    intros ha x y
    simp only [coe_units_inv, ← ha ((a.1⁻¹) *ᵥ x) ((a.1⁻¹) *ᵥ y), mulVec_mulVec]
    have hx : (a.1 * (a.1)⁻¹) = 1 := by
      simp only [@Units.mul_eq_one_iff_inv_eq, coe_units_inv]
    simp [hx]

/-- The Lorentz group is a topological group with the subset topology. -/
instance : TopologicalGroup lorentzGroup :=
  Subgroup.instTopologicalGroupSubtypeMem lorentzGroup


lemma preserve_ηLin_iff' (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    (∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y) ↔
    ∀ (x y : spaceTime), ηLin (x) ((η * Λᵀ * η * Λ) *ᵥ y) = ηLin x y := by
  apply Iff.intro
  intro h
  intro x y
  have h1 := h x y
  rw [ηLin_mulVec_left, mulVec_mulVec] at h1
  exact h1
  intro h
  intro x y
  rw [ηLin_mulVec_left, mulVec_mulVec]
  exact h x y


lemma preserve_ηLin_iff'' (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    (∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y) ↔
     η * Λᵀ * η * Λ = 1  := by
  rw [preserve_ηLin_iff', ηLin_matrix_eq_identity_iff (η * Λᵀ * η * Λ)]
  apply Iff.intro
  · simp_all  [ηLin, implies_true, iff_true, one_mulVec]
  · simp_all only [ηLin, LinearMap.coe_mk, AddHom.coe_mk, linearMapForSpaceTime_apply,
    mulVec_mulVec, implies_true]

lemma preserve_ηLin_iff''' (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    (∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y) ↔
    Λ * (η * Λᵀ * η) = 1  := by
  rw [preserve_ηLin_iff'']
  apply Iff.intro
  intro h
  exact mul_eq_one_comm.mp h
  intro h
  exact mul_eq_one_comm.mp h

lemma preserve_ηLin_iff_transpose (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    (∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y) ↔
    (∀ (x y : spaceTime), ηLin (Λᵀ *ᵥ x) (Λᵀ *ᵥ y) = ηLin x y) := by
  apply Iff.intro
  intro h
  have h1 := congrArg transpose ((preserve_ηLin_iff'' Λ).mp h)
  rw [transpose_mul, transpose_mul, transpose_mul, η_transpose,
    ← mul_assoc, transpose_one] at h1
  rw [preserve_ηLin_iff''' Λ.transpose, ← h1]
  repeat rw [← mul_assoc]
  intro h
  have h1 := congrArg transpose ((preserve_ηLin_iff'' Λ.transpose).mp h)
  rw [transpose_mul, transpose_mul, transpose_mul, η_transpose,
    ← mul_assoc, transpose_one, transpose_transpose] at h1
  rw [preserve_ηLin_iff''', ← h1]
  repeat rw [← mul_assoc]

def preserveηLinGLnLift {Λ : Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y) : GL (Fin 4) ℝ :=
  ⟨Λ, η * Λᵀ * η  ,(preserve_ηLin_iff''' Λ).mp h , (preserve_ηLin_iff'' Λ).mp h⟩

lemma mem_lorentzGroup_iff (Λ : GeneralLinearGroup (Fin 4) ℝ) :
    Λ ∈ lorentzGroup ↔ ∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y := by
  rfl


lemma mem_lorentzGroup_iff' (Λ : GeneralLinearGroup (Fin 4) ℝ) :
    Λ ∈ lorentzGroup ↔ ∀ (x y : spaceTime), ηLin (x) ((η * Λ.1ᵀ * η * Λ.1) *ᵥ y) = ηLin x y := by
  rw [mem_lorentzGroup_iff]
  exact preserve_ηLin_iff' Λ.1


lemma mem_lorentzGroup_iff'' (Λ : GL (Fin 4) ℝ) :
    Λ ∈ lorentzGroup ↔ η * Λ.1ᵀ * η * Λ.1 = 1 := by
  rw [mem_lorentzGroup_iff]
  exact preserve_ηLin_iff'' Λ

lemma mem_lorentzGroup_iff''' (Λ : GL (Fin 4) ℝ) :
    Λ ∈ lorentzGroup ↔ η * Λ.1ᵀ * η = Λ⁻¹ := by
  rw [mem_lorentzGroup_iff'']
  exact Units.mul_eq_one_iff_eq_inv

def preserveηLinLorentzLift {Λ : Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y) : lorentzGroup :=
  ⟨preserveηLinGLnLift h, (mem_lorentzGroup_iff (preserveηLinGLnLift h)).mpr h⟩

-- TODO: Simplify using preserveηLinLorentzLift.
lemma mem_lorentzGroup_iff_transpose (Λ : GL (Fin 4) ℝ) :
    Λ ∈ lorentzGroup ↔ ⟨transpose Λ, (transpose Λ)⁻¹, by
        rw [← transpose_nonsing_inv, ← transpose_mul, (coe_units_inv Λ).symm]
        rw [show ((Λ)⁻¹).1 * Λ.1 = (1 : Matrix (Fin 4) (Fin 4) ℝ) by rw [@Units.inv_mul_eq_one]]
        rw [@transpose_eq_one], by
        rw [← transpose_nonsing_inv, ← transpose_mul, (coe_units_inv Λ).symm]
        rw [show Λ.1 * ((Λ)⁻¹).1  = (1 : Matrix (Fin 4) (Fin 4) ℝ) by rw [@Units.mul_inv_eq_one]]
        rw [@transpose_eq_one]⟩  ∈ lorentzGroup := by
  rw [mem_lorentzGroup_iff''', mem_lorentzGroup_iff''']
  simp only [coe_units_inv, transpose_transpose, Units.inv_mk]
  apply Iff.intro
  intro h
  have h1 := congrArg transpose h
  rw [transpose_mul, transpose_mul, transpose_transpose, η_transpose, ← mul_assoc] at h1
  rw [h1]
  exact transpose_nonsing_inv _
  intro h
  have h1 := congrArg transpose h
  rw [transpose_mul, transpose_mul, η_transpose, ← mul_assoc] at h1
  rw [h1, transpose_nonsing_inv, transpose_transpose]

/-- The transpose of an matrix in the Lorentz group is an element of the Lorentz group. -/
def lorentzGroupTranspose (Λ : lorentzGroup) : lorentzGroup :=
  ⟨⟨transpose Λ.1, (transpose Λ.1)⁻¹, by
    rw [← transpose_nonsing_inv, ← transpose_mul, (coe_units_inv Λ.1).symm]
    rw [show ((Λ.1)⁻¹).1 * Λ.1 = (1 : Matrix (Fin 4) (Fin 4) ℝ) by rw [@Units.inv_mul_eq_one]]
    rw [@transpose_eq_one], by
    rw [← transpose_nonsing_inv, ← transpose_mul, (coe_units_inv Λ.1).symm]
    rw [show Λ.1.1 * ((Λ.1)⁻¹).1  = (1 : Matrix (Fin 4) (Fin 4) ℝ) by rw [@Units.mul_inv_eq_one]]
    rw [@transpose_eq_one]⟩,
    (mem_lorentzGroup_iff_transpose Λ.1).mp Λ.2 ⟩


/-- A continous map from `GL (Fin 4) ℝ` to  `Matrix (Fin 4) (Fin 4) ℝ` for which the Lorentz
group is the kernal. -/
def lorentzMap (Λ : GL (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ := η * Λ.1ᵀ * η * Λ.1

lemma lorentzMap_continuous : Continuous lorentzMap := by
  apply Continuous.mul _ Units.continuous_val
  apply Continuous.mul _ continuous_const
  exact Continuous.mul continuous_const (Continuous.matrix_transpose (Units.continuous_val))

lemma lorentzGroup_kernal : lorentzGroup = lorentzMap ⁻¹' {1} := by
  ext Λ
  erw [mem_lorentzGroup_iff'' Λ]
  rfl

/-- The Lorentz Group is a closed subset of `GL (Fin 4) ℝ`. -/
theorem lorentzGroup_isClosed : IsClosed (lorentzGroup : Set (GL (Fin 4) ℝ)) := by
  rw [lorentzGroup_kernal]
  exact continuous_iff_isClosed.mp lorentzMap_continuous {1} isClosed_singleton

namespace lorentzGroup


lemma det_eq_one_or_neg_one (Λ : lorentzGroup) : Λ.1.1.det = 1 ∨ Λ.1.1.det = -1 := by
  simpa [← sq, det_one, det_mul, det_mul, det_mul, det_transpose, det_η] using
    (congrArg det ((mem_lorentzGroup_iff'' Λ.1).mp Λ.2))

local notation  "ℤ₂" => Multiplicative (ZMod 2)

instance : TopologicalSpace ℤ₂ := instTopologicalSpaceFin

/-- A group homomorphism from `lorentzGroup` to `ℤ₂` taking a matrix to
0 if it's determinant is 1 and 1 if its determinant is -1.-/
@[simps!]
def detRep : lorentzGroup →* ℤ₂ where
  toFun Λ := if Λ.1.1.det = 1 then (Additive.toMul 0) else Additive.toMul (1 : ZMod 2)
  map_one' := by
    simp
  map_mul' := by
    intro Λ1 Λ2
    simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, Units.val_mul, det_mul, toMul_zero,
      mul_ite, mul_one, ite_mul, one_mul]
    cases' (det_eq_one_or_neg_one Λ1) with h1 h1
      <;> cases' (det_eq_one_or_neg_one Λ2) with h2 h2
      <;> simp [h1, h2]
    rfl

/-- A Lorentz Matrix is proper if its determinant is 1. -/
def IsProper (Λ : lorentzGroup) : Prop := Λ.1.1.det = 1

instance : DecidablePred IsProper := by
  intro Λ
  apply Real.decidableEq

lemma IsProper_iff (Λ : lorentzGroup) :
    IsProper Λ ↔ detRep Λ = Additive.toMul 0 := by
  apply Iff.intro
  intro h
  erw [detRep_apply, if_pos h]
  simp only [toMul_zero]
  intro h
  by_cases h1 : IsProper Λ
  exact h1
  erw [detRep_apply, if_neg h1] at h
  contradiction

section Orthochronous

/-- The space-like part of the first row of of a Lorentz matrix. -/
@[simp]
def fstRowToEuclid (Λ : lorentzGroup) : EuclideanSpace ℝ (Fin 3) := fun i => Λ.1 0 i.succ

/-- The space-like part of the first column of of a Lorentz matrix. -/
@[simp]
def fstColToEuclid (Λ : lorentzGroup) : EuclideanSpace ℝ (Fin 3) := fun i => Λ.1 i.succ 0

lemma fst_col_normalized (Λ : lorentzGroup) :
    (Λ.1 0 0) ^ 2 - (Λ.1 1 0) ^ 2 - (Λ.1 2 0) ^ 2 - (Λ.1 3 0) ^ 2 = 1 := by
  have h00 := congrFun (congrFun ((mem_lorentzGroup_iff'' Λ).mp Λ.2) 0) 0
  simp only [Fin.isValue, mul_apply, transpose_apply, Fin.sum_univ_four, ne_eq, zero_ne_one,
    not_false_eq_true, η_off_diagonal, zero_mul, add_zero, Fin.reduceEq, one_ne_zero, mul_zero,
    zero_add, one_apply_eq] at h00
  simp only [η, Fin.isValue, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one,
    vecCons_const, one_mul, mul_one, cons_val_one, head_cons, mul_neg, neg_mul, cons_val_two,
    Nat.succ_eq_add_one, Nat.reduceAdd, tail_cons, cons_val_three, head_fin_const] at h00
  rw [← h00]
  ring

lemma fst_row_normalized (Λ : lorentzGroup) :
    (Λ.1 0 0) ^ 2 - (Λ.1 0 1) ^ 2 - (Λ.1 0 2) ^ 2 - (Λ.1 0 3) ^ 2 = 1 := by
  simpa using fst_col_normalized (lorentzGroupTranspose Λ)


lemma zero_zero_sq_col (Λ : lorentzGroup) :
    (Λ.1 0 0) ^ 2 = 1 + (Λ.1 1 0) ^ 2 + (Λ.1 2 0) ^ 2 + (Λ.1 3 0) ^ 2 := by
  rw [← fst_col_normalized Λ]
  ring

lemma zero_zero_sq_row (Λ : lorentzGroup) :
    (Λ.1 0 0) ^ 2 = 1 + (Λ.1 0 1) ^ 2 + (Λ.1 0 2) ^ 2 + (Λ.1 0 3) ^ 2 := by
  rw [← fst_row_normalized Λ]
  ring

lemma zero_zero_sq_col' (Λ : lorentzGroup) :
    (Λ.1 0 0) ^ 2 = 1 + ‖fstColToEuclid Λ‖ ^ 2  := by
  rw [zero_zero_sq_col, ← @real_inner_self_eq_norm_sq, @PiLp.inner_apply, Fin.sum_univ_three]
  simp only [Fin.isValue, fstColToEuclid, Fin.succ_zero_eq_one, RCLike.inner_apply, conj_trivial,
    Fin.succ_one_eq_two]
  rw [show (Fin.succ 2) = 3 by rfl]
  ring_nf

lemma zero_zero_sq_row' (Λ : lorentzGroup) :
    (Λ.1 0 0) ^ 2 = 1 + ‖fstRowToEuclid Λ‖ ^ 2  := by
  rw [zero_zero_sq_row, ← @real_inner_self_eq_norm_sq, @PiLp.inner_apply, Fin.sum_univ_three]
  simp only [Fin.isValue, fstRowToEuclid, Fin.succ_zero_eq_one, RCLike.inner_apply, conj_trivial,
    Fin.succ_one_eq_two]
  rw [show (Fin.succ 2) = 3 by rfl]
  ring_nf

lemma norm_col_leq_abs_zero_zero  (Λ : lorentzGroup) : ‖fstColToEuclid Λ‖ ≤ |Λ.1 0 0| := by
  rw [(abs_norm (fstColToEuclid Λ)).symm, ← @sq_le_sq, zero_zero_sq_col']
  simp only [le_add_iff_nonneg_left, zero_le_one]

lemma norm_row_leq_abs_zero_zero (Λ : lorentzGroup)  : ‖fstRowToEuclid Λ‖ ≤ |Λ.1 0 0| := by
  rw [(abs_norm (fstRowToEuclid Λ)).symm, ← @sq_le_sq, zero_zero_sq_row']
  simp only [le_add_iff_nonneg_left, zero_le_one]


lemma zero_zero_sq_ge_one (Λ : lorentzGroup) : 1 ≤ (Λ.1 0 0) ^ 2 := by
  rw [zero_zero_sq_col Λ]
  refine le_add_of_le_of_nonneg ?_ (sq_nonneg _)
  refine le_add_of_le_of_nonneg ?_ (sq_nonneg _)
  refine le_add_of_le_of_nonneg (le_refl 1) (sq_nonneg _)

lemma abs_zero_zero_ge_one (Λ : lorentzGroup) : 1 ≤ |Λ.1 0 0| :=
  (one_le_sq_iff_one_le_abs _).mp (zero_zero_sq_ge_one Λ)

lemma zero_zero_le_minus_one_or_ge_one (Λ : lorentzGroup) : (Λ.1 0 0) ≤ - 1 ∨ 1 ≤ (Λ.1 0 0) :=
  le_abs'.mp (abs_zero_zero_ge_one Λ)

lemma zero_zero_nonpos_iff (Λ : lorentzGroup) : (Λ.1 0 0) ≤ 0 ↔ (Λ.1 0 0) ≤ - 1 := by
  apply Iff.intro
  · intro h
    cases' zero_zero_le_minus_one_or_ge_one Λ with h1 h1
    exact h1
    linarith
  · intro h
    linarith

lemma zero_zero_nonneg_iff (Λ : lorentzGroup) : 0 ≤ (Λ.1 0 0) ↔ 1 ≤ (Λ.1 0 0) := by
  apply Iff.intro
  · intro h
    cases' zero_zero_le_minus_one_or_ge_one Λ with h1 h1
    linarith
    exact h1
  · intro h
    linarith

/-- An element of the lorentz group is orthochronous if its time-time element is non-negative. -/
@[simp]
def IsOrthochronous (Λ : lorentzGroup) : Prop := 0 ≤ Λ.1 0 0

instance : Decidable (IsOrthochronous Λ) :=
  Real.decidableLE 0 (Λ.1 0 0)

lemma not_IsOrthochronous_iff (Λ : lorentzGroup) : ¬ IsOrthochronous Λ ↔ Λ.1 0 0 ≤ 0 := by
  rw [IsOrthochronous, not_le]
  apply Iff.intro
  intro h
  exact le_of_lt h
  intro h
  have h1 := (zero_zero_nonpos_iff Λ).mp h
  linarith


lemma IsOrthochronous_abs_zero_zero {Λ : lorentzGroup} (h : IsOrthochronous Λ) :
    |Λ.1 0 0| = Λ.1 0 0 :=
  abs_eq_self.mpr h

lemma not_IsOrthochronous_abs_zero_zero {Λ : lorentzGroup} (h : ¬ IsOrthochronous Λ) :
    Λ.1 0 0  = - |Λ.1 0 0| := by
  refine neg_eq_iff_eq_neg.mp (abs_eq_neg_self.mpr ?_).symm
  simp only [IsOrthochronous, Fin.isValue, not_le] at h
  exact le_of_lt h

lemma schwartz_identity_fst_row_col (Λ Λ' : lorentzGroup) :
    ‖⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ‖ ≤ ‖fstRowToEuclid Λ‖ * ‖fstColToEuclid Λ'‖ :=
  norm_inner_le_norm (fstRowToEuclid Λ) (fstColToEuclid Λ')

lemma zero_zero_mul (Λ Λ' : lorentzGroup) :
    (Λ * Λ').1 0 0 = (Λ.1 0 0) * (Λ'.1 0 0) + ⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ := by
  rw [@Subgroup.coe_mul, @GeneralLinearGroup.coe_mul, mul_apply, Fin.sum_univ_four]
  rw [@PiLp.inner_apply, Fin.sum_univ_three]
  simp
  rw [show (Fin.succ 2) = 3 by rfl]
  ring_nf
example (a b c : ℝ ) (h : a - b ≤ a + c) : - b ≤ c := by
  exact (add_le_add_iff_left a).mp h

lemma zero_zero_mul_sub_row_col (Λ Λ' : lorentzGroup) :
    0 ≤ |Λ.1 0 0| * |Λ'.1 0 0| - ‖fstRowToEuclid Λ‖ * ‖fstColToEuclid Λ'‖ :=
  sub_nonneg.mpr (mul_le_mul (norm_row_leq_abs_zero_zero Λ) (norm_col_leq_abs_zero_zero Λ')
    (norm_nonneg (fstColToEuclid Λ')) (abs_nonneg (Λ.1 0 0)))

lemma orthchro_mul_orthchro {Λ Λ' : lorentzGroup} (h : IsOrthochronous Λ)
    (h' : IsOrthochronous Λ') : IsOrthochronous (Λ * Λ') := by
  apply le_trans (zero_zero_mul_sub_row_col Λ Λ')
  have h1 := zero_zero_mul Λ Λ'
  rw [← IsOrthochronous_abs_zero_zero h, ← IsOrthochronous_abs_zero_zero h'] at h1
  refine le_trans
    (?_ : _ ≤ |Λ.1 0 0| * |Λ'.1 0 0| + (- |⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ|)) ?_
  · erw [add_le_add_iff_left]
    simp only [neg_mul, neg_neg, neg_le]
    exact schwartz_identity_fst_row_col Λ Λ'
  · rw [h1, add_le_add_iff_left]
    exact neg_abs_le ⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ

lemma not_orthchro_mul_not_orthchro {Λ Λ' : lorentzGroup} (h : ¬ IsOrthochronous Λ)
    (h' : ¬ IsOrthochronous Λ') : IsOrthochronous (Λ * Λ') := by
  apply le_trans (zero_zero_mul_sub_row_col Λ Λ')
  refine le_trans
    (?_ : _ ≤ |Λ.1 0 0| * |Λ'.1 0 0| + (- |⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ|)) ?_
  · erw [add_le_add_iff_left]
    simp only [neg_mul, neg_neg, neg_le]
    exact schwartz_identity_fst_row_col Λ Λ'
  · rw [zero_zero_mul Λ Λ', not_IsOrthochronous_abs_zero_zero h,
      not_IsOrthochronous_abs_zero_zero h']
    simp only [Fin.isValue, abs_neg, _root_.abs_abs, conj_trivial, mul_neg, neg_mul, neg_neg,
      add_le_add_iff_left]
    exact neg_abs_le ⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ

lemma orthchro_mul_not_orthchro {Λ Λ' : lorentzGroup} (h : IsOrthochronous Λ)
    (h' : ¬ IsOrthochronous Λ') : ¬ IsOrthochronous (Λ * Λ') := by
  rw [not_IsOrthochronous_iff]
  refine le_trans
    (?_ : _ ≤ - (|Λ.1 0 0| * |Λ'.1 0 0| + (- |⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ|))) ?_
  · rw [zero_zero_mul Λ Λ', ← IsOrthochronous_abs_zero_zero h,
      not_IsOrthochronous_abs_zero_zero h']
    simp only [Fin.isValue, mul_neg, _root_.abs_abs, abs_neg, neg_add_rev, neg_neg,
      le_add_neg_iff_add_le, neg_add_cancel_comm]
    exact le_abs_self ⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ
  · apply le_trans ?_ (neg_nonpos_of_nonneg (zero_zero_mul_sub_row_col Λ Λ'))
    simp only [Fin.isValue, neg_add_rev, neg_neg, neg_sub, add_neg_le_iff_le_add, sub_add_cancel]
    exact schwartz_identity_fst_row_col _ _

lemma not_orthchro_mul_orthchro {Λ Λ' : lorentzGroup} (h : ¬ IsOrthochronous Λ)
    (h' : IsOrthochronous Λ') : ¬ IsOrthochronous (Λ * Λ') := by
  rw [not_IsOrthochronous_iff]
  refine le_trans
    (?_ : _ ≤ - (|Λ.1 0 0| * |Λ'.1 0 0| + (- |⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ|))) ?_
  · rw [zero_zero_mul Λ Λ', ← IsOrthochronous_abs_zero_zero h',
      not_IsOrthochronous_abs_zero_zero h]
    simp only [Fin.isValue, neg_mul, PiLp.inner_apply, fstRowToEuclid, fstColToEuclid,
      RCLike.inner_apply, conj_trivial, abs_neg, _root_.abs_abs, neg_add_rev, neg_neg,
      le_add_neg_iff_add_le, neg_add_cancel_comm]
    exact le_abs_self ⟪fstRowToEuclid Λ, fstColToEuclid Λ'⟫_ℝ
  · apply le_trans ?_ (neg_nonpos_of_nonneg (zero_zero_mul_sub_row_col Λ Λ'))
    simp only [Fin.isValue, neg_add_rev, neg_neg, neg_sub, add_neg_le_iff_le_add, sub_add_cancel]
    exact schwartz_identity_fst_row_col _ _

/-- The homomorphism from `lorentzGroup` to `ℤ₂` whose kernal consists of precisely the
orthochronous elements. -/
@[simps!]
def orthochronousRep : lorentzGroup →* ℤ₂ where
  toFun Λ := if IsOrthochronous Λ then (Additive.toMul 0) else Additive.toMul (1 : ZMod 2)
  map_one' := by
    simp
  map_mul' := by
    intro Λ1 Λ2
    simp only [toMul_zero, mul_ite, mul_one, ite_mul, one_mul]
    cases' (em (IsOrthochronous Λ1)) with h h
      <;> cases' (em (IsOrthochronous Λ2)) with h' h'
    rw [if_pos (orthchro_mul_orthchro h h'), if_pos h, if_pos h']
    rw [if_neg (orthchro_mul_not_orthchro h h'), if_neg h', if_pos h]
    rw [if_neg (not_orthchro_mul_orthchro h h'), if_pos h', if_neg h]
    rw [if_pos (not_orthchro_mul_not_orthchro h h'), if_neg h', if_neg h]
    rfl

lemma IsOrthochronous_iff (Λ : lorentzGroup) :
    IsOrthochronous Λ ↔ orthochronousRep Λ = Additive.toMul 0 := by
  apply Iff.intro
  intro h
  erw [orthochronousRep_apply, if_pos h]
  simp only [toMul_zero]
  intro h
  by_cases h1 : IsOrthochronous Λ
  exact h1
  erw [orthochronousRep_apply, if_neg h1] at h
  contradiction



end Orthochronous

end lorentzGroup

open lorentzGroup in
/-- The restricted lorentz group consists of those elements of the `lorentzGroup` which are
proper and orthochronous. -/
def restrictedLorentzGroup : Subgroup (lorentzGroup) where
  carrier := {Λ | IsProper Λ ∧ IsOrthochronous Λ}
  mul_mem' {Λa Λb} := by
    intro ha hb
    apply And.intro
    rw [IsProper_iff, detRep.map_mul, (IsProper_iff Λa).mp ha.1, (IsProper_iff Λb).mp hb.1]
    simp only [toMul_zero, mul_one]
    rw [IsOrthochronous_iff, orthochronousRep.map_mul, (IsOrthochronous_iff Λa).mp ha.2,
      (IsOrthochronous_iff Λb).mp hb.2]
    simp
  one_mem' := by
    simp only [IsOrthochronous, Fin.isValue, Set.mem_setOf_eq, OneMemClass.coe_one, Units.val_one,
      one_apply_eq, zero_le_one, and_true]
    rw [IsProper_iff, detRep.map_one]
    simp
  inv_mem' {Λ} := by
    intro h
    apply And.intro
    rw [IsProper_iff, detRep.map_inv, (IsProper_iff Λ).mp h.1]
    simp only [toMul_zero, inv_one]
    rw [IsOrthochronous_iff, orthochronousRep.map_inv, (IsOrthochronous_iff Λ).mp h.2]
    simp

/-- The restricted lorentz group is a topological group. -/
instance : TopologicalGroup restrictedLorentzGroup :=
  Subgroup.instTopologicalGroupSubtypeMem restrictedLorentzGroup

end spaceTime

end
