/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.HiggsBoson.Basic
import Mathlib.RepresentationTheory.Basic
import HepLean.StandardModel.Basic
import HepLean.StandardModel.Representations
import Mathlib.Analysis.InnerProductSpace.Adjoint
/-!

# The action of the gauge group on the Higgs field

-/
/-! TODO: Currently this only contains the action of the global gauge group. Generalize. -/
noncomputable section

namespace StandardModel

namespace HiggsVec
open Manifold
open Matrix
open Complex
open ComplexConjugate

/-!

## The representation of the gauge group on the Higgs vector space

-/

/-- The Higgs representation as a homomorphism from the gauge group to unitary `2×2`-matrices. -/
@[simps!]
noncomputable def higgsRepUnitary : GaugeGroup →* unitaryGroup (Fin 2) ℂ where
  toFun g := repU1 g.2.2 * fundamentalSU2 g.2.1
  map_mul' := by
    intro ⟨_, a2, a3⟩ ⟨_, b2, b3⟩
    change repU1 (a3 * b3) * fundamentalSU2 (a2 * b2) = _
    rw [repU1.map_mul, fundamentalSU2.map_mul, mul_assoc, mul_assoc,
      ← mul_assoc (repU1 b3) _ _, repU1_fundamentalSU2_commute]
    repeat rw [mul_assoc]
  map_one' := by simp

/-- Takes in a `2×2`-matrix and returns a linear map of `higgsVec`. -/
noncomputable def matrixToLin : Matrix (Fin 2) (Fin 2) ℂ →* (HiggsVec →L[ℂ] HiggsVec) where
  toFun g := LinearMap.toContinuousLinearMap
    $ Matrix.toLin orthonormBasis.toBasis orthonormBasis.toBasis g
  map_mul' g h := ContinuousLinearMap.coe_inj.mp $
    Matrix.toLin_mul orthonormBasis.toBasis orthonormBasis.toBasis orthonormBasis.toBasis g h
  map_one' := ContinuousLinearMap.coe_inj.mp $ Matrix.toLin_one orthonormBasis.toBasis

/-- `matrixToLin` commutes with the `star` operation. -/
lemma matrixToLin_star (g : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixToLin (star g) = star (matrixToLin g) :=
  ContinuousLinearMap.coe_inj.mp $ Matrix.toLin_conjTranspose orthonormBasis orthonormBasis g

lemma matrixToLin_unitary (g : unitaryGroup (Fin 2) ℂ) :
    matrixToLin g ∈ unitary (HiggsVec →L[ℂ] HiggsVec) := by
  rw [@unitary.mem_iff, ← matrixToLin_star, ← matrixToLin.map_mul, ← matrixToLin.map_mul,
    mem_unitaryGroup_iff.mp g.prop, mem_unitaryGroup_iff'.mp g.prop, matrixToLin.map_one]
  simp

/-- The natural homomorphism from unitary `2×2` complex matrices to unitary transformations
of `higgsVec`. -/
noncomputable def unitaryToLin : unitaryGroup (Fin 2) ℂ →* unitary (HiggsVec →L[ℂ] HiggsVec) where
  toFun g := ⟨matrixToLin g, matrixToLin_unitary g⟩
  map_mul' g h := by simp
  map_one' := by simp

/-- The inclusion of unitary transformations on `higgsVec` into all linear transformations. -/
@[simps!]
def unitToLinear : unitary (HiggsVec →L[ℂ] HiggsVec) →* HiggsVec →ₗ[ℂ] HiggsVec :=
  DistribMulAction.toModuleEnd ℂ HiggsVec

/-- The representation of the gauge group acting on `higgsVec`. -/
@[simps!]
def rep : Representation ℂ GaugeGroup HiggsVec :=
   unitToLinear.comp (unitaryToLin.comp higgsRepUnitary)

lemma higgsRepUnitary_mul (g : GaugeGroup) (φ : HiggsVec) :
    (higgsRepUnitary g).1 *ᵥ φ = g.2.2 ^ 3 • (g.2.1.1 *ᵥ φ) := by
  simp [higgsRepUnitary_apply_coe, smul_mulVec_assoc]

lemma rep_apply (g : GaugeGroup) (φ : HiggsVec) : rep g φ = g.2.2 ^ 3 • (g.2.1.1 *ᵥ φ) :=
  higgsRepUnitary_mul g φ

/-!

# Gauge freedom

-/

/-- Given a Higgs vector, a rotation matrix which puts the first component of the
vector to zero, and the second component to a real -/
def rotateMatrix (φ : HiggsVec) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![φ 1 /‖φ‖ , - φ 0 /‖φ‖], ![conj (φ 0) / ‖φ‖ , conj (φ 1) / ‖φ‖] ]

lemma rotateMatrix_star (φ : HiggsVec) :
    star φ.rotateMatrix =
    ![![conj (φ 1) /‖φ‖ , φ 0 /‖φ‖], ![- conj (φ 0) / ‖φ‖ , φ 1 / ‖φ‖] ] := by
  simp_rw [star, rotateMatrix, conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conj_ofReal]

lemma rotateMatrix_det {φ : HiggsVec} (hφ : φ ≠ 0) : (rotateMatrix φ).det = 1 := by
  have h1 : (‖φ‖ : ℂ) ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
  field_simp [rotateMatrix, det_fin_two]
  rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
  simp [PiLp.inner_apply, Complex.inner, neg_mul, sub_neg_eq_add,
    Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm, add_comm]

lemma rotateMatrix_unitary {φ : HiggsVec} (hφ : φ ≠ 0) :
    (rotateMatrix φ) ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff', rotateMatrix_star, rotateMatrix]
  erw [mul_fin_two, one_fin_two]
  have : (‖φ‖ : ℂ) ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
  ext i j
  fin_cases i <;> fin_cases j <;> field_simp
  <;> rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
  · simp [PiLp.inner_apply, Complex.inner, neg_mul, sub_neg_eq_add,
      Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm, add_comm]
  · ring_nf
  · ring_nf
  · simp [PiLp.inner_apply, Complex.inner, neg_mul, sub_neg_eq_add,
      Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm]

lemma rotateMatrix_specialUnitary {φ : HiggsVec} (hφ : φ ≠ 0) :
    (rotateMatrix φ) ∈ specialUnitaryGroup (Fin 2) ℂ :=
  mem_specialUnitaryGroup_iff.mpr ⟨rotateMatrix_unitary hφ, rotateMatrix_det hφ⟩

/-- Given a Higgs vector, an element of the gauge group which puts the first component of the
vector to zero, and the second component to a real -/
def rotateGuageGroup {φ : HiggsVec} (hφ : φ ≠ 0) : GaugeGroup :=
    ⟨1, ⟨(rotateMatrix φ), rotateMatrix_specialUnitary hφ⟩, 1⟩

lemma rotateGuageGroup_apply {φ : HiggsVec} (hφ : φ ≠ 0) :
    rep (rotateGuageGroup hφ) φ = ![0, ofReal ‖φ‖] := by
  rw [rep_apply]
  simp only [rotateGuageGroup, rotateMatrix, one_pow, one_smul,
     Nat.succ_eq_add_one, Nat.reduceAdd, ofReal_eq_coe]
  ext i
  fin_cases i
  · simp only [mulVec, Fin.zero_eta, Fin.isValue, cons_val', empty_val', cons_val_fin_one,
    cons_val_zero, cons_dotProduct, vecHead, vecTail, Nat.succ_eq_add_one, Nat.reduceAdd,
    Function.comp_apply, Fin.succ_zero_eq_one, dotProduct_empty, add_zero]
    ring_nf
  · simp only [Fin.mk_one, Fin.isValue, cons_val_one, head_cons, mulVec, Fin.isValue,
    cons_val', empty_val', cons_val_fin_one, vecHead, cons_dotProduct, vecTail, Nat.succ_eq_add_one,
    Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, dotProduct_empty, add_zero]
    have : (‖φ‖ : ℂ) ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
    field_simp
    rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
    simp [PiLp.inner_apply, Complex.inner, neg_mul, sub_neg_eq_add,
      Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm]

theorem rotate_fst_zero_snd_real (φ : HiggsVec) :
    ∃ (g : GaugeGroup), rep g φ = ![0, ofReal ‖φ‖] := by
  by_cases h : φ = 0
  · use ⟨1, 1, 1⟩
    simp [h]
    ext i
    fin_cases i <;> rfl
  · use rotateGuageGroup h
    exact rotateGuageGroup_apply h

end HiggsVec

/-! TODO: Define the global gauge action on HiggsField. -/
/-! TODO: Prove `⟪φ1, φ2⟫_H` invariant under the global gauge action. (norm_map_of_mem_unitary) -/
/-! TODO: Prove invariance of potential under global gauge action. -/

end StandardModel
end
