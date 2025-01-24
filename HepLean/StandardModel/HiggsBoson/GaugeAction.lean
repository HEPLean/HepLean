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
TODO "Currently this only contains the action of the global gauge group. Generalize
  to include the full action of the gauge group."
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
noncomputable def higgsRepUnitary : GaugeGroupI →* unitaryGroup (Fin 2) ℂ where
  toFun g := repU1 g.2.2 * fundamentalSU2 g.2.1
  map_mul' := by
    intro ⟨_, a2, a3⟩ ⟨_, b2, b3⟩
    change repU1 (a3 * b3) * fundamentalSU2 (a2 * b2) = _
    rw [repU1.map_mul, fundamentalSU2.map_mul, mul_assoc, mul_assoc,
      ← mul_assoc (repU1 b3) _ _, repU1_fundamentalSU2_commute]
    repeat rw [mul_assoc]
  map_one' := by simp

/-- Using the orthonormal basis of `HiggsVec`, turns a `2×2`-matrix intoa a linear map
  of `HiggsVec`. -/
noncomputable def matrixToLin : Matrix (Fin 2) (Fin 2) ℂ →* (HiggsVec →L[ℂ] HiggsVec) where
  toFun g := LinearMap.toContinuousLinearMap
    $ Matrix.toLin orthonormBasis.toBasis orthonormBasis.toBasis g
  map_mul' g h := ContinuousLinearMap.coe_inj.mp $
    Matrix.toLin_mul orthonormBasis.toBasis orthonormBasis.toBasis orthonormBasis.toBasis g h
  map_one' := ContinuousLinearMap.coe_inj.mp $ Matrix.toLin_one orthonormBasis.toBasis

/-- The map `matrixToLin` commutes with the `star` operation. -/
lemma matrixToLin_star (g : Matrix (Fin 2) (Fin 2) ℂ) :
    matrixToLin (star g) = star (matrixToLin g) :=
  ContinuousLinearMap.coe_inj.mp $ Matrix.toLin_conjTranspose orthonormBasis orthonormBasis g

/-- If `g` is a member of the `2 × 2` unitary group, then as a linear map from
  `HiggsVec →L[ℂ] HiggsVec` formed by the orthonormal basis on `HiggsVec`, it is unitary. -/
lemma matrixToLin_unitary (g : unitaryGroup (Fin 2) ℂ) :
    matrixToLin g ∈ unitary (HiggsVec →L[ℂ] HiggsVec) := by
  rw [@unitary.mem_iff, ← matrixToLin_star, ← matrixToLin.map_mul, ← matrixToLin.map_mul,
    mem_unitaryGroup_iff.mp g.prop, mem_unitaryGroup_iff'.mp g.prop, matrixToLin.map_one]
  exact Prod.mk_eq_one.mp rfl

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
def rep : Representation ℂ GaugeGroupI HiggsVec :=
  unitToLinear.comp (unitaryToLin.comp higgsRepUnitary)

lemma higgsRepUnitary_mul (g : GaugeGroupI) (φ : HiggsVec) :
    (higgsRepUnitary g).1 *ᵥ φ = g.2.2 ^ 3 • (g.2.1.1 *ᵥ φ) := by
  simp [higgsRepUnitary_apply_coe, smul_mulVec_assoc]

/-- The application of gauge group on a Higgs vector can be decomposed in
  to an smul with the `U(1)-factor` and a multiplication by the `SU(2)`-factor. -/
lemma rep_apply (g : GaugeGroupI) (φ : HiggsVec) : rep g φ = g.2.2 ^ 3 • (g.2.1.1 *ᵥ φ) :=
  higgsRepUnitary_mul g φ

/-!

# Gauge freedom

-/

/-- Given a Higgs vector, a rotation matrix which puts the first component of the
  svector to zero, and the second component to a real -/
def rotateMatrix (φ : HiggsVec) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![φ 1 /‖φ‖, - φ 0 /‖φ‖], ![conj (φ 0) / ‖φ‖, conj (φ 1) / ‖φ‖]]

/-- An expansion of the conjugate of the `rotateMatrix` for a higgs vector. -/
lemma rotateMatrix_star (φ : HiggsVec) :
    star φ.rotateMatrix =
    ![![conj (φ 1) /‖φ‖, φ 0 /‖φ‖], ![- conj (φ 0) / ‖φ‖, φ 1 / ‖φ‖]] := by
  simp_rw [star, rotateMatrix, conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conj_ofReal]

/-- The determinant of the `rotateMatrix` for a non-zero Higgs vector is `1`. -/
lemma rotateMatrix_det {φ : HiggsVec} (hφ : φ ≠ 0) : (rotateMatrix φ).det = 1 := by
  have h1 : (‖φ‖ : ℂ) ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
  field_simp [rotateMatrix, det_fin_two]
  rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
  simp [PiLp.inner_apply, Complex.inner, neg_mul, sub_neg_eq_add,
    Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm, add_comm]

/-- The `rotateMatrix` for a non-zero Higgs vector is untitary. -/
lemma rotateMatrix_unitary {φ : HiggsVec} (hφ : φ ≠ 0) :
    (rotateMatrix φ) ∈ unitaryGroup (Fin 2) ℂ := by
  rw [mem_unitaryGroup_iff', rotateMatrix_star, rotateMatrix]
  erw [mul_fin_two, one_fin_two]
  have : (‖φ‖ : ℂ) ≠ 0 := ofReal_inj.mp.mt (norm_ne_zero_iff.mpr hφ)
  ext i j
  fin_cases i <;> fin_cases j
  · field_simp
    rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
    simp [PiLp.inner_apply, Complex.inner, neg_mul, sub_neg_eq_add,
      Fin.sum_univ_two, ofReal_add, ofReal_mul, mul_conj, mul_comm, add_comm]
  · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, of_apply, cons_val', cons_val_one, head_cons,
    empty_val', cons_val_fin_one, cons_val_zero]
    ring_nf
  · simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, of_apply, cons_val', cons_val_zero,
    empty_val', cons_val_fin_one, cons_val_one, head_fin_const]
    ring_nf
  · field_simp
    rw [← ofReal_mul, ← sq, ← @real_inner_self_eq_norm_sq]
    simp only [Fin.isValue, mul_comm, mul_conj, PiLp.inner_apply, Complex.inner, ofReal_re,
    Fin.sum_univ_two, ofReal_add]

/-- The `rotateMatrix` for a non-zero Higgs vector is special unitary. -/
lemma rotateMatrix_specialUnitary {φ : HiggsVec} (hφ : φ ≠ 0) :
    (rotateMatrix φ) ∈ specialUnitaryGroup (Fin 2) ℂ :=
  mem_specialUnitaryGroup_iff.mpr ⟨rotateMatrix_unitary hφ, rotateMatrix_det hφ⟩

/-- Given a Higgs vector, an element of the gauge group which puts the first component of the
vector to zero, and the second component to a real number. -/
def rotateGuageGroup {φ : HiggsVec} (hφ : φ ≠ 0) : GaugeGroupI :=
    ⟨1, ⟨(rotateMatrix φ), rotateMatrix_specialUnitary hφ⟩, 1⟩

/-- Acting on a non-zero Higgs vector with its rotation matrix gives a vector which is
  zero in the first componenent and a positive real in the second component. -/
lemma rotateGuageGroup_apply {φ : HiggsVec} (hφ : φ ≠ 0) :
    rep (rotateGuageGroup hφ) φ = ![0, Complex.ofRealHom ‖φ‖] := by
  rw [rep_apply]
  simp only [rotateGuageGroup, rotateMatrix, one_pow, one_smul,
    Nat.succ_eq_add_one, Nat.reduceAdd, ofRealHom_eq_coe]
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

/-- For every Higgs vector there exists an element of the gauge group which rotates that
  Higgs vector to have `0` in the first component and be a non-negative real in the second
  componenet. -/
theorem rotate_fst_zero_snd_real (φ : HiggsVec) :
    ∃ (g : GaugeGroupI), rep g φ = ![0, Complex.ofReal ‖φ‖] := by
  by_cases h : φ = 0
  · use ⟨1, 1, 1⟩
    simp only [Prod.mk_one_one, _root_.map_one, h, map_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
      norm_zero]
    ext i
    fin_cases i <;> rfl
  · use rotateGuageGroup h
    exact rotateGuageGroup_apply h

/-- For every Higgs vector there exists an element of the gauge group which rotates that
  Higgs vector to have `0` in the second component and be a non-negative real in the first
  componenet. -/
theorem rotate_fst_real_snd_zero (φ : HiggsVec) :
    ∃ (g : GaugeGroupI), rep g φ = ![Complex.ofReal ‖φ‖, 0] := by
  obtain ⟨g, h⟩ := rotate_fst_zero_snd_real φ
  let P : GaugeGroupI := ⟨1, ⟨!![0, 1; -1, 0], by
    rw [mem_specialUnitaryGroup_iff]
    apply And.intro
    · rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j
        <;> simp
    · simp [det_fin_two]⟩, 1⟩
  use P * g
  rw [rep.map_mul]
  change rep P (rep g φ) = _
  rw [h, rep_apply]
  simp only [one_pow, Nat.succ_eq_add_one, Nat.reduceAdd, ofRealHom_eq_coe, mulVec_cons, zero_smul,
    coe_smul, mulVec_empty, add_zero, zero_add, one_smul]
  funext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Pi.smul_apply, Function.comp_apply, cons_val_zero,
      tail_cons, head_cons, real_smul, mul_one]
  · simp only [Fin.mk_one, Fin.isValue, Pi.smul_apply, Function.comp_apply, cons_val_one, head_cons,
      tail_cons, smul_zero]

informal_lemma guage_orbit where
  math :≈ "There exists a `g` in ``GaugeGroupI such that `rep g φ = φ'` if and only if
    ‖φ‖ = ‖φ'‖."
  deps :≈ [``rotate_fst_zero_snd_real]

informal_lemma stability_group_single where
  physics :≈ "The Higgs boson breaks electroweak symmetry down to the electromagnetic force."
  math :≈ "The stablity group of the action of `rep` on `![0, Complex.ofReal ‖φ‖]`,
    for non-zero `‖φ‖` is the `SU(3) x U(1)` subgroup of
    `gaugeGroup := SU(3) x SU(2) x U(1)` with the embedding given by
    `(g, e^{i θ}) ↦ (g, diag (e ^ {3 * i θ}, e ^ {- 3 * i θ}), e^{i θ})`."
  deps :≈ [``StandardModel.HiggsVec, ``StandardModel.HiggsVec.rep]

informal_lemma stability_group where
  math :≈ "The subgroup of `gaugeGroup := SU(3) x SU(2) x U(1)` which preserves every `HiggsVec`
    by the action of ``StandardModel.HiggsVec.rep is given by `SU(3) x ℤ₆` where ℤ₆
    is the subgroup of `SU(2) x U(1)` with elements `(α^(-3) * I₂, α)` where
    α is a sixth root of unity."
  deps :≈ [``HiggsVec, ``rep]

end HiggsVec

TODO "Define the global gauge action on HiggsField."
TODO "Prove `⟪φ1, φ2⟫_H` invariant under the global gauge action. (norm_map_of_mem_unitary)"
TODO "Prove invariance of potential under global gauge action."

namespace HiggsField

/-!

## Gauge transformations acting on Higgs fields.

-/

informal_definition gaugeAction where
  math :≈ "The action of ``gaugeTransformI on ``HiggsField acting pointwise through
    ``HiggsVec.rep."
  deps :≈ [``HiggsVec.rep, ``gaugeTransformI]

informal_lemma guage_orbit where
  math :≈ "There exists a `g` in ``gaugeTransformI such that `gaugeAction g φ = φ'` if and only if
    φ(x)^† φ(x) = φ'(x)^† φ'(x)."
  deps :≈ [``gaugeAction]

informal_lemma gauge_orbit_surject where
  math :≈ "For every smooth map f from ``SpaceTime to ℝ such that `f` is positive semidefinite,
    there exists a Higgs field φ such that `f = φ^† φ`."
  deps :≈ [``HiggsField, ``SpaceTime]

end HiggsField

end StandardModel
end
