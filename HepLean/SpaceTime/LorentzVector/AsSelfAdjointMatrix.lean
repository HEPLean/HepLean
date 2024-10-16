/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.MinkowskiMetric
import HepLean.SpaceTime.PauliMatrices.SelfAdjoint
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.Polyrith
/-!
# Lorentz vector as a self-adjoint matrix

There is a linear equivalence between the vector space of space-time points
and the vector space of 2×2-complex self-adjoint matrices.

In this file we define this linear equivalence in `toSelfAdjointMatrix`.

-/
/-! TODO: Generalize rep of Lorentz vector as a self-adjoint matrix to arbitrary dimension. -/
namespace SpaceTime

open Matrix
open MatrixGroups
open Complex
noncomputable section

/-- The linear equivalence between the vector-space `spaceTime` and self-adjoint
  `2×2`-complex matrices. -/
def toSelfAdjointMatrix : LorentzVector 3 ≃ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin 1 ⊕ Fin 3)).symm ≪≫ₗ PauliMatrix.σSAL.repr.symm

lemma toSelfAdjointMatrix_apply (x : LorentzVector 3) : toSelfAdjointMatrix x =
    x (Sum.inl 0) • ⟨PauliMatrix.σ0, PauliMatrix.σ0_selfAdjoint⟩
    - x (Sum.inr 0) • ⟨PauliMatrix.σ1, PauliMatrix.σ1_selfAdjoint⟩
    - x (Sum.inr 1) • ⟨PauliMatrix.σ2, PauliMatrix.σ2_selfAdjoint⟩
    - x (Sum.inr 2) • ⟨PauliMatrix.σ3, PauliMatrix.σ3_selfAdjoint⟩ := by
  simp only [toSelfAdjointMatrix, PauliMatrix.σSAL, LinearEquiv.trans_apply, Basis.repr_symm_apply,
    Basis.coe_mk, Fin.isValue]
  rw [Finsupp.linearCombination_apply_of_mem_supported ℝ (s := Finset.univ)]
  · change (∑ i : Fin 1 ⊕ Fin 3, x i • PauliMatrix.σSAL' i) = _
    simp only [PauliMatrix.σSAL', Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Finset.sum_singleton, Fin.sum_univ_three]
    apply Subtype.ext
    simp only [Fin.isValue, AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg,
      AddSubgroupClass.coe_sub]
    simp only [neg_add, add_assoc, sub_eq_add_neg]
  · simp_all only [Finset.coe_univ, Finsupp.supported_univ, Submodule.mem_top]

lemma toSelfAdjointMatrix_apply_coe (x : LorentzVector 3) : (toSelfAdjointMatrix x).1 =
    x (Sum.inl 0) • PauliMatrix.σ0
    - x (Sum.inr 0) • PauliMatrix.σ1
    - x (Sum.inr 1) • PauliMatrix.σ2
    - x (Sum.inr 2) • PauliMatrix.σ3 := by
  rw [toSelfAdjointMatrix_apply]
  simp only [Fin.isValue, AddSubgroupClass.coe_sub, selfAdjoint.val_smul]

lemma toSelfAdjointMatrix_stdBasis (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjointMatrix (LorentzVector.stdBasis i) = PauliMatrix.σSAL i := by
  rw [toSelfAdjointMatrix_apply]
  match i with
  | Sum.inl 0 =>
    simp only [LorentzVector.stdBasis, Fin.isValue]
    erw [Pi.basisFun_apply]
    simp [PauliMatrix.σSAL, PauliMatrix.σSAL']
  | Sum.inr 0 =>
    simp only [LorentzVector.stdBasis, Fin.isValue]
    erw [Pi.basisFun_apply]
    simp only [Fin.isValue, ne_eq, reduceCtorEq, not_false_eq_true, Pi.single_eq_of_ne, zero_smul,
      Pi.single_eq_same, one_smul, zero_sub, Sum.inr.injEq, one_ne_zero, sub_zero, Fin.reduceEq,
      PauliMatrix.σSAL, Basis.coe_mk, PauliMatrix.σSAL']
    refine Eq.symm (PauliMatrix.selfAdjoint_ext rfl rfl rfl rfl)
  | Sum.inr 1 =>
    simp only [LorentzVector.stdBasis, Fin.isValue]
    erw [Pi.basisFun_apply]
    simp only [Fin.isValue, ne_eq, reduceCtorEq, not_false_eq_true, Pi.single_eq_of_ne, zero_smul,
      Sum.inr.injEq, zero_ne_one, sub_self, Pi.single_eq_same, one_smul, zero_sub, Fin.reduceEq,
      sub_zero, PauliMatrix.σSAL, Basis.coe_mk, PauliMatrix.σSAL']
    refine Eq.symm (PauliMatrix.selfAdjoint_ext rfl rfl rfl rfl)
  | Sum.inr 2 =>
    simp only [LorentzVector.stdBasis, Fin.isValue]
    erw [Pi.basisFun_apply]
    simp only [Fin.isValue, ne_eq, reduceCtorEq, not_false_eq_true, Pi.single_eq_of_ne, zero_smul,
      Sum.inr.injEq, Fin.reduceEq, sub_self, Pi.single_eq_same, one_smul, zero_sub,
      PauliMatrix.σSAL, Basis.coe_mk, PauliMatrix.σSAL']
    refine Eq.symm (PauliMatrix.selfAdjoint_ext rfl rfl rfl rfl)

@[simp]
lemma toSelfAdjointMatrix_symm_basis (i : Fin 1 ⊕ Fin 3) :
    toSelfAdjointMatrix.symm (PauliMatrix.σSAL i) = (LorentzVector.stdBasis i) := by
  refine (LinearEquiv.symm_apply_eq toSelfAdjointMatrix).mpr ?_
  rw [toSelfAdjointMatrix_stdBasis]

open minkowskiMetric in
lemma det_eq_ηLin (x : LorentzVector 3) : det (toSelfAdjointMatrix x).1 = ⟪x, x⟫ₘ := by
  rw [toSelfAdjointMatrix_apply_coe]
  simp only [Fin.isValue, eq_time_minus_inner_prod, LorentzVector.time, LorentzVector.space,
    PiLp.inner_apply, Function.comp_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_three,
    ofReal_sub, ofReal_mul, ofReal_add]
  simp only [Fin.isValue, PauliMatrix.σ0, smul_of, smul_cons, real_smul, mul_one, smul_zero,
    smul_empty, PauliMatrix.σ1, of_sub_of, sub_cons, head_cons, sub_zero, tail_cons, zero_sub,
    sub_self, zero_empty, PauliMatrix.σ2, smul_neg, sub_neg_eq_add, PauliMatrix.σ3, det_fin_two_of]
  ring_nf
  simp only [Fin.isValue, I_sq, mul_neg, mul_one]
  ring

end
end SpaceTime
