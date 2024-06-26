/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzAlgebra.Basic
/-!
# Basis of the Lorentz Algebra

We define the standard basis of the Lorentz group.

-/

namespace SpaceTime

namespace lorentzAlgebra
open Matrix

/-- The matrices which form the basis of the Lorentz algebra. -/
@[simp]
def σMat (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ := fun ρ δ ↦
  η_[μ]_[δ] * η^[ρ]_[ν] - η^[ρ]_[μ] * η_[ν]_[δ]

lemma σMat_in_lorentzAlgebra (μ ν : Fin 4) : σMat μ ν ∈ lorentzAlgebra := by
  rw [mem_iff]
  funext ρ δ
  rw [Matrix.neg_mul, Matrix.neg_apply, η_mul, mul_η, transpose_apply]
  apply Eq.trans ?_ (by ring :
    ((η^[ρ]_[μ] * η_[ρ]_[ρ]) * η_[ν]_[δ] - η_[μ]_[δ] * (η^[ρ]_[ν] *  η_[ρ]_[ρ])) =
    -(η_[ρ]_[ρ] * (η_[μ]_[δ] * η^[ρ]_[ν] - η^[ρ]_[μ] * η_[ν]_[δ] )))
  apply Eq.trans (by ring : (η_[μ]_[ρ] * η^[δ]_[ν] - η^[δ]_[μ] * η_[ν]_[ρ]) * η_[δ]_[δ]
    = (- (η^[δ]_[μ] * η_[δ]_[δ]) * η_[ν]_[ρ] + η_[μ]_[ρ] * (η^[δ]_[ν]  * η_[δ]_[δ])))
  rw [η_mul_self, η_mul_self, η_mul_self, η_mul_self]
  ring

/-- Elements of the Lorentz algebra which form a basis thereof. -/
@[simps!]
def σ (μ ν : Fin 4) : lorentzAlgebra := ⟨σMat μ ν, σMat_in_lorentzAlgebra μ ν⟩

lemma σ_anti_symm (μ ν : Fin 4) : σ μ ν = - σ ν μ := by
  refine SetCoe.ext ?_
  funext ρ δ
  simp only [σ_coe, σMat, NegMemClass.coe_neg, neg_apply, neg_sub]
  ring

lemma σMat_mul (α β γ δ  a b: Fin 4) :
    (σMat α β * σMat γ δ) a b =
    η^[a]_[α] * (η_[δ]_[b] * η_[β]_[γ] - η_[γ]_[b] * η_[β]_[δ])
    - η^[a]_[β] * (η_[δ]_[b] * η_[α]_[γ]- η_[γ]_[b] * η_[α]_[δ]) := by
  rw [Matrix.mul_apply]
  simp only [σMat]
  trans (η^[a]_[α] * η_[δ]_[b]) * ∑ x, η^[x]_[γ] * η_[β]_[x]
    - (η^[a]_[α] * η_[γ]_[b]) * ∑ x, η^[x]_[δ] * η_[β]_[x]
    - (η^[a]_[β] *  η_[δ]_[b]) * ∑ x, η^[x]_[γ] * η_[α]_[x]
    + (η^[a]_[β] * η_[γ]_[b]) * ∑ x, η^[x]_[δ] * η_[α]_[x]
  repeat rw [Fin.sum_univ_four]
  ring
  rw [η_contract_self', η_contract_self', η_contract_self', η_contract_self']
  ring

lemma σ_comm (α β γ δ : Fin 4) :
    ⁅σ α β , σ γ δ⁆ =
    η_[α]_[δ] • σ γ β + η_[α]_[γ] • σ β δ + η_[β]_[δ] • σ α γ + η_[β]_[γ] • σ δ α := by
  refine SetCoe.ext ?_
  change σMat α β * σ γ δ -  σ γ δ * σ α β = _
  funext a b
  simp only [σ_coe, sub_apply, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid,
    Submodule.coe_smul_of_tower, Matrix.add_apply, Matrix.smul_apply, σMat, smul_eq_mul]
  rw [σMat_mul, σMat_mul, η_symmetric α γ, η_symmetric α δ, η_symmetric β γ, η_symmetric β δ]
  ring

lemma eq_span_σ (Λ : lorentzAlgebra) :
    Λ = Λ.1 0 1 • σ 0 1 + Λ.1 0 2 • σ 0 2 + Λ.1 0 3 • σ 0 3 +
      Λ.1 1 2 • σ 1 2 + Λ.1 1 3 • σ 1 3 + Λ.1 2 3 • σ 2 3 := by
  apply SetCoe.ext ?_
  funext a b
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, AddSubmonoid.coe_add,
     Submodule.coe_smul_of_tower, σ_coe,
     Matrix.add_apply, Matrix.smul_apply, σMat, ηUpDown, ne_eq, zero_ne_one, not_false_eq_true,
     one_apply_ne, η_explicit, of_apply, cons_val_zero,
     mul_zero, one_apply_eq, mul_one, sub_neg_eq_add,
     zero_add, smul_eq_mul, Fin.reduceEq, cons_val_one, vecHead, vecTail,
     Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, sub_self, add_zero, cons_val_two,
     cons_val_three, Fin.succ_one_eq_two, mul_neg, neg_zero, sub_zero]
  · exact diag_comp Λ 0
  · exact time_comps Λ 0
  · exact diag_comp Λ 1
  · exact time_comps Λ 1
  · exact space_comps Λ 1 0
  · exact diag_comp Λ 2
  · exact time_comps Λ 2
  · exact space_comps Λ 2 0
  · exact space_comps Λ 2 1
  · exact diag_comp Λ 3

/-- The coordinate map for the basis formed by the matrices `σ`. -/
@[simps!]
noncomputable def σCoordinateMap : lorentzAlgebra ≃ₗ[ℝ] Fin 6 →₀ ℝ where
  toFun Λ := Finsupp.equivFunOnFinite.invFun
    fun i => match i with
    | 0 => Λ.1 0 1
    | 1 => Λ.1 0 2
    | 2 => Λ.1 0 3
    | 3 => Λ.1 1 2
    | 4 => Λ.1 1 3
    | 5 => Λ.1 2 3
  map_add' S T := by
    ext i
    fin_cases i <;> rfl
  map_smul' c S := by
    ext i
    fin_cases i <;> rfl
  invFun c := c 0 • σ 0 1 + c 1 • σ 0 2 + c 2 • σ 0 3 +
      c 3 • σ 1 2 + c 4 • σ 1 3 + c 5 • σ 2 3
  left_inv Λ := by
    simp only [Fin.isValue, Equiv.invFun_as_coe, Finsupp.equivFunOnFinite_symm_apply_toFun]
    exact (eq_span_σ Λ).symm
  right_inv c := by
    ext i
    fin_cases i <;> simp only  [Fin.isValue, Set.Finite.toFinset_setOf, ne_eq, Finsupp.coe_mk,
    Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, AddSubmonoid.coe_add,
     Submodule.coe_toAddSubmonoid, Submodule.coe_smul_of_tower, σ_coe,
     Matrix.add_apply, Matrix.smul_apply, σMat, ηUpDown, ne_eq, zero_ne_one, not_false_eq_true,
     one_apply_ne, η_explicit, of_apply, cons_val', cons_val_zero, empty_val',
     cons_val_fin_one, vecCons_const, mul_zero, one_apply_eq, mul_one, sub_neg_eq_add,
     zero_add, smul_eq_mul, Fin.reduceEq, cons_val_one, vecHead, vecTail, Nat.succ_eq_add_one,
     Nat.reduceAdd, Function.comp_apply, Fin.succ_zero_eq_one, sub_self, add_zero, cons_val_two,
     cons_val_three, Fin.succ_one_eq_two, mul_neg, neg_zero, sub_zero, Finsupp.equivFunOnFinite]

/-- The basis formed by the matrices `σ`. -/
@[simps! repr_apply_support_val repr_apply_toFun]
noncomputable def σBasis : Basis (Fin 6) ℝ lorentzAlgebra where
  repr := σCoordinateMap

instance : Module.Finite ℝ lorentzAlgebra :=
   Module.Finite.of_basis σBasis

/-- The Lorentz algebra is 6-dimensional. -/
theorem finrank_eq_six : FiniteDimensional.finrank ℝ lorentzAlgebra = 6 := by
  have h  :=  Module.mk_finrank_eq_card_basis σBasis
  simp only [finrank_eq_rank, Cardinal.mk_fintype, Fintype.card_fin, Nat.cast_ofNat] at h
  exact FiniteDimensional.finrank_eq_of_rank_eq h


end lorentzAlgebra

end SpaceTime
