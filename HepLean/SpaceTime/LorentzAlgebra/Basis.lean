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

namespace spaceTime

namespace lorentzAlgebra
open Matrix

/-- The matrices which form the basis of the Lorentz algebra. -/
@[simp]
def σMat (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ := fun ρ δ ↦
  η^[ρ]_[μ] * η_[ν]_[δ] - η_[μ]_[δ] * η^[ρ]_[ν]

lemma σMat_in_lorentzAlgebra (μ ν : Fin 4) : σMat μ ν ∈ lorentzAlgebra := by
  rw [mem_iff]
  funext ρ δ
  rw [Matrix.neg_mul, Matrix.neg_apply, η_mul, mul_η, transpose_apply]
  apply Eq.trans ?_ (by ring :
    - ((η^[ρ]_[μ] * η_[ρ]_[ρ]) * η_[ν]_[δ] - η_[μ]_[δ] * (η^[ρ]_[ν] *  η_[ρ]_[ρ])) =
    -(η_[ρ]_[ρ] * (η^[ρ]_[μ] * η_[ν]_[δ] - η_[μ]_[δ] * η^[ρ]_[ν])))
  apply Eq.trans (by ring : (η^[δ]_[μ] * η_[ν]_[ρ] - η_[μ]_[ρ] * η^[δ]_[ν]) * η_[δ]_[δ]
    = ((η^[δ]_[μ] * η_[δ]_[δ]) * η_[ν]_[ρ] - η_[μ]_[ρ] * (η^[δ]_[ν]  * η_[δ]_[δ])))
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
    η_[α]_[δ] • σ β γ + η_[α]_[γ] • σ δ β + η_[β]_[δ] • σ γ α + η_[β]_[γ] • σ α δ := by
  refine SetCoe.ext ?_
  change σMat α β * σ γ δ -  σ γ δ * σ α β = _
  funext a b
  simp only [σ_coe, sub_apply, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid,
    Submodule.coe_smul_of_tower, add_apply, smul_apply, σMat, smul_eq_mul]
  rw [σMat_mul, σMat_mul, η_symmetric α γ, η_symmetric α δ, η_symmetric β γ, η_symmetric β δ]
  ring


end lorentzAlgebra

end spaceTime
