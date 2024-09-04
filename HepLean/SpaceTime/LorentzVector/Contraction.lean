/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.LorentzAction
import HepLean.SpaceTime.LorentzVector.Covariant
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Contractions of Lorentz vectors

We define the contraction between a covariant and contravariant Lorentz vector,
as well as properties thereof.

The structures in this file are used in `HepLean.SpaceTime.LorentzTensor.Real.Basic`
to define the contraction between indices of Lorentz tensors.

-/

noncomputable section

open TensorProduct

namespace LorentzVector

open Matrix
variable {d : ℕ} (v : LorentzVector d)

/-- The bi-linear map defining the contraction of a contravariant Lorentz vector
  and a covariant Lorentz vector. -/
def contrUpDownBi : LorentzVector d →ₗ[ℝ] CovariantLorentzVector d →ₗ[ℝ] ℝ where
  toFun v := {
    toFun := fun w => ∑ i, v i * w i,
    map_add' := by
      intro w1 w2
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => mul_add _ _ _)
    map_smul' := by
      intro r w
      simp only [RingHom.id_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [HSMul.hSMul, SMul.smul]
      ring}
  map_add' v1 v2 := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => add_mul _ _ _)
  map_smul' r v := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [HSMul.hSMul, SMul.smul]
    exact mul_assoc r (v i) (w i)

/-- The linear map defining the contraction of a contravariant Lorentz vector
  and a covariant Lorentz vector. -/
def contrUpDown : LorentzVector d ⊗[ℝ] CovariantLorentzVector d →ₗ[ℝ] ℝ :=
  TensorProduct.lift contrUpDownBi

lemma contrUpDown_tmul_eq_dotProduct {x : LorentzVector d} {y : CovariantLorentzVector d} :
    contrUpDown (x ⊗ₜ[ℝ] y) = x ⬝ᵥ y := by
  rfl

@[simp]
lemma contrUpDown_stdBasis_left (x : LorentzVector d) (i : Fin 1 ⊕ Fin d) :
    contrUpDown (x ⊗ₜ[ℝ] (CovariantLorentzVector.stdBasis i)) = x i := by
  simp only [contrUpDown, contrUpDownBi, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem i]
  · simp only [CovariantLorentzVector.stdBasis]
    erw [Pi.basisFun_apply]
    simp only [Pi.single_eq_same, mul_one]
  · exact Finset.mem_univ i
  · intro b _ hbi
    simp only [CovariantLorentzVector.stdBasis, mul_eq_zero]
    erw [Pi.basisFun_apply]
    simp only [Pi.single_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    apply Or.inr hbi

@[simp]
lemma contrUpDown_stdBasis_right (x : CovariantLorentzVector d) (i : Fin 1 ⊕ Fin d) :
    contrUpDown (e i ⊗ₜ[ℝ] x) = x i := by
  simp only [contrUpDown, contrUpDownBi, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem i]
  · erw [Pi.basisFun_apply]
    simp only [Pi.single_eq_same, one_mul]
  · exact Finset.mem_univ i
  · intro b _ hbi
    simp only [CovariantLorentzVector.stdBasis, mul_eq_zero]
    erw [Pi.basisFun_apply]
    simp only [Pi.single_apply, ite_eq_right_iff, one_ne_zero, imp_false]
    exact Or.intro_left (x b = 0) hbi

/-- The linear map defining the contraction of a covariant Lorentz vector
  and a contravariant Lorentz vector. -/
def contrDownUp : CovariantLorentzVector d ⊗[ℝ] LorentzVector d →ₗ[ℝ] ℝ :=
  contrUpDown ∘ₗ (TensorProduct.comm ℝ _ _).toLinearMap

lemma contrDownUp_tmul_eq_dotProduct {x : CovariantLorentzVector d} {y : LorentzVector d} :
    contrDownUp (x ⊗ₜ[ℝ] y) = x ⬝ᵥ y := by
  rw [dotProduct_comm x y]
  rfl

/-!

## The unit of the contraction

-/

/-- The unit of the contraction of contravariant Lorentz vector and a
  covariant Lorentz vector. -/
def unitUp : CovariantLorentzVector d ⊗[ℝ] LorentzVector d :=
  ∑ i, CovariantLorentzVector.stdBasis i ⊗ₜ[ℝ] LorentzVector.stdBasis i

lemma unitUp_rid (x : LorentzVector d) :
    TensorStructure.contrLeftAux contrUpDown (x ⊗ₜ[ℝ] unitUp) = x := by
  simp only [unitUp, LinearEquiv.refl_toLinearMap]
  rw [tmul_sum]
  simp only [TensorStructure.contrLeftAux, LinearEquiv.refl_toLinearMap, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton, map_add,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_symm_tmul, map_tmul,
    contrUpDown_stdBasis_left, LinearMap.id_coe, id_eq, lid_tmul, map_sum, decomp_stdBasis']

/-- The unit of the contraction of covariant Lorentz vector and a
  contravariant Lorentz vector. -/
def unitDown : LorentzVector d ⊗[ℝ] CovariantLorentzVector d :=
  ∑ i, LorentzVector.stdBasis i ⊗ₜ[ℝ] CovariantLorentzVector.stdBasis i

lemma unitDown_rid (x : CovariantLorentzVector d) :
    TensorStructure.contrLeftAux contrDownUp (x ⊗ₜ[ℝ] unitDown) = x := by
  simp only [unitDown, LinearEquiv.refl_toLinearMap]
  rw [tmul_sum]
  simp only [TensorStructure.contrLeftAux, contrDownUp, LinearEquiv.refl_toLinearMap,
    Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, map_add, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    assoc_symm_tmul, map_tmul, comm_tmul, contrUpDown_stdBasis_right, LinearMap.id_coe, id_eq,
    lid_tmul, map_sum, CovariantLorentzVector.decomp_stdBasis']

/-!

# Contractions and the Lorentz actions

-/
open Matrix

@[simp]
lemma contrUpDown_invariant_lorentzAction : @contrUpDown d ((LorentzVector.rep g) x ⊗ₜ[ℝ]
    (CovariantLorentzVector.rep g) y) = contrUpDown (x ⊗ₜ[ℝ] y) := by
  rw [contrUpDown_tmul_eq_dotProduct, contrUpDown_tmul_eq_dotProduct]
  simp only [rep_apply, CovariantLorentzVector.rep_apply]
  rw [Matrix.dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
  simp only [LorentzGroup.subtype_inv_mul, one_mulVec]

@[simp]
lemma contrDownUp_invariant_lorentzAction : @contrDownUp d ((CovariantLorentzVector.rep g) x ⊗ₜ[ℝ]
    (LorentzVector.rep g) y) = contrDownUp (x ⊗ₜ[ℝ] y) := by
  rw [contrDownUp_tmul_eq_dotProduct, contrDownUp_tmul_eq_dotProduct]
  rw [dotProduct_comm, dotProduct_comm x y]
  simp only [rep_apply, CovariantLorentzVector.rep_apply]
  rw [Matrix.dotProduct_mulVec, vecMul_transpose, mulVec_mulVec]
  simp only [LorentzGroup.subtype_inv_mul, one_mulVec]

end LorentzVector

namespace minkowskiMatrix
open LorentzVector
open TensorStructure
open scoped minkowskiMatrix
variable {d : ℕ}

/-- The metric tensor as an element of `LorentzVector d ⊗[ℝ] LorentzVector d`. -/
def asTenProd : LorentzVector d ⊗[ℝ] LorentzVector d :=
  ∑ μ, ∑ ν, η μ ν • (LorentzVector.stdBasis μ ⊗ₜ[ℝ] LorentzVector.stdBasis ν)

lemma asTenProd_diag :
    @asTenProd d = ∑ μ, η μ μ • (LorentzVector.stdBasis μ ⊗ₜ[ℝ] LorentzVector.stdBasis μ) := by
  simp only [asTenProd]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.sum_eq_single μ]
  · intro ν _ hμν
    rw [minkowskiMatrix.off_diag_zero hμν.symm]
    exact TensorProduct.zero_smul (e μ ⊗ₜ[ℝ] e ν)
  · intro a
    rename_i j
    exact False.elim (a j)

/-- The metric tensor as an element of `CovariantLorentzVector d ⊗[ℝ] CovariantLorentzVector d`. -/
def asCoTenProd : CovariantLorentzVector d ⊗[ℝ] CovariantLorentzVector d :=
  ∑ μ, ∑ ν, η μ ν • (CovariantLorentzVector.stdBasis μ ⊗ₜ[ℝ] CovariantLorentzVector.stdBasis ν)

lemma asCoTenProd_diag :
    @asCoTenProd d = ∑ μ, η μ μ • (CovariantLorentzVector.stdBasis μ ⊗ₜ[ℝ]
      CovariantLorentzVector.stdBasis μ) := by
  simp only [asCoTenProd]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Finset.sum_eq_single μ]
  · intro ν _ hμν
    rw [minkowskiMatrix.off_diag_zero hμν.symm]
    simp only [zero_smul]
  · intro a
    simp_all only

@[simp]
lemma contrLeft_asTenProd (x : CovariantLorentzVector d) :
    contrLeftAux contrDownUp (x ⊗ₜ[ℝ] asTenProd) =
    ∑ μ, ((η μ μ * x μ) • LorentzVector.stdBasis μ) := by
  simp only [asTenProd_diag]
  rw [tmul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [contrLeftAux, contrDownUp, LinearEquiv.refl_toLinearMap, tmul_smul, map_smul,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_symm_tmul, map_tmul,
    comm_tmul, contrUpDown_stdBasis_right, LinearMap.id_coe, id_eq, lid_tmul]
  exact smul_smul (η μ μ) (x μ) (e μ)

@[simp]
lemma contrLeft_asCoTenProd (x : LorentzVector d) :
    contrLeftAux contrUpDown (x ⊗ₜ[ℝ] asCoTenProd) =
    ∑ μ, ((η μ μ * x μ) • CovariantLorentzVector.stdBasis μ) := by
  simp only [asCoTenProd_diag]
  rw [tmul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [contrLeftAux, LinearEquiv.refl_toLinearMap, tmul_smul, LinearMapClass.map_smul,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_symm_tmul, map_tmul,
    contrUpDown_stdBasis_left, LinearMap.id_coe, id_eq, lid_tmul]
  exact smul_smul (η μ μ) (x μ) (CovariantLorentzVector.stdBasis μ)

@[simp]
lemma asTenProd_contr_asCoTenProd :
    (contrMidAux (contrUpDown) (asTenProd ⊗ₜ[ℝ] asCoTenProd))
    = TensorProduct.comm ℝ _ _ (@unitUp d) := by
  simp only [contrMidAux, LinearEquiv.refl_toLinearMap, asTenProd_diag, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [sum_tmul, map_sum, map_sum, unitUp]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, map_add, comm_tmul, map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [← tmul_smul, TensorProduct.assoc_tmul]
  simp only [map_tmul, LinearMap.id_coe, id_eq, contrLeft_asCoTenProd]
  rw [tmul_sum, Finset.sum_eq_single_of_mem μ, tmul_smul]
  · change (η μ μ * (η μ μ * e μ μ)) • e μ ⊗ₜ[ℝ] CovariantLorentzVector.stdBasis μ = _
    rw [LorentzVector.stdBasis]
    erw [Pi.basisFun_apply]
    simp only [Pi.single_eq_same, mul_one, η_apply_mul_η_apply_diag, one_smul]
  · exact Finset.mem_univ μ
  · intro ν _ hμν
    rw [tmul_smul]
    change (η ν ν * (η μ μ * e μ ν)) • (e μ ⊗ₜ[ℝ] CovariantLorentzVector.stdBasis ν) = _
    rw [LorentzVector.stdBasis]
    erw [Pi.basisFun_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
      ite_eq_right_iff, smul_eq_zero, mul_eq_zero]
    exact fun a => False.elim (hμν a)

@[simp]
lemma asCoTenProd_contr_asTenProd :
    (contrMidAux (contrDownUp) (asCoTenProd ⊗ₜ[ℝ] asTenProd))
    = TensorProduct.comm ℝ _ _ (@unitDown d) := by
  simp only [contrMidAux, LinearEquiv.refl_toLinearMap, asCoTenProd_diag,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [sum_tmul, map_sum, map_sum, unitDown]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, map_add, comm_tmul, map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [smul_tmul, TensorProduct.assoc_tmul]
  simp only [tmul_smul, LinearMapClass.map_smul, map_tmul, LinearMap.id_coe, id_eq,
    contrLeft_asTenProd]
  rw [tmul_sum, Finset.sum_eq_single_of_mem μ, tmul_smul, smul_smul, LorentzVector.stdBasis]
  · erw [Pi.basisFun_apply]
    simp only [Pi.single_eq_same, mul_one, η_apply_mul_η_apply_diag, one_smul]
  · exact Finset.mem_univ μ
  · intro ν _ hμν
    rw [tmul_smul]
    rw [LorentzVector.stdBasis]
    erw [Pi.basisFun_apply]
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
      ite_eq_right_iff, smul_eq_zero, mul_eq_zero]
    exact fun a => False.elim (hμν a)

lemma asTenProd_invariant (g : LorentzGroup d) :
    TensorProduct.map (LorentzVector.rep g) (LorentzVector.rep g) asTenProd = asTenProd := by
  simp only [asTenProd, map_sum, LinearMapClass.map_smul, map_tmul, rep_apply_stdBasis,
    Matrix.transpose_apply]
  trans ∑ μ : Fin 1 ⊕ Fin d, ∑ ν : Fin 1 ⊕ Fin d, ∑ φ : Fin 1 ⊕ Fin d,
      η μ ν • (g.1 φ μ • e φ) ⊗ₜ[ℝ] ∑ ρ : Fin 1 ⊕ Fin d, g.1 ρ ν • e ρ
  · refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
    rw [sum_tmul, Finset.smul_sum]
  trans ∑ μ : Fin 1 ⊕ Fin d, ∑ ν : Fin 1 ⊕ Fin d, ∑ φ : Fin 1 ⊕ Fin d, ∑ ρ : Fin 1 ⊕ Fin d,
      (η μ ν • (g.1 φ μ • e φ) ⊗ₜ[ℝ] (g.1 ρ ν • e ρ))
  · refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ =>
      Finset.sum_congr rfl (fun φ _ => ?_)))
    rw [tmul_sum, Finset.smul_sum]
  rw [Finset.sum_congr rfl (fun μ _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => Finset.sum_comm))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun φ _ => Finset.sum_comm)]
  trans ∑ φ : Fin 1 ⊕ Fin d, ∑ ρ : Fin 1 ⊕ Fin d, ∑ μ : Fin 1 ⊕ Fin d, ∑ ν : Fin 1 ⊕ Fin d,
      ((g.1 φ μ * η μ ν * g.1 ρ ν) • (e φ) ⊗ₜ[ℝ] (e ρ))
  · refine Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun ρ _ =>
    Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))))
    rw [smul_tmul, tmul_smul, tmul_smul, smul_smul, smul_smul]
    ring_nf
  rw [Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun ρ _ =>
    Finset.sum_congr rfl (fun μ _ => Finset.sum_smul.symm)))]
  rw [Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun ρ _ => Finset.sum_smul.symm))]
  trans ∑ φ : Fin 1 ⊕ Fin d, ∑ ρ : Fin 1 ⊕ Fin d,
    (((g.1 * minkowskiMatrix * g.1.transpose : Matrix _ _ _) φ ρ) • (e φ) ⊗ₜ[ℝ] (e ρ))
  · refine Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun ρ _ => ?_))
    apply congrFun
    apply congrArg
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Finset.sum_mul]
  simp

open CovariantLorentzVector in
lemma asCoTenProd_invariant (g : LorentzGroup d) :
    TensorProduct.map (CovariantLorentzVector.rep g) (CovariantLorentzVector.rep g)
      asCoTenProd = asCoTenProd := by
  simp only [asCoTenProd, map_sum, LinearMapClass.map_smul, map_tmul,
    CovariantLorentzVector.rep_apply_stdBasis, Matrix.transpose_apply]
  trans ∑ μ : Fin 1 ⊕ Fin d, ∑ ν : Fin 1 ⊕ Fin d, ∑ φ : Fin 1 ⊕ Fin d,
      η μ ν • (g⁻¹.1 μ φ • CovariantLorentzVector.stdBasis φ) ⊗ₜ[ℝ]
        ∑ ρ : Fin 1 ⊕ Fin d, g⁻¹.1 ν ρ • CovariantLorentzVector.stdBasis ρ
  · refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
    rw [sum_tmul, Finset.smul_sum]
  trans ∑ μ : Fin 1 ⊕ Fin d, ∑ ν : Fin 1 ⊕ Fin d, ∑ φ : Fin 1 ⊕ Fin d, ∑ ρ : Fin 1 ⊕ Fin d,
      (η μ ν • (g⁻¹.1 μ φ • CovariantLorentzVector.stdBasis φ) ⊗ₜ[ℝ]
      (g⁻¹.1 ν ρ • CovariantLorentzVector.stdBasis ρ))
  · refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ =>
      Finset.sum_congr rfl (fun φ _ => ?_)))
    rw [tmul_sum, Finset.smul_sum]
  rw [Finset.sum_congr rfl (fun μ _ => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => Finset.sum_comm))]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun φ _ => Finset.sum_comm)]
  trans ∑ φ : Fin 1 ⊕ Fin d, ∑ ρ : Fin 1 ⊕ Fin d, ∑ μ : Fin 1 ⊕ Fin d, ∑ ν : Fin 1 ⊕ Fin d,
      ((g⁻¹.1 μ φ * η μ ν * g⁻¹.1 ν ρ) • (CovariantLorentzVector.stdBasis φ) ⊗ₜ[ℝ]
      (CovariantLorentzVector.stdBasis ρ))
  · refine Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun ρ _ =>
    Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))))
    rw [smul_tmul, tmul_smul, tmul_smul, smul_smul, smul_smul]
    ring_nf
  rw [Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun ρ _ =>
    Finset.sum_congr rfl (fun μ _ => Finset.sum_smul.symm)))]
  rw [Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun ρ _ => Finset.sum_smul.symm))]
  trans ∑ φ : Fin 1 ⊕ Fin d, ∑ ρ : Fin 1 ⊕ Fin d,
    (((g⁻¹.1.transpose * minkowskiMatrix * g⁻¹.1 : Matrix _ _ _) φ ρ) •
    (CovariantLorentzVector.stdBasis φ) ⊗ₜ[ℝ] (CovariantLorentzVector.stdBasis ρ))
  · refine Finset.sum_congr rfl (fun φ _ => Finset.sum_congr rfl (fun ρ _ => ?_))
    apply congrFun
    apply congrArg
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Finset.sum_mul]
  rw [LorentzGroup.transpose_mul_minkowskiMatrix_mul_self]

end minkowskiMatrix

end
