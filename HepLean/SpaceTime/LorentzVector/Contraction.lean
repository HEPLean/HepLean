/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Basic
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

variable {d : ℕ} (v : LorentzVector d)


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
    simp only [RingHom.id, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, id_eq]
    ring

def contrUpDown : LorentzVector d ⊗[ℝ] CovariantLorentzVector d →ₗ[ℝ] ℝ :=
  TensorProduct.lift contrUpDownBi

@[simp]
lemma contrUpDown_stdBasis_left (x : LorentzVector d) (i : Fin 1 ⊕ Fin d) :
    contrUpDown (x ⊗ₜ[ℝ] (CovariantLorentzVector.stdBasis i)) = x i := by
  simp only [contrUpDown, contrUpDownBi, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem i]
  simp only [CovariantLorentzVector.stdBasis]
  erw [Pi.basisFun_apply]
  simp only [LinearMap.stdBasis_same, mul_one]
  exact Finset.mem_univ i
  intro b _ hbi
  simp only [CovariantLorentzVector.stdBasis, mul_eq_zero]
  erw [Pi.basisFun_apply]
  simp only [LinearMap.stdBasis_apply', ite_eq_right_iff, one_ne_zero, imp_false]
  exact Or.inr hbi.symm

@[simp]
lemma contrUpDown_stdBasis_right (x : CovariantLorentzVector d) (i : Fin 1 ⊕ Fin d) :
    contrUpDown (e i ⊗ₜ[ℝ] x) = x i := by
  simp only [contrUpDown, contrUpDownBi, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single_of_mem i]
  erw [Pi.basisFun_apply]
  simp only [LinearMap.stdBasis_same, one_mul]
  exact Finset.mem_univ i
  intro b _ hbi
  simp only [CovariantLorentzVector.stdBasis, mul_eq_zero]
  erw [Pi.basisFun_apply]
  simp only [LinearMap.stdBasis_apply', ite_eq_right_iff, one_ne_zero, imp_false]
  exact Or.intro_left (x b = 0) (id (Ne.symm hbi))

def contrDownUp : CovariantLorentzVector d ⊗[ℝ] LorentzVector d →ₗ[ℝ] ℝ :=
  contrUpDown ∘ₗ (TensorProduct.comm ℝ _ _).toLinearMap


def unitUp : LorentzVector d ⊗[ℝ] CovariantLorentzVector d :=
  ∑ i, LorentzVector.stdBasis i ⊗ₜ[ℝ] CovariantLorentzVector.stdBasis i

lemma unitUp_lid (x : LorentzVector d) :
    TensorProduct.rid ℝ _
    (TensorProduct.map  (LinearEquiv.refl ℝ (_)).toLinearMap
    (contrUpDown ∘ₗ (TensorProduct.comm ℝ _ _).toLinearMap )
    ((TensorProduct.assoc ℝ _ _ _) (unitUp ⊗ₜ[ℝ] x )))  = x := by
  simp only  [LinearEquiv.refl_toLinearMap, unitUp]
  rw [sum_tmul]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, map_add, assoc_tmul, map_sum, map_tmul, LinearMap.id_coe, id_eq,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, comm_tmul,
    contrUpDown_stdBasis_left, rid_tmul, decomp_stdBasis']

def unitDown : CovariantLorentzVector d ⊗[ℝ] LorentzVector d :=
  ∑ i, CovariantLorentzVector.stdBasis i ⊗ₜ[ℝ] LorentzVector.stdBasis i

lemma unitDown_lid (x : CovariantLorentzVector d) :
    TensorProduct.rid ℝ _
    (TensorProduct.map  (LinearEquiv.refl ℝ (_)).toLinearMap
    (contrDownUp ∘ₗ (TensorProduct.comm ℝ _ _).toLinearMap )
    ((TensorProduct.assoc ℝ _ _ _) (unitDown ⊗ₜ[ℝ] x))) = x := by
  simp only [LinearEquiv.refl_toLinearMap, unitDown]
  rw [sum_tmul]
  simp only [contrDownUp, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton, map_add, assoc_tmul, map_sum, map_tmul, LinearMap.id_coe,
    id_eq, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, comm_tmul,
    contrUpDown_stdBasis_right, rid_tmul, CovariantLorentzVector.decomp_stdBasis']


end LorentzVector

namespace minkowskiMatrix
open LorentzVector
open scoped minkowskiMatrix
variable {d : ℕ}

def asProdLorentzVector : LorentzVector d ⊗[ℝ] LorentzVector d :=
  ∑ μ,  η μ μ  • (LorentzVector.stdBasis μ ⊗ₜ[ℝ] LorentzVector.stdBasis μ)

def asProdCovariantLorentzVector : CovariantLorentzVector d ⊗[ℝ] CovariantLorentzVector d :=
  ∑ μ, η μ μ • (CovariantLorentzVector.stdBasis μ ⊗ₜ[ℝ] CovariantLorentzVector.stdBasis μ)

@[simp]
lemma contrLeft_asProdLorentzVector (x : CovariantLorentzVector d) :
    contrDualLeftAux contrDownUp (x ⊗ₜ[ℝ] asProdLorentzVector) =
    ∑ μ, ((η μ μ * x μ) • LorentzVector.stdBasis μ) := by
  simp only [asProdLorentzVector]
  rw [tmul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [contrDualLeftAux, contrDownUp, LinearEquiv.refl_toLinearMap, tmul_smul, map_smul,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_symm_tmul, map_tmul,
    comm_tmul, contrUpDown_stdBasis_right, LinearMap.id_coe, id_eq, lid_tmul]
  exact smul_smul (η μ μ) (x μ) (e μ)

@[simp]
lemma contrLeft_asProdCovariantLorentzVector (x : LorentzVector d) :
    contrDualLeftAux contrUpDown (x ⊗ₜ[ℝ] asProdCovariantLorentzVector) =
    ∑ μ, ((η μ μ * x μ) • CovariantLorentzVector.stdBasis μ) := by
  simp only [asProdCovariantLorentzVector]
  rw [tmul_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  simp only [contrDualLeftAux, LinearEquiv.refl_toLinearMap, tmul_smul, LinearMapClass.map_smul,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_symm_tmul, map_tmul,
    contrUpDown_stdBasis_left, LinearMap.id_coe, id_eq, lid_tmul]
  exact smul_smul (η μ μ) (x μ) (CovariantLorentzVector.stdBasis μ)

@[simp]
lemma asProdLorentzVector_contr_asCovariantProdLorentzVector :
    (contrDualMidAux (contrUpDown) (asProdLorentzVector ⊗ₜ[ℝ] asProdCovariantLorentzVector))
    = @unitUp d := by
  simp only [contrDualMidAux, LinearEquiv.refl_toLinearMap, asProdLorentzVector, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [sum_tmul, map_sum, map_sum, unitUp]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [← tmul_smul, TensorProduct.assoc_tmul]
  simp only [map_tmul, LinearMap.id_coe, id_eq, contrLeft_asProdCovariantLorentzVector]
  rw [tmul_sum, Finset.sum_eq_single_of_mem μ]
  rw [tmul_smul]
  change (η μ μ * (η μ μ * e μ μ)) •  e μ ⊗ₜ[ℝ] CovariantLorentzVector.stdBasis μ = _
  rw [LorentzVector.stdBasis]
  erw [Pi.basisFun_apply]
  simp
  exact Finset.mem_univ μ
  intro ν _ hμν
  rw [tmul_smul]
  change  (η ν ν * (η μ μ * e μ ν)) • (e μ ⊗ₜ[ℝ] CovariantLorentzVector.stdBasis ν) = _
  rw [LorentzVector.stdBasis]
  erw [Pi.basisFun_apply]
  simp only [LinearMap.stdBasis_apply', mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    ite_eq_right_iff, smul_eq_zero, mul_eq_zero]
  exact fun a => False.elim (hμν (id (Eq.symm a)))

@[simp]
lemma asProdCovariantLorentzVector_contr_asProdLorentzVector :
    (contrDualMidAux (contrDownUp) (asProdCovariantLorentzVector ⊗ₜ[ℝ] asProdLorentzVector))
    = @unitDown d := by
  simp only [contrDualMidAux, LinearEquiv.refl_toLinearMap, asProdCovariantLorentzVector,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [sum_tmul, map_sum, map_sum, unitDown]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [smul_tmul,]
  rw [TensorProduct.assoc_tmul]
  simp only [tmul_smul, LinearMapClass.map_smul, map_tmul, LinearMap.id_coe, id_eq,
    contrLeft_asProdLorentzVector]
  rw [tmul_sum, Finset.sum_eq_single_of_mem μ]
  rw [tmul_smul, smul_smul]
  rw [LorentzVector.stdBasis]
  erw [Pi.basisFun_apply]
  simp
  exact Finset.mem_univ μ
  intro ν _ hμν
  rw [tmul_smul]
  rw [LorentzVector.stdBasis]
  erw [Pi.basisFun_apply]
  simp only [LinearMap.stdBasis_apply', mul_ite, mul_one, mul_zero, ite_smul, zero_smul,
    ite_eq_right_iff, smul_eq_zero, mul_eq_zero]
  exact fun a => False.elim (hμν (id (Eq.symm a)))

end minkowskiMatrix


end
