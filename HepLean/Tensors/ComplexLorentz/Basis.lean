/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Elab
import HepLean.Tensors.ComplexLorentz.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import HepLean.Tensors.Tree.NodeIdentities.Basic
import HepLean.Tensors.Tree.NodeIdentities.PermProd
import HepLean.Tensors.Tree.NodeIdentities.PermContr
import HepLean.Tensors.Tree.NodeIdentities.ProdComm
import HepLean.Tensors.Tree.NodeIdentities.ContrSwap
import HepLean.Tensors.Tree.NodeIdentities.ContrContr
/-!

## Basis vectors associated with complex Lorentz tensors

Note that this file will be much improved once:
  https://github.com/leanprover-community/mathlib4/pull/11156
is merged.

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open TensorTree
open OverColor.Discrete
noncomputable section
namespace Fermion
namespace complexLorentzTensor

/-- Basis vectors for complex Lorentz tensors. -/
def basisVector {n : ℕ} (c : Fin n → complexLorentzTensor.C)
  (b : Π j, Fin (complexLorentzTensor.repDim (c j))) :
    complexLorentzTensor.F.obj (OverColor.mk c) :=
  PiTensorProduct.tprod ℂ (fun i => complexLorentzTensor.basis (c i) (b i))

/-!

## Useful expansions.

-/

/-- The expansion of the Lorentz covariant metric in terms of basis vectors. -/
lemma coMetric_basis_expand : {Lorentz.coMetric | μ ν}ᵀ.tensor =
    basisVector ![Color.down, Color.down] (fun _ => 0)
    - basisVector ![Color.down, Color.down] (fun _ => 1)
    - basisVector ![Color.down, Color.down] (fun _ => 2)
    - basisVector ![Color.down, Color.down] (fun _ => 3) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Functor.id_obj, Fin.isValue]
  erw [Lorentz.coMetric_apply_one, Lorentz.coMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    all_goals
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      change _ = Lorentz.complexCoBasisFin4 _
      simp only [Fin.isValue, Lorentz.complexCoBasisFin4, Basis.coe_reindex, Function.comp_apply]
      rfl

/-- The expansion of the Lorentz contrvariant metric in terms of basis vectors. -/
lemma contrMatrix_basis_expand : {Lorentz.contrMetric | μ ν}ᵀ.tensor =
    basisVector ![Color.up, Color.up] (fun _ => 0)
    - basisVector ![Color.up, Color.up] (fun _ => 1)
    - basisVector ![Color.up, Color.up] (fun _ => 2)
    - basisVector ![Color.up, Color.up] (fun _ => 3) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    Functor.id_obj, Fin.isValue]
  erw [Lorentz.contrMetric_apply_one, Lorentz.contrMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    all_goals
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      change _ = Lorentz.complexContrBasisFin4 _
      simp only [Fin.isValue, Lorentz.complexContrBasisFin4, Basis.coe_reindex, Function.comp_apply]
      rfl

end complexLorentzTensor
end Fermion
end
