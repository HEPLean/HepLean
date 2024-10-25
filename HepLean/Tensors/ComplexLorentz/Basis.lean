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
open Fermion
noncomputable section
namespace complexLorentzTensor

/-- Basis vectors for complex Lorentz tensors. -/
def basisVector {n : ℕ} (c : Fin n → complexLorentzTensor.C)
    (b : Π j, Fin (complexLorentzTensor.repDim (c j))) :
    complexLorentzTensor.F.obj (OverColor.mk c) :=
  PiTensorProduct.tprod ℂ (fun i => complexLorentzTensor.basis (c i) (b i))

lemma perm_basisVector_cast {n m : ℕ} {c : Fin n → complexLorentzTensor.C}
    {c1 : Fin m → complexLorentzTensor.C}
    (σ : OverColor.mk c ⟶ OverColor.mk c1) (i : Fin m) :
    complexLorentzTensor.repDim (c ((OverColor.Hom.toEquiv σ).symm i)) =
    complexLorentzTensor.repDim (c1 i) := by
  have h1 := OverColor.Hom.toEquiv_symm_apply σ i
  simp only [Functor.const_obj_obj, OverColor.mk_hom] at h1
  rw [h1]

/-! TODO: Generalize `basis_eq_FDiscrete`. -/
lemma basis_eq_FDiscrete {n : ℕ} (c : Fin n → complexLorentzTensor.C)
    (b : Π j, Fin (complexLorentzTensor.repDim (c j))) (i : Fin n)
    (h : { as := c i } = { as := c1 }) :
    (complexLorentzTensor.FDiscrete.map (eqToHom h)).hom
    (complexLorentzTensor.basis (c i) (b i)) =
    (complexLorentzTensor.basis c1 (Fin.cast (by simp_all) (b i))) := by
  have h' : c i = c1 := by
    simp_all only [Discrete.mk.injEq]
  subst h'
  rfl

lemma perm_basisVector {n m : ℕ} {c : Fin n → complexLorentzTensor.C}
    {c1 : Fin m → complexLorentzTensor.C} (σ : OverColor.mk c ⟶ OverColor.mk c1)
    (b : Π j, Fin (complexLorentzTensor.repDim (c j))) :
    (perm σ (tensorNode (basisVector c b))).tensor =
    (basisVector c1 (fun i => Fin.cast (perm_basisVector_cast σ i)
    (b ((OverColor.Hom.toEquiv σ).symm i)))) := by
  rw [perm_tensor]
  simp only [TensorSpecies.F_def, tensorNode_tensor]
  rw [basisVector, basisVector]
  erw [OverColor.lift.map_tprod]
  apply congrArg
  funext i
  simp only [OverColor.mk_hom, OverColor.lift.discreteFunctorMapEqIso, Functor.mapIso_hom,
    eqToIso.hom, Functor.mapIso_inv, eqToIso.inv, LinearEquiv.ofLinear_apply]
  rw [basis_eq_FDiscrete]

lemma perm_basisVector_tree {n m : ℕ} {c : Fin n → complexLorentzTensor.C}
    {c1 : Fin m → complexLorentzTensor.C} (σ : OverColor.mk c ⟶ OverColor.mk c1)
    (b : Π j, Fin (complexLorentzTensor.repDim (c j))) :
    (perm σ (tensorNode (basisVector c b))).tensor =
    (tensorNode (basisVector c1 (fun i => Fin.cast (perm_basisVector_cast σ i)
    (b ((OverColor.Hom.toEquiv σ).symm i))))).tensor := by
  exact perm_basisVector _ _

/-- The scalar determining if contracting two basis vectors together gives zero or not. -/
def contrBasisVectorMul {n : ℕ} {c : Fin n.succ.succ → complexLorentzTensor.C}
    (i : Fin n.succ.succ) (j : Fin n.succ)
    (b : Π k, Fin (complexLorentzTensor.repDim (c k))) : ℂ :=
  (if (b i).val = (b (i.succAbove j)).val then (1 : ℂ) else 0)

lemma contrBasisVectorMul_neg {n : ℕ} {c : Fin n.succ.succ → complexLorentzTensor.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {b : Π k, Fin (complexLorentzTensor.repDim (c k))}
    (h : ¬ (b i).val = (b (i.succAbove j)).val) :
    contrBasisVectorMul i j b = 0 := by
  rw [contrBasisVectorMul]
  simp only [ite_eq_else, one_ne_zero, imp_false]
  exact h

lemma contrBasisVectorMul_pos {n : ℕ} {c : Fin n.succ.succ → complexLorentzTensor.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {b : Π k, Fin (complexLorentzTensor.repDim (c k))}
    (h : (b i).val = (b (i.succAbove j)).val) :
    contrBasisVectorMul i j b = 1 := by
  rw [contrBasisVectorMul]
  simp only [ite_eq_then, zero_ne_one, imp_false, Decidable.not_not]
  exact h

lemma contr_basisVector {n : ℕ} {c : Fin n.succ.succ → complexLorentzTensor.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {h : c (i.succAbove j) = complexLorentzTensor.τ (c i)}
    (b : Π k, Fin (complexLorentzTensor.repDim (c k))) :
    (contr i j h (tensorNode (basisVector c b))).tensor = (contrBasisVectorMul i j b) •
    basisVector (c ∘ Fin.succAbove i ∘ Fin.succAbove j)
    (fun k => b (i.succAbove (j.succAbove k))) := by
  rw [contr_tensor]
  simp only [Nat.succ_eq_add_one, tensorNode_tensor]
  rw [basisVector]
  erw [TensorSpecies.contrMap_tprod]
  congr 1
  rw [basis_eq_FDiscrete]
  simp only [Monoidal.tensorUnit_obj, Action.instMonoidalCategory_tensorUnit_V,
    Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Functor.comp_obj, Discrete.functor_obj_eq_as,
    Function.comp_apply]
  erw [basis_contr]
  rfl

lemma contr_basisVector_tree {n : ℕ} {c : Fin n.succ.succ → complexLorentzTensor.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {h : c (i.succAbove j) = complexLorentzTensor.τ (c i)}
    (b : Π k, Fin (complexLorentzTensor.repDim (c k))) :
    (contr i j h (tensorNode (basisVector c b))).tensor =
    (smul (contrBasisVectorMul i j b) (tensorNode
    (basisVector (c ∘ Fin.succAbove i ∘ Fin.succAbove j)
    (fun k => b (i.succAbove (j.succAbove k)))))).tensor := by
  exact contr_basisVector _

lemma contr_basisVector_tree_pos {n : ℕ} {c : Fin n.succ.succ → complexLorentzTensor.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {h : c (i.succAbove j) = complexLorentzTensor.τ (c i)}
    (b : Π k, Fin (complexLorentzTensor.repDim (c k)))
    (hn : (b i).val = (b (i.succAbove j)).val := by decide) :
    (contr i j h (tensorNode (basisVector c b))).tensor =
    ((tensorNode (basisVector (c ∘ Fin.succAbove i ∘ Fin.succAbove j)
    (fun k => b (i.succAbove (j.succAbove k)))))).tensor := by
  rw [contr_basisVector_tree, contrBasisVectorMul]
  rw [if_pos hn]
  simp [smul_tensor]

lemma contr_basisVector_tree_neg {n : ℕ} {c : Fin n.succ.succ → complexLorentzTensor.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {h : c (i.succAbove j) = complexLorentzTensor.τ (c i)}
    (b : Π k, Fin (complexLorentzTensor.repDim (c k)))
    (hn : ¬ (b i).val = (b (i.succAbove j)).val := by decide) :
    (contr i j h (tensorNode (basisVector c b))).tensor =
    (tensorNode 0).tensor := by
  rw [contr_basisVector_tree, contrBasisVectorMul]
  rw [if_neg hn]
  simp only [Nat.succ_eq_add_one, smul_tensor, tensorNode_tensor, _root_.zero_smul]

/-- Equivalence of Fin types appearing in the product of two basis vectors. -/
def prodBasisVecEquiv {n m : ℕ} {c : Fin n → complexLorentzTensor.C}
    {c1 : Fin m → complexLorentzTensor.C} (i : Fin n ⊕ Fin m) :
    Sum.elim (fun i => Fin (complexLorentzTensor.repDim (c i))) (fun i =>
      Fin (complexLorentzTensor.repDim (c1 i)))
    i ≃ Fin (complexLorentzTensor.repDim ((Sum.elim c c1 i))) :=
  match i with
  | Sum.inl _ => Equiv.refl _
  | Sum.inr _ => Equiv.refl _

lemma prod_basisVector {n m : ℕ} {c : Fin n → complexLorentzTensor.C}
    {c1 : Fin m → complexLorentzTensor.C}
    (b : Π k, Fin (complexLorentzTensor.repDim (c k)))
    (b1 : Π k, Fin (complexLorentzTensor.repDim (c1 k))) :
    (prod (tensorNode (basisVector c b)) (tensorNode (basisVector c1 b1))).tensor =
    basisVector (Sum.elim c c1 ∘ finSumFinEquiv.symm) (fun i =>
    prodBasisVecEquiv (finSumFinEquiv.symm i)
    ((HepLean.PiTensorProduct.elimPureTensor b b1) (finSumFinEquiv.symm i))) := by
  rw [prod_tensor, basisVector, basisVector]
  simp only [TensorSpecies.F_def, Functor.id_obj, OverColor.mk_hom,
    Action.instMonoidalCategory_tensorObj_V, Equivalence.symm_inverse,
    Action.functorCategoryEquivalence_functor, Action.FunctorCategoryEquivalence.functor_obj_obj,
    tensorNode_tensor]
  have h1 := OverColor.lift.μ_tmul_tprod_mk complexLorentzTensor.FDiscrete
    (fun i => (complexLorentzTensor.basis (c i)) (b i))
    (fun i => (complexLorentzTensor.basis (c1 i)) (b1 i))
  erw [h1, OverColor.lift.map_tprod]
  apply congrArg
  funext i
  obtain ⟨k, hk⟩ := finSumFinEquiv.surjective i
  subst hk
  simp only [Functor.id_obj, OverColor.mk_hom, Function.comp_apply,
    OverColor.lift.discreteFunctorMapEqIso, eqToIso_refl, Functor.mapIso_refl, Iso.refl_hom,
    Action.id_hom, Iso.refl_inv, LinearEquiv.ofLinear_apply]
  erw [← (Equiv.apply_eq_iff_eq_symm_apply finSumFinEquiv).mp rfl]
  match k with
  | Sum.inl k => rfl
  | Sum.inr k => rfl

lemma prod_basisVector_tree {n m : ℕ} {c : Fin n → complexLorentzTensor.C}
    {c1 : Fin m → complexLorentzTensor.C}
    (b : Π k, Fin (complexLorentzTensor.repDim (c k)))
    (b1 : Π k, Fin (complexLorentzTensor.repDim (c1 k))) :
    (prod (tensorNode (basisVector c b)) (tensorNode (basisVector c1 b1))).tensor =
    (tensorNode (basisVector (Sum.elim c c1 ∘ finSumFinEquiv.symm) (fun i =>
    prodBasisVecEquiv (finSumFinEquiv.symm i)
    ((HepLean.PiTensorProduct.elimPureTensor b b1) (finSumFinEquiv.symm i))))).tensor := by
  exact prod_basisVector _ _

lemma eval_basisVector {n : ℕ} {c : Fin n.succ → complexLorentzTensor.C}
    {i : Fin n.succ} (j : Fin (complexLorentzTensor.repDim (c i)))
    (b : Π k, Fin (complexLorentzTensor.repDim (c k))) :
    (eval i j (tensorNode (basisVector c b))).tensor = (if j = b i then (1 : ℂ) else 0) •
    basisVector (c ∘ Fin.succAbove i) (fun k => b (i.succAbove k)) := by
  rw [eval_tensor, basisVector, basisVector]
  simp only [Nat.succ_eq_add_one, Functor.id_obj, OverColor.mk_hom, tensorNode_tensor,
    Function.comp_apply, one_smul, _root_.zero_smul]
  erw [TensorSpecies.evalMap_tprod]
  congr 1
  have h1 : Fin.ofNat' ↑j (@Fin.size_pos' (complexLorentzTensor.repDim (c i)) _) = j := by
    simpa [Fin.ext_iff] using Nat.mod_eq_of_lt j.prop
  rw [Basis.repr_self, Finsupp.single_apply, h1]
  exact ite_congr (Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a))
    (congrFun rfl) (congrFun rfl)

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

lemma coMetric_basis_expand_tree : {Lorentz.coMetric | μ ν}ᵀ.tensor =
    (TensorTree.add (tensorNode (basisVector ![Color.down, Color.down] (fun _ => 0))) <|
    TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.down, Color.down] (fun _ => 1)))) <|
    TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.down, Color.down] (fun _ => 2)))) <|
    (smul (-1) (tensorNode (basisVector ![Color.down, Color.down] (fun _ => 3))))).tensor :=
  coMetric_basis_expand

/-- The expansion of the Lorentz contrvariant metric in terms of basis vectors. -/
lemma contrMatrix_basis_expand : {Lorentz.contrMetric | μ ν}ᵀ.tensor =
    basisVector ![Color.up, Color.up] (fun _ => 0)
    - basisVector ![Color.up, Color.up] (fun _ => 1)
    - basisVector ![Color.up, Color.up] (fun _ => 2)
    - basisVector ![Color.up, Color.up] (fun _ => 3) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V]
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

lemma contrMatrix_basis_expand_tree : {Lorentz.contrMetric | μ ν}ᵀ.tensor =
    (TensorTree.add (tensorNode (basisVector ![Color.up, Color.up] (fun _ => 0))) <|
    TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.up, Color.up] (fun _ => 1)))) <|
    TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.up, Color.up] (fun _ => 2)))) <|
    (smul (-1) (tensorNode (basisVector ![Color.up, Color.up] (fun _ => 3))))).tensor :=
  contrMatrix_basis_expand

lemma leftMetric_expand : {Fermion.leftMetric | α β}ᵀ.tensor =
    - basisVector ![Color.upL, Color.upL] (fun | 0 => 0 | 1 => 1)
    + basisVector ![Color.upL, Color.upL] (fun | 0 => 1 | 1 => 0) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [Fermion.leftMetric_apply_one, Fermion.leftMetricVal_expand_tmul]
  simp only [Fin.isValue, map_add, map_neg]
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    · rfl
    · rfl

lemma leftMetric_expand_tree : {Fermion.leftMetric | α β}ᵀ.tensor =
    (TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.upL, Color.upL]
    (fun | 0 => 0 | 1 => 1)))) <|
    (tensorNode (basisVector ![Color.upL, Color.upL] (fun | 0 => 1 | 1 => 0)))).tensor :=
  leftMetric_expand

lemma altLeftMetric_expand : {Fermion.altLeftMetric | α β}ᵀ.tensor =
    basisVector ![Color.downL, Color.downL] (fun | 0 => 0 | 1 => 1)
    - basisVector ![Color.downL, Color.downL] (fun | 0 => 1 | 1 => 0) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [Fermion.altLeftMetric_apply_one, Fermion.altLeftMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    · rfl
    · rfl

lemma altLeftMetric_expand_tree : {Fermion.altLeftMetric | α β}ᵀ.tensor =
    (TensorTree.add (tensorNode (basisVector ![Color.downL, Color.downL]
    (fun | 0 => 0 | 1 => 1))) <|
    (smul (-1) (tensorNode (basisVector ![Color.downL, Color.downL]
    (fun | 0 => 1 | 1 => 0))))).tensor :=
  altLeftMetric_expand

lemma rightMetric_expand : {Fermion.rightMetric | α β}ᵀ.tensor =
    - basisVector ![Color.upR, Color.upR] (fun | 0 => 0 | 1 => 1)
    + basisVector ![Color.upR, Color.upR] (fun | 0 => 1 | 1 => 0) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [Fermion.rightMetric_apply_one, Fermion.rightMetricVal_expand_tmul]
  simp only [Fin.isValue, map_add, map_neg]
  congr 1
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    · rfl
    · rfl

lemma rightMetric_expand_tree : {Fermion.rightMetric | α β}ᵀ.tensor =
    (TensorTree.add (smul (-1) (tensorNode (basisVector ![Color.upR, Color.upR]
    (fun | 0 => 0 | 1 => 1)))) <|
    (tensorNode (basisVector ![Color.upR, Color.upR] (fun | 0 => 1 | 1 => 0)))).tensor :=
  rightMetric_expand

lemma altRightMetric_expand : {Fermion.altRightMetric | α β}ᵀ.tensor =
    basisVector ![Color.downR, Color.downR] (fun | 0 => 0 | 1 => 1)
    - basisVector ![Color.downR, Color.downR] (fun | 0 => 1 | 1 => 0) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constTwoNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [Fermion.altRightMetric_apply_one, Fermion.altRightMetricVal_expand_tmul]
  simp only [Fin.isValue, map_sub]
  congr 1
  all_goals
    erw [pairIsoSep_tmul, basisVector]
    apply congrArg
    funext i
    fin_cases i
    · rfl
    · rfl

lemma altRightMetric_expand_tree : {Fermion.altRightMetric | α β}ᵀ.tensor =
    (TensorTree.add (tensorNode (basisVector
    ![Color.downR, Color.downR] (fun | 0 => 0 | 1 => 1))) <|
    (smul (-1) (tensorNode (basisVector ![Color.downR, Color.downR]
    (fun | 0 => 1 | 1 => 0))))).tensor :=
  altRightMetric_expand

/-- The expansion of the Pauli matrices `σ^μ^a^{dot a}` in terms of basis vectors. -/
lemma pauliMatrix_basis_expand : {PauliMatrix.asConsTensor | μ α β}ᵀ.tensor =
    basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 1 | 2 => 1)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 1 | 2 => 0)
    - I • basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + I • basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 1 | 2 => 0)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 0 | 2 => 0)
    - basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, constThreeNode_tensor,
    Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V, Fin.isValue]
  erw [PauliMatrix.asConsTensor_apply_one, PauliMatrix.asTensor_expand]
  simp only [Equivalence.symm_inverse, Action.functorCategoryEquivalence_functor,
    Action.FunctorCategoryEquivalence.functor_obj_obj, Action.instMonoidalCategory_tensorObj_V,
    Fin.isValue, map_sub, map_add, _root_.map_smul]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  all_goals
    erw [tripleIsoSep_tmul, basisVector]
    apply congrArg
    try apply congrArg
    funext i
    match i with
    | (0 : Fin 3) =>
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, OverColor.mk_hom,
        cons_val_zero, Fin.cases_zero]
      change _ = Lorentz.complexContrBasisFin4 _
      simp only [Fin.isValue, Lorentz.complexContrBasisFin4, Basis.coe_reindex, Function.comp_apply]
      rfl
    | (1 : Fin 3) => rfl
    | (2 : Fin 3) => rfl

lemma pauliMatrix_basis_expand_tree : {PauliMatrix.asConsTensor | μ α β}ᵀ.tensor =
    (TensorTree.add (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 0 | 2 => 0))) <|
    TensorTree.add (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 1 | 2 => 1))) <|
    TensorTree.add (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 0 | 2 => 1))) <|
    TensorTree.add (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 1 | 2 => 0))) <|
    TensorTree.add (smul (-I) (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 0 | 2 => 1)))) <|
    TensorTree.add (smul I (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 1 | 2 => 0)))) <|
    TensorTree.add (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 0 | 2 => 0))) <|
    (smul (-1) (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR]
        (fun | 0 => 3 | 1 => 1 | 2 => 1))))).tensor := by
  rw [pauliMatrix_basis_expand]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, add_tensor, tensorNode_tensor,
    smul_tensor, neg_smul, one_smul]
  rfl

end complexLorentzTensor
end
