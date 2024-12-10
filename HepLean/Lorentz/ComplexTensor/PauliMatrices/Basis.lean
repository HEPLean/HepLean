/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.ComplexTensor.PauliMatrices.Basic
import HepLean.Lorentz.ComplexTensor.Basis
/-!

## Pauli matrices and the basis of complex Lorentz tensors

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

namespace complexLorentzTensor
open Fermion

/-!

## Expanding pauliContr in a basis.

-/
/-- The expansion of the Pauli matrices `σ^μ^a^{dot a}` in terms of basis vectors. -/
lemma pauliContr_in_basis : {pauliContr | μ α β}ᵀ.tensor =
    basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 0 | 1 => 1 | 2 => 1)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 1 | 1 => 1 | 2 => 0)
    - I • basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + I • basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 2 | 1 => 1 | 2 => 0)
    + basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 0 | 2 => 0)
    - basisVector ![Color.up, Color.upL, Color.upR] (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  rw [tensorNode_pauliContr]
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

lemma pauliContr_basis_expand_tree : {pauliContr | μ α β}ᵀ.tensor =
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
  rw [pauliContr_in_basis]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, add_tensor, tensorNode_tensor,
    smul_tensor, neg_smul, one_smul]
  rfl

/-- The map to colors one gets when contracting with Pauli matrices on the right. -/
abbrev pauliMatrixContrMap {n : ℕ} (c : Fin n → complexLorentzTensor.C) :=
  (Sum.elim c ![Color.up, Color.upL, Color.upR] ∘ ⇑finSumFinEquiv.symm)

lemma prod_pauliMatrix_basis_tree_expand {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (t : TensorTree complexLorentzTensor c) :
    (TensorTree.prod t (tensorNode pauliContr)).tensor = (((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 0 | 1 => 0 | 2 => 0)))).add
    (((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 0 | 1 => 1 | 2 => 1)))).add
    (((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 1 | 1 => 0 | 2 => 1)))).add
    (((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 1 | 1 => 1 | 2 => 0)))).add
    ((TensorTree.smul (-I) ((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 2 | 1 => 0 | 2 => 1))))).add
    ((TensorTree.smul I ((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 2 | 1 => 1 | 2 => 0))))).add
    ((t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 3 | 1 => 0 | 2 => 0))).add
    (TensorTree.smul (-1) (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR]
        fun | 0 => 3 | 1 => 1 | 2 => 1))))))))))).tensor := by
  rw [prod_tensor_eq_snd <| pauliContr_basis_expand_tree]
  rw [prod_add _ _ _]
  rw [add_tensor_eq_snd <| prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| prod_add _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| prod_add _ _ _]
  /- Moving smuls. -/
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_fst <| prod_smul _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| prod_smul _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd<| add_tensor_eq_snd
    <| add_tensor_eq_snd <| prod_smul _ _ _]

lemma contr_pauliMatrix_basis_tree_expand {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (t : TensorTree complexLorentzTensor c) (i : Fin (n + 3)) (j : Fin (n +2))
    (h : (pauliMatrixContrMap c) (i.succAbove j) =
      complexLorentzTensor.τ ((pauliMatrixContrMap c) i)) :
    (contr i j h (TensorTree.prod t (tensorNode pauliContr))).tensor =
    ((contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 0 | 1 => 0 | 2 => 0)))).add
    ((contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 0 | 1 => 1 | 2 => 1)))).add
    ((contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 1 | 1 => 0 | 2 => 1)))).add
    ((contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 1 | 1 => 1 | 2 => 0)))).add
    ((TensorTree.smul (-I) (contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 2 | 1 => 0 | 2 => 1))))).add
    ((TensorTree.smul I (contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 2 | 1 => 1 | 2 => 0))))).add
    ((contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR] fun | 0 => 3 | 1 => 0 | 2 => 0)))).add
    (TensorTree.smul (-1) (contr i j h (t.prod (tensorNode
      (basisVector ![Color.up, Color.upL, Color.upR]
        fun | 0 => 3 | 1 => 1 | 2 => 1)))))))))))).tensor := by
  rw [contr_tensor_eq <| prod_pauliMatrix_basis_tree_expand _]
  /- Moving contr over add. -/
  rw [contr_add]
  rw [add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  /- Moving contr over smul. -/
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    contr_smul _ _]

lemma basis_contr_pauliMatrix_basis_tree_expand' {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (i : Fin (n + 3)) (j : Fin (n +2))
    (h : (pauliMatrixContrMap c) (i.succAbove j) = complexLorentzTensor.τ
      ((pauliMatrixContrMap c) i))
    (b : Π k, Fin (complexLorentzTensor.repDim (c k))) :
    let c' := Sum.elim c ![Color.up, Color.upL, Color.upR] ∘ finSumFinEquiv.symm
    let b' (i1 i2 i3 : Fin 4) := fun i => prodBasisVecEquiv (finSumFinEquiv.symm i)
      ((HepLean.PiTensorProduct.elimPureTensor b (fun | 0 => i1 | 1 => i2 | 2 => i3))
      (finSumFinEquiv.symm i))
    (contr i j h (TensorTree.prod (tensorNode (basisVector c b))
      (tensorNode pauliContr))).tensor = ((contr i j h ((tensorNode
    (basisVector c' (b' 0 0 0))))).add
    ((contr i j h ((tensorNode (basisVector c' (b' 0 1 1))))).add
    ((contr i j h ((tensorNode (basisVector c' (b' 1 0 1))))).add
    ((contr i j h ((tensorNode (basisVector c' (b' 1 1 0))))).add
    ((TensorTree.smul (-I) (contr i j h ((tensorNode (basisVector c' (b' 2 0 1)))))).add
    ((TensorTree.smul I (contr i j h ((tensorNode (basisVector c' (b' 2 1 0)))))).add
    ((contr i j h ((tensorNode (basisVector c' (b' 3 0 0))))).add
    (TensorTree.smul (-1) (contr i j h ((tensorNode
      (basisVector c' (b' 3 1 1))))))))))))).tensor := by
  rw [contr_pauliMatrix_basis_tree_expand]
  /- Product of basis vectors . -/
  rw [add_tensor_eq_fst <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_tensor_eq
    <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst
    <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_fst <| smul_tensor_eq <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| contr_tensor_eq
      <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_tensor_eq
    <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| smul_tensor_eq
    <| contr_tensor_eq <| prod_basisVector_tree _ _]
  rfl

/-- The map to color which appears when contracting a basis vector with
  puali matrices. -/
def pauliMatrixBasisProdMap
    {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (b : Π k, Fin (complexLorentzTensor.repDim (c k))) (i1 i2 i3 : Fin 4) :
    (i : Fin (n + (Nat.succ 0).succ.succ)) →
      Fin (complexLorentzTensor.repDim (Sum.elim c ![Color.up, Color.upL, Color.upR]
          (finSumFinEquiv.symm i))) := fun i => prodBasisVecEquiv (finSumFinEquiv.symm i)
      ((HepLean.PiTensorProduct.elimPureTensor b (fun | (0 : Fin 3) => i1 | 1 => i2 | 2 => i3))
      (finSumFinEquiv.symm i))

/-- The new basis vectors which appear when contracting pauli matrices with
  basis vectors. -/
def basisVectorContrPauli {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (i : Fin (n + 3)) (j : Fin (n +2))
    (b : Π k, Fin (complexLorentzTensor.repDim (c k)))
    (i1 i2 i3 : Fin 4) :=
  let c' := (Sum.elim c ![Color.up, Color.upL, Color.upR] ∘ finSumFinEquiv.symm)
      ∘ Fin.succAbove i ∘ Fin.succAbove j
  let b' (i1 i2 i3 : Fin 4) := fun k => (pauliMatrixBasisProdMap b i1 i2 i3)
    (i.succAbove (j.succAbove k))
  basisVector c' (b' i1 i2 i3)

lemma basis_contr_pauliMatrix_basis_tree_expand {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (i : Fin (n + 3)) (j : Fin (n +2))
    (h : (pauliMatrixContrMap c) (i.succAbove j) = complexLorentzTensor.τ
      ((pauliMatrixContrMap c) i))
    (b : Π k, Fin (complexLorentzTensor.repDim (c k))) :
    let c' := (Sum.elim c ![Color.up, Color.upL, Color.upR] ∘ finSumFinEquiv.symm)
      ∘ Fin.succAbove i ∘ Fin.succAbove j
    let b' (i1 i2 i3 : Fin 4) := fun k => (pauliMatrixBasisProdMap b i1 i2 i3)
      (i.succAbove (j.succAbove k))
    (contr i j h (TensorTree.prod (tensorNode (basisVector c b))
    (tensorNode pauliContr))).tensor =
    (((TensorTree.smul (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 0 0 0))
      (tensorNode (basisVector c' (b' 0 0 0))))).add
    (((TensorTree.smul (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 0 1 1))
      (tensorNode (basisVector c' (b' 0 1 1))))).add
    (((TensorTree.smul (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 1 0 1))
      (tensorNode (basisVector c' (b' 1 0 1))))).add
    (((TensorTree.smul (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 1 1 0))
      (tensorNode (basisVector c' (b' 1 1 0))))).add
    ((TensorTree.smul (-I) ((TensorTree.smul
      (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 2 0 1))
      (tensorNode (basisVector c' (b' 2 0 1)))))).add
    ((TensorTree.smul I ((TensorTree.smul
      (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 2 1 0))
      (tensorNode (basisVector c' (b' 2 1 0)))))).add
    (((TensorTree.smul (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 3 0 0))
      (tensorNode (basisVector c' (b' 3 0 0))))).add
    (TensorTree.smul (-1) ((TensorTree.smul
      (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 3 1 1)) (tensorNode
      (basisVector c' (b' 3 1 1))))))))))))).tensor := by
  rw [basis_contr_pauliMatrix_basis_tree_expand']
  /- Contracting basis vectors. -/
  rw [add_tensor_eq_fst <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst
    <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_fst <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq
    <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_basisVector_tree _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    smul_tensor_eq <| contr_basisVector_tree _]
  rfl

lemma basis_contr_pauliMatrix_basis_tree_expand_tensor {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (i : Fin (n + 3)) (j : Fin (n +2))
    (h : (pauliMatrixContrMap c) (i.succAbove j) = complexLorentzTensor.τ
      ((pauliMatrixContrMap c) i))
    (b : Π k, Fin (complexLorentzTensor.repDim (c k))) :
    (contr i j h (TensorTree.prod (tensorNode (basisVector c b))
    (tensorNode pauliContr))).tensor =
    (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 0 0 0)) •
      (basisVectorContrPauli i j b 0 0 0)
    + (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 0 1 1)) •
      (basisVectorContrPauli i j b 0 1 1)
    + (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 1 0 1)) •
      (basisVectorContrPauli i j b 1 0 1)
    + (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 1 1 0)) •
      (basisVectorContrPauli i j b 1 1 0)
    + (-I) • (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 2 0 1)) •
      (basisVectorContrPauli i j b 2 0 1)
    + I • (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 2 1 0)) •
      (basisVectorContrPauli i j b 2 1 0)
    + (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 3 0 0)) •
      (basisVectorContrPauli i j b 3 0 0)
    + (-1 : ℂ) • (contrBasisVectorMul i j (pauliMatrixBasisProdMap b 3 1 1)) •
      (basisVectorContrPauli i j b 3 1 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, cons_val_one, head_cons, Fin.val_zero,
    Nat.cast_zero, cons_val_two, Fin.val_one, Nat.cast_one, add_tensor, smul_tensor,
    tensorNode_tensor, neg_smul, one_smul, Int.reduceNeg]
  simp_all only [Function.comp_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  rfl

/-!

## Expanding pauliCo in a basis.

-/

/-- The map to color one gets when lowering the indices of pauli matrices. -/
def pauliCoMap := ((Sum.elim ![Color.down, Color.down] ![Color.up, Color.upL, Color.upR] ∘
  ⇑finSumFinEquiv.symm) ∘ Fin.succAbove 1 ∘ Fin.succAbove 1)

lemma pauliMatrix_contr_down_0 :
    (contr 1 1 rfl (((tensorNode (basisVector ![Color.down, Color.down] fun _ => 0)).prod
    (tensorNode pauliContr)))).tensor
    = basisVector pauliCoMap (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + basisVector pauliCoMap (fun | 0 => 0 | 1 => 1 | 2 => 1) := by
  conv =>
    lhs
    rw [basis_contr_pauliMatrix_basis_tree_expand_tensor]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; lhs; lhs
    rw [contrBasisVectorMul_pos (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_pos (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; rhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; rhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; rhs; lhs;
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; rhs; rhs; lhs;
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs
    simp only [_root_.zero_smul, one_smul, _root_.smul_zero, _root_.add_zero, _root_.zero_add]
  congr 1
  · rw [basisVectorContrPauli]
    congr 1
    funext k
    fin_cases k <;> rfl
  · rw [basisVectorContrPauli]
    congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_down_1 :
    {(basisVector ![Color.down, Color.down] fun _ => 1) | ν μ ⊗
      pauliContr | μ α β}ᵀ.tensor
    = basisVector pauliCoMap (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + basisVector pauliCoMap (fun | 0 => 1 | 1 => 1 | 2 => 0) := by
  conv =>
    lhs
    rw [basis_contr_pauliMatrix_basis_tree_expand_tensor]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; lhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_pos (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_pos (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; rhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; rhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; rhs; lhs;
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; rhs; rhs; lhs;
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs
    simp only [_root_.zero_smul, one_smul, _root_.smul_zero, _root_.add_zero, _root_.zero_add]
  congr 1
  · rw [basisVectorContrPauli]
    congr 1
    funext k
    fin_cases k <;> rfl
  · rw [basisVectorContrPauli]
    congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_down_2 :
    {(basisVector ![Color.down, Color.down] fun _ => 2) | μ ν ⊗
      pauliContr | ν α β}ᵀ.tensor
    = (- I) • basisVector pauliCoMap (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + (I) • basisVector pauliCoMap (fun | 0 => 2 | 1 => 1 | 2 => 0) := by
  conv =>
    lhs
    rw [basis_contr_pauliMatrix_basis_tree_expand_tensor]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; lhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; rhs; rhs; lhs
    rw [contrBasisVectorMul_pos (by decide)]
  conv =>
    lhs; lhs; lhs; rhs; rhs; lhs
    rw [contrBasisVectorMul_pos (by decide)]
  conv =>
    lhs; lhs; rhs; lhs;
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; rhs; rhs; lhs;
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs
    simp only [_root_.zero_smul, one_smul, _root_.smul_zero, _root_.add_zero, _root_.zero_add]
  rw [basisVectorContrPauli, basisVectorContrPauli]
  congr 3
  · decide
  · decide

lemma pauliMatrix_contr_down_3 :
    {(basisVector ![Color.down, Color.down] fun _ => 3) | μ ν ⊗
    pauliContr | ν α β}ᵀ.tensor
    = basisVector pauliCoMap (fun | 0 => 3 | 1 => 0 | 2 => 0)
    + (- 1 : ℂ) • basisVector pauliCoMap (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  conv =>
    lhs
    rw [basis_contr_pauliMatrix_basis_tree_expand_tensor]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; lhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; lhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; lhs; rhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; lhs; rhs; rhs; lhs
    rw [contrBasisVectorMul_neg (by decide)]
  conv =>
    lhs; lhs; rhs; lhs;
    rw [contrBasisVectorMul_pos (by decide)]
  conv =>
    lhs; rhs; rhs; lhs;
    rw [contrBasisVectorMul_pos (by decide)]
  conv =>
    lhs
    simp only [_root_.zero_smul, one_smul, _root_.smul_zero, _root_.add_zero, _root_.zero_add]
  rw [basisVectorContrPauli, basisVectorContrPauli]
  congr 3
  · decide
  · decide

/-- The expansion of `pauliCo` in terms of a basis. -/
lemma pauliCo_basis_expand : pauliCo
    = basisVector pauliCoMap (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + basisVector pauliCoMap (fun | 0 => 0 | 1 => 1 | 2 => 1)
    - basisVector pauliCoMap (fun | 0 => 1 | 1 => 0 | 2 => 1)
    - basisVector pauliCoMap (fun | 0 => 1 | 1 => 1 | 2 => 0)
    + I • basisVector pauliCoMap (fun | 0 => 2 | 1 => 0 | 2 => 1)
    - I • basisVector pauliCoMap (fun | 0 => 2 | 1 => 1 | 2 => 0)
    - basisVector pauliCoMap (fun | 0 => 3 | 1 => 0 | 2 => 0)
    + basisVector pauliCoMap (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
  conv =>
    lhs
    rw [pauliCo]
    rw [contr_tensor_eq <| prod_tensor_eq_fst <| coMetric_basis_expand_tree]
    /- Moving the prod through additions. -/
    rw [contr_tensor_eq <| add_prod _ _ _]
    rw [contr_tensor_eq <| add_tensor_eq_snd <| add_prod _ _ _]
    rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
    /- Moving the prod through smuls. -/
    rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_prod _ _ _]
    rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst
        <| smul_prod _ _ _]
    rw [contr_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd
      <| smul_prod _ _ _]
    /- Moving contraction through addition. -/
    rw [contr_add]
    rw [add_tensor_eq_snd <| contr_add _ _]
    rw [add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
    /- Moving contraction through smul. -/
    rw [add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
    rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
    rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_smul _ _]
    simp only [tensorNode_tensor, add_tensor, smul_tensor]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, neg_smul, one_smul]
  conv =>
    lhs; lhs;
    rw [pauliMatrix_contr_down_0]
  conv =>
    lhs; rhs; lhs; rhs;
    rw [pauliMatrix_contr_down_1]
  conv =>
    lhs; rhs; rhs; lhs; rhs;
    rw [pauliMatrix_contr_down_2]
  conv =>
    lhs; rhs; rhs; rhs; rhs;
    rw [pauliMatrix_contr_down_3]
  simp only [neg_smul, one_smul]
  abel

lemma pauliCo_basis_expand_tree : {pauliCo | μ α β}ᵀ.tensor
    = (TensorTree.add (tensorNode
      (basisVector pauliCoMap (fun | 0 => 0 | 1 => 0 | 2 => 0))) <|
    TensorTree.add (tensorNode
      (basisVector pauliCoMap (fun | 0 => 0 | 1 => 1 | 2 => 1))) <|
    TensorTree.add (TensorTree.smul (-1) (tensorNode
      (basisVector pauliCoMap (fun | 0 => 1 | 1 => 0 | 2 => 1)))) <|
    TensorTree.add (TensorTree.smul (-1) (tensorNode
      (basisVector pauliCoMap (fun | 0 => 1 | 1 => 1 | 2 => 0)))) <|
    TensorTree.add (TensorTree.smul I (tensorNode
      (basisVector pauliCoMap (fun | 0 => 2 | 1 => 0 | 2 => 1)))) <|
    TensorTree.add (TensorTree.smul (-I) (tensorNode
      (basisVector pauliCoMap (fun | 0 => 2 | 1 => 1 | 2 => 0)))) <|
    TensorTree.add (TensorTree.smul (-1) (tensorNode
      (basisVector pauliCoMap (fun | 0 => 3 | 1 => 0 | 2 => 0)))) <|
      (tensorNode (basisVector pauliCoMap (fun | 0 => 3 | 1 => 1 | 2 => 1)))).tensor := by
  rw [pauliCo_basis_expand]
  simp only [Nat.reduceAdd, Fin.isValue, add_tensor, tensorNode_tensor, smul_tensor, neg_smul,
    one_smul]
  rfl

lemma pauliCo_prod_basis_expand {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (t : TensorTree complexLorentzTensor c) :
    (prod (tensorNode pauliCo) t).tensor =
    (((tensorNode
      (basisVector pauliCoMap fun | 0 => 0 | 1 => 0 | 2 => 0)).prod t).add
    (((tensorNode
      (basisVector pauliCoMap fun | 0 => 0 | 1 => 1 | 2 => 1)).prod t).add
    ((TensorTree.smul (-1) ((tensorNode
      (basisVector pauliCoMap fun | 0 => 1 | 1 => 0 | 2 => 1)).prod t)).add
    ((TensorTree.smul (-1) ((tensorNode
      (basisVector pauliCoMap fun | 0 => 1 | 1 => 1 | 2 => 0)).prod t)).add
    ((TensorTree.smul I ((tensorNode
      (basisVector pauliCoMap fun | 0 => 2 | 1 => 0 | 2 => 1)).prod t)).add
    ((TensorTree.smul (-I) ((tensorNode
      (basisVector pauliCoMap fun | 0 => 2 | 1 => 1 | 2 => 0)).prod t)).add
    ((TensorTree.smul (-1) ((tensorNode
      (basisVector pauliCoMap fun | 0 => 3 | 1 => 0 | 2 => 0)).prod t)).add
    ((tensorNode
      (basisVector pauliCoMap fun | 0 => 3 | 1 => 1 | 2 => 1)).prod
      t)))))))).tensor := by
  rw [prod_tensor_eq_fst <| pauliCo_basis_expand_tree]
  /- Moving the prod through additions. -/
  rw [add_prod _ _ _]
  rw [add_tensor_eq_snd <| add_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_prod _ _ _]
  /- Moving the prod through smuls. -/
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <|
    smul_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_fst <| smul_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <|
    smul_prod _ _ _]

end complexLorentzTensor
