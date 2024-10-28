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
import HepLean.Tensors.ComplexLorentz.Basis
/-!

## Basis trees

When contracting e.g. Pauli matrices with other tensors, it is sometimes convienent
to rewrite the contraction in terms of a basis.

The lemmas in this file allow us to do this.
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

## Tree expansions for Pauli matrices.

-/

/-- The map to colors one gets when contracting with Pauli matrices on the right. -/
abbrev pauliMatrixContrMap {n : ℕ} (c : Fin n → complexLorentzTensor.C) :=
  (Sum.elim c ![Color.up, Color.upL, Color.upR] ∘ ⇑finSumFinEquiv.symm)

lemma prod_pauliMatrix_basis_tree_expand {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (t : TensorTree complexLorentzTensor c) :
    (TensorTree.prod t (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)).tensor = (((t.prod (tensorNode
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
  rw [prod_tensor_eq_snd <| pauliMatrix_basis_expand_tree]
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
  rfl

lemma contr_pauliMatrix_basis_tree_expand {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (t : TensorTree complexLorentzTensor c) (i : Fin (n + 3)) (j : Fin (n +2))
    (h : (pauliMatrixContrMap c) (i.succAbove j) =
      complexLorentzTensor.τ ((pauliMatrixContrMap c) i)) :
    (contr i j h (TensorTree.prod t
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor))).tensor =
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
      (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor))).tensor = ((contr i j h ((tensorNode
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
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor))).tensor =
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
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
    PauliMatrix.asConsTensor))).tensor =
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

end complexLorentzTensor

end
