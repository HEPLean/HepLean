/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.ComplexLorentz.PauliLower
import HepLean.Tensors.ComplexLorentz.Lemmas
/-!

## Contractiong of indices of Pauli matrix.

The main result of this file is `pauliMatrix_contract_pauliMatrix` which states that
`η_{μν} σ^{μ α dot β} σ^{ν α' dot β'} = 2 ε^{αα'} ε^{dot β dot β'}`.

The current way this result is proved is by using tensor tree manipulations.
There is likely a more direct path to this result.

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
open complexLorentzTensor

/-- The map to colors one gets when contracting the 4-vector indices pauli matrices. -/
def pauliMatrixContrPauliMatrixMap := ((Sum.elim
  ((Sum.elim ![Color.down, Color.down] ![Color.up, Color.upL, Color.upR] ∘ ⇑finSumFinEquiv.symm) ∘
  Fin.succAbove 0 ∘ Fin.succAbove 1) ![Color.up, Color.upL, Color.upR] ∘ ⇑finSumFinEquiv.symm) ∘
  Fin.succAbove 0 ∘ Fin.succAbove 2)

lemma pauliMatrix_contr_lower_0_0_0 :
    {(basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0)) | μ α β ⊗
    PauliMatrix.asConsTensor | μ α' β'}ᵀ.tensor =
    basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0)
    + basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_0_1_1 :
    {(basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1)) | μ α β ⊗
    PauliMatrix.asConsTensor | μ α' β'}ᵀ.tensor =
    basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0)
    + basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_1_0_1 :
    {(basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1)) | μ α β ⊗
    PauliMatrix.asConsTensor | μ α' β'}ᵀ.tensor =
    basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    + basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_1_1_0 :
    {(basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0)) | μ α β ⊗
    PauliMatrix.asConsTensor | μ α' β'}ᵀ.tensor =
    basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_2_0_1 :
    {(basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1)) | μ α β ⊗
    PauliMatrix.asConsTensor | μ α' β'}ᵀ.tensor =
      (-I) • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    + (I) •
      basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_2_1_0 :
    {(basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0)) | μ α β ⊗
    PauliMatrix.asConsTensor | μ α' β'}ᵀ.tensor =
      (-I) • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + (I) •
      basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_3_0_0 :
    {(basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0)) | μ α β ⊗
    PauliMatrix.asConsTensor | μ α' β'}ᵀ.tensor =
    basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0)
    + (-1 : ℂ) • basisVector pauliMatrixContrPauliMatrixMap
    (fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_lower_3_1_1 :
    {(basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 1 | 2 => 1)) | μ α β ⊗
    PauliMatrix.asConsTensor | μ α' β'}ᵀ.tensor =
    basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0)
    + (-1 : ℂ) •
      basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 2
    funext k
    fin_cases k <;> rfl
  · congr 2
    funext k
    fin_cases k <;> rfl

/-! TODO: Work out why `pauliMatrix_lower_basis_expand_prod'` is needed. -/
/-- This lemma is exactly the same as `pauliMatrix_lower_basis_expand_prod'`.
  It is needed here for `pauliMatrix_contract_pauliMatrix_aux`. It is unclear why
  `pauliMatrix_lower_basis_expand_prod` does not work. -/
private lemma pauliMatrix_lower_basis_expand_prod' {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (t : TensorTree complexLorentzTensor c) :
    (prod {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β}ᵀ t).tensor =
    ((((tensorNode
      (basisVector pauliMatrixLowerMap fun | 0 => 0 | 1 => 0 | 2 => 0)).prod t).add
    (((tensorNode
      (basisVector pauliMatrixLowerMap fun | 0 => 0 | 1 => 1 | 2 => 1)).prod t).add
    ((TensorTree.smul (-1) ((tensorNode
      (basisVector pauliMatrixLowerMap fun | 0 => 1 | 1 => 0 | 2 => 1)).prod t)).add
    ((TensorTree.smul (-1) ((tensorNode
      (basisVector pauliMatrixLowerMap fun | 0 => 1 | 1 => 1 | 2 => 0)).prod t)).add
    ((TensorTree.smul I ((tensorNode
      (basisVector pauliMatrixLowerMap fun | 0 => 2 | 1 => 0 | 2 => 1)).prod t)).add
    ((TensorTree.smul (-I) ((tensorNode
      (basisVector pauliMatrixLowerMap fun | 0 => 2 | 1 => 1 | 2 => 0)).prod t)).add
    ((TensorTree.smul (-1) ((tensorNode
      (basisVector pauliMatrixLowerMap fun | 0 => 3 | 1 => 0 | 2 => 0)).prod t)).add
    ((tensorNode
      (basisVector pauliMatrixLowerMap fun | 0 => 3 | 1 => 1 | 2 => 1)).prod
      t))))))))).tensor := by
    exact pauliMatrix_lower_basis_expand_prod _

lemma pauliMatrix_contract_pauliMatrix_aux :
    {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β ⊗
    PauliMatrix.asConsTensor | ν α' β'}ᵀ.tensor
    = ((tensorNode
      ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0) +
        basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1)).add
    ((tensorNode
      ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0) +
      basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1)).add
    ((TensorTree.smul (-1) (tensorNode
      ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1) +
      basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0))).add
    ((TensorTree.smul (-1) (tensorNode
      ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1) +
      basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0))).add
    ((TensorTree.smul I (tensorNode
      ((-I • basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1) +
        I •
        basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0))).add
    ((TensorTree.smul (-I) (tensorNode
      ((-I • basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1) +
      I • basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0))).add
      ((TensorTree.smul (-1) (tensorNode
        ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0) +
        (-1 : ℂ) •
        basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1))).add
      (tensorNode
        ((basisVector pauliMatrixContrPauliMatrixMap fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0) +
        (-1 : ℂ) • basisVector pauliMatrixContrPauliMatrixMap
          fun | 0 => 1 | 1 => 1 | 2 => 1 | 3 => 1))))))))).tensor := by
  rw [contr_tensor_eq <| pauliMatrix_lower_basis_expand_prod' _]
  /- Moving contraction through addition. -/
  rw [contr_add]
  rw [add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| contr_add _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| contr_add _ _]
  /- Moving contraction through smul. -/
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <|
    contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| contr_smul _ _]
  /- Replacing the contractions. -/
  rw [add_tensor_eq_fst <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_0_0_0]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| eq_tensorNode_of_eq_tensor <|
    pauliMatrix_contr_lower_0_1_1]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <|
    eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_1_0_1]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <|
    smul_tensor_eq <| eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_1_1_0]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_fst <| smul_tensor_eq <| eq_tensorNode_of_eq_tensor <|
    pauliMatrix_contr_lower_2_0_1]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| eq_tensorNode_of_eq_tensor
    <| pauliMatrix_contr_lower_2_1_0]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <|
    eq_tensorNode_of_eq_tensor <| pauliMatrix_contr_lower_3_0_0]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| eq_tensorNode_of_eq_tensor <|
    pauliMatrix_contr_lower_3_1_1]

lemma pauliMatrix_contract_pauliMatrix_expand :
    {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β ⊗
    PauliMatrix.asConsTensor | ν α' β'}ᵀ.tensor =
    2 • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1)
    + 2 • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 1 | 2 => 0 | 3 => 0)
    - 2 • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    - 2 • basisVector pauliMatrixContrPauliMatrixMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1) := by
  rw [pauliMatrix_contract_pauliMatrix_aux]
  simp only [Nat.reduceAdd, Fin.isValue, Fin.succAbove_zero, neg_smul,
    one_smul, add_tensor, tensorNode_tensor, smul_tensor, smul_add, smul_neg, _root_.smul_smul,
    neg_mul, _root_.neg_neg]
  ring_nf
  rw [Complex.I_sq]
  simp only [neg_smul, one_smul, _root_.neg_neg]
  abel

/-- The statement that `η_{μν} σ^{μ α dot β} σ^{ν α' dot β'} = 2 ε^{αα'} ε^{dot β dot β'}`. -/
theorem pauliMatrix_contract_pauliMatrix :
    {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β ⊗
    PauliMatrix.asConsTensor | ν α' β' =
    2 •ₜ Fermion.leftMetric | α α' ⊗ Fermion.rightMetric | β β'}ᵀ := by
  rw [pauliMatrix_contract_pauliMatrix_expand]
  rw [perm_tensor_eq <| smul_tensor_eq <| leftMetric_mul_rightMetric_tree]
  rw [perm_smul]
  /- Moving perm through adds. -/
  rw [smul_tensor_eq <| perm_add _ _ _]
  rw [smul_tensor_eq <| add_tensor_eq_snd <| perm_add _ _ _]
  rw [smul_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| perm_add _ _ _]
  /- Moving perm through smul. -/
  rw [smul_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_fst <| perm_smul _ _ _]
  rw [smul_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd
    <| add_tensor_eq_fst <| perm_smul _ _ _]
  /- Perm acting on basis. -/
  erw [smul_tensor_eq <| add_tensor_eq_fst <| perm_basisVector_tree _ _]
  erw [smul_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <|
    perm_basisVector_tree _ _]
  erw [smul_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <|
    smul_tensor_eq <| perm_basisVector_tree _ _]
  erw [smul_tensor_eq <| add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <|
    perm_basisVector_tree _ _]
  /- Simplifying. -/
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  have h1 (b0011 b1100 b0110 b1001 : CoeSort.coe (complexLorentzTensor.F.obj
      (OverColor.mk pauliMatrixContrPauliMatrixMap))) :
      ((2 • b0011 + 2 • b1100) - 2 • b0110 - 2 • b1001) = (2 : ℂ) • ((b0011) +
      (((-1 : ℂ)• b0110) + (((-1 : ℂ) •b1001) + b1100))) := by
    trans (2 : ℂ) • b0011 + (2 : ℂ) • b1100 - ((2 : ℂ) • b0110) - ((2 : ℂ) • b1001)
    · repeat rw [two_smul]
    · simp only [neg_smul, one_smul, smul_add, smul_neg]
      abel
  rw [h1]
  congr
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

end Fermion
