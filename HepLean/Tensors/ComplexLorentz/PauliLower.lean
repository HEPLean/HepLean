/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.ComplexLorentz.BasisTrees
/-!

## Lowering indices of Pauli matrices.

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

/-- The map to color one gets when lowering the indices of pauli matrices. -/
def pauliMatrixLowerMap := ((Sum.elim ![Color.down, Color.down] ![Color.up, Color.upL, Color.upR] ∘
  ⇑finSumFinEquiv.symm) ∘ Fin.succAbove 0 ∘ Fin.succAbove 1)

lemma pauliMatrix_contr_down_0 :
    (contr 0 1 rfl (((tensorNode (basisVector ![Color.down, Color.down] fun x => 0)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor
    = basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [one_smul, zero_smul, smul_zero, add_zero]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_down_0_tree :
    (contr 0 1 rfl (((tensorNode (basisVector ![Color.down, Color.down] fun x => 0)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor
    = (TensorTree.add (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0)))
    (tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1)))).tensor := by
  exact pauliMatrix_contr_down_0

lemma pauliMatrix_contr_down_1 :
    {(basisVector ![Color.down, Color.down] fun x => 1) | μ ν ⊗
      PauliMatrix.asConsTensor | μ α β}ᵀ.tensor
    = basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1)
    + basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0) := by
  rw [basis_contr_pauliMatrix_basis_tree_expand]
  rw [contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_pos, contrBasisVectorMul_pos,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg,
      contrBasisVectorMul_neg, contrBasisVectorMul_neg]
  simp only [smul_tensor, add_tensor, tensorNode_tensor]
  simp only [zero_smul, one_smul, smul_zero, add_zero, zero_add]
  congr 1
  · congr 1
    funext k
    fin_cases k <;> rfl
  · congr 1
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_down_1_tree :
    {(basisVector ![Color.down, Color.down] fun x => 1) | μ ν ⊗
      PauliMatrix.asConsTensor | μ α β}ᵀ.tensor
    = (TensorTree.add (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1)))
    (tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0)))).tensor := by
  exact pauliMatrix_contr_down_1

lemma pauliMatrix_contr_down_2 :
    {(basisVector ![Color.down, Color.down] fun x => 2) | μ ν ⊗
      PauliMatrix.asConsTensor | μ α β}ᵀ.tensor
    = (- I) • basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1)
    + (I) • basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0) := by
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

lemma pauliMatrix_contr_down_2_tree :
    {(basisVector ![Color.down, Color.down] fun x => 2) | μ ν ⊗
      PauliMatrix.asConsTensor | μ α β}ᵀ.tensor =
    (TensorTree.add
    (smul (- I) (tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1))))
    (smul I (tensorNode (basisVector
      pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0))))).tensor := by
  exact pauliMatrix_contr_down_2

lemma pauliMatrix_contr_down_3 :
    {(basisVector ![Color.down, Color.down] fun x => 3) | μ ν ⊗
    PauliMatrix.asConsTensor | μ α β}ᵀ.tensor
    = basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0)
    + (- 1 : ℂ) • basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
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

lemma pauliMatrix_contr_down_3_tree : {(basisVector ![Color.down, Color.down] fun x => 3) | μ ν ⊗
      PauliMatrix.asConsTensor | μ α β}ᵀ.tensor =
    (TensorTree.add
      ((tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0))))
      (smul (-1) (tensorNode (basisVector pauliMatrixLowerMap
      (fun | 0 => 3 | 1 => 1 | 2 => 1))))).tensor := by
  exact pauliMatrix_contr_down_3

lemma pauliMatrix_lower : {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β}ᵀ.tensor
    = basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0)
    + basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1)
    - basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1)
    - basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0)
    + I • basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1)
    - I • basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0)
    - basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0)
    + basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 1 | 2 => 1) := by
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
  /- Replacing the contractions. -/
  rw [add_tensor_eq_fst <| pauliMatrix_contr_down_0_tree]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| pauliMatrix_contr_down_1_tree]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <|
    pauliMatrix_contr_down_2_tree]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| add_tensor_eq_snd <| smul_tensor_eq <|
    pauliMatrix_contr_down_3_tree]
  /- Simplifying -/
  simp only [add_tensor, smul_tensor, tensorNode_tensor, smul_add,_root_.smul_smul]
  simp only [Nat.reduceAdd, Fin.isValue, neg_smul, one_smul, mul_neg, neg_mul, one_mul,
    _root_.neg_neg, mul_one]
  rfl

lemma pauliMatrix_lower_tree : {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β}ᵀ.tensor
    = (TensorTree.add (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 0 | 2 => 0))) <|
    TensorTree.add (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 0 | 1 => 1 | 2 => 1))) <|
    TensorTree.add (TensorTree.smul (-1) (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 0 | 2 => 1)))) <|
    TensorTree.add (TensorTree.smul (-1) (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 1 | 1 => 1 | 2 => 0)))) <|
    TensorTree.add (TensorTree.smul I (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 0 | 2 => 1)))) <|
    TensorTree.add (TensorTree.smul (-I) (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 2 | 1 => 1 | 2 => 0)))) <|
    TensorTree.add (TensorTree.smul (-1) (tensorNode
      (basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 0 | 2 => 0)))) <|
      (tensorNode (basisVector pauliMatrixLowerMap (fun | 0 => 3 | 1 => 1 | 2 => 1)))).tensor := by
  rw [pauliMatrix_lower]
  simp only [Nat.reduceAdd, Fin.isValue, add_tensor,
    tensorNode_tensor, smul_tensor, neg_smul, one_smul]
  rfl

lemma pauliMatrix_lower_basis_expand_prod {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (t : TensorTree complexLorentzTensor c) :
    (prod {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | μ α β}ᵀ t).tensor =
    (((tensorNode
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
      t)))))))).tensor := by
  rw [prod_tensor_eq_fst <| pauliMatrix_lower_tree]
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

end Fermion
