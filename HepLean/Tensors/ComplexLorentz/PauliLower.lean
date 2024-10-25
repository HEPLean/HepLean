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

def pauliCo := {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | ν α β}ᵀ.tensor

lemma tensorNode_pauliCo : (tensorNode pauliCo).tensor =
    {Lorentz.coMetric | μ ν ⊗ PauliMatrix.asConsTensor | ν α β}ᵀ.tensor := by
  rw [pauliCo]
  rfl

/-- The map to color one gets when lowering the indices of pauli matrices. -/
def pauliCoMap := ((Sum.elim ![Color.down, Color.down] ![Color.up, Color.upL, Color.upR] ∘
  ⇑finSumFinEquiv.symm) ∘ Fin.succAbove 1 ∘ Fin.succAbove 1)

lemma pauliMatrix_contr_down_0 :
    (contr 1 1 rfl (((tensorNode (basisVector ![Color.down, Color.down] fun x => 0)).prod
    (constThreeNodeE complexLorentzTensor Color.up Color.upL Color.upR
      PauliMatrix.asConsTensor)))).tensor
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
    {(basisVector ![Color.down, Color.down] fun x => 1) | ν μ ⊗
      PauliMatrix.asConsTensor | μ α β}ᵀ.tensor
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
    {(basisVector ![Color.down, Color.down] fun x => 2) | μ ν ⊗
      PauliMatrix.asConsTensor | ν α β}ᵀ.tensor
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
  congr 1
  · rw [basisVectorContrPauli]
    congr 2
    funext k
    fin_cases k <;> rfl
  · rw [basisVectorContrPauli]
    congr 2
    funext k
    fin_cases k <;> rfl

lemma pauliMatrix_contr_down_3 :
    {(basisVector ![Color.down, Color.down] fun x => 3) | μ ν ⊗
    PauliMatrix.asConsTensor | ν α β}ᵀ.tensor
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
  congr 1
  · rw [basisVectorContrPauli]
    congr 1
    funext k
    fin_cases k <;> rfl
  · rw [basisVectorContrPauli]
    congr 1
    congr 1
    funext k
    fin_cases k <;> rfl

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

lemma pauliCo_basis_expand_tree : pauliCo
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
  rw [prod_tensor_eq_fst <| tensorNode_pauliCo]
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

end Fermion
