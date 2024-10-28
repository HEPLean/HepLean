/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.ComplexLorentz.PauliLower
import HepLean.Tensors.Tree.NodeIdentities.ProdContr
import HepLean.Tensors.Tree.NodeIdentities.Congr
import HepLean.Tensors.Tree.NodeIdentities.ProdAssoc
/-!

## Bispinors

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
open Lorentz

/-- A bispinor `pᵃᵃ` created from a lorentz vector `p^μ`. -/
def contrBispinorUp (p : complexContr) :=
  {p | μ ⊗ pauliCo | μ α β}ᵀ.tensor

lemma tensorNode_contrBispinorUp (p : complexContr) :
    (tensorNode (contrBispinorUp p)).tensor = {p | μ ⊗ pauliCo | μ α β}ᵀ.tensor := by
  rw [contrBispinorUp, tensorNode_tensor]

/-- An up-bispinor is equal to `pauliCo | μ α β ⊗ p | μ`-/
lemma contrBispinorUp_eq_pauliCo_self (p : complexContr) :
    {contrBispinorUp p | α β = pauliCo | μ α β ⊗ p | μ}ᵀ := by
  rw [tensorNode_contrBispinorUp]
  conv_lhs =>
    rw [contr_tensor_eq <| prod_comm _ _ _ _]
    rw [perm_contr]
    rw [perm_tensor_eq <| contr_swap _ _]
    rw [perm_perm]
  apply perm_congr
  · apply OverColor.Hom.ext
    ext x
    match x with
    | (0 : Fin 2) => rfl
    | (1 : Fin 2)  => rfl
  · rfl

set_option maxRecDepth 2000 in
lemma altRightMetric_contr_contrBispinorUp_assoc (p : complexContr) :
    {Fermion.altRightMetric | β β' ⊗ contrBispinorUp p | α β =
    Fermion.altRightMetric | β β' ⊗ pauliCo | μ α β ⊗ p | μ}ᵀ := by
  conv_lhs =>
    rw [contr_tensor_eq <| prod_tensor_eq_snd <| contrBispinorUp_eq_pauliCo_self _]
    rw [contr_tensor_eq <| prod_perm_right  _ _ _ _]
    rw [perm_contr]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_contr _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    erw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <| prod_assoc _ _ _ _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
  conv_rhs =>
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_prod _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    erw [perm_tensor_eq <| contr_tensor_eq <| perm_contr _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_contr _ _ _]
    rw [perm_perm]
  apply perm_congr (_) rfl
  · apply OverColor.Hom.fin_ext
    intro i
    fin_cases i
    exact rfl
    exact rfl

/-- A bispinor `pₐₐ` created from a lorentz vector `p^μ`. -/
def contrBispinorDown (p : complexContr) :=
  {Fermion.altLeftMetric | α α' ⊗ Fermion.altRightMetric | β β' ⊗
    (contrBispinorUp p) | α β}ᵀ.tensor

/-- Expands the tensor node of `contrBispinorDown` into a tensor tree based on
  `contrBispinorUp`. -/
lemma tensorNode_contrBispinorDown (p : complexContr) :
    {contrBispinorDown p | α β}ᵀ.tensor = {Fermion.altLeftMetric | α α' ⊗
    Fermion.altRightMetric | β β' ⊗ (contrBispinorUp p) | α β}ᵀ.tensor := by
  rw [contrBispinorDown, tensorNode_tensor]

set_option maxRecDepth 10000 in
lemma contrBispinorDown_eq_metric_contr_contrBispinorUp  (p : complexContr) :
    {contrBispinorDown p | α' β' = Fermion.altLeftMetric | α α' ⊗
    (Fermion.altRightMetric | β β' ⊗ contrBispinorUp p | α β)}ᵀ := by
  rw [tensorNode_contrBispinorDown]
  conv_lhs =>
    rw [contr_tensor_eq <| contr_tensor_eq <| prod_assoc' _ _ _ _ _ _]
    rw [contr_tensor_eq <| perm_contr _ _]
    rw [perm_contr]
    rw [perm_tensor_eq <| contr_contr _ _ _]
    rw [perm_perm]
  conv_rhs =>
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_contr _ _ _ ]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
  apply perm_congr
  · apply OverColor.Hom.ext
    ext x
    match x with
    | (0 : Fin 2) => rfl
    | (1 : Fin 2) => rfl
  · rfl

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2000 in
lemma contrBispinorDown_eq_contr_with_self (p : complexContr) :
    {contrBispinorDown p | α' β' = (Fermion.altLeftMetric | α α' ⊗
    (Fermion.altRightMetric | β β' ⊗ pauliCo | μ α β)) ⊗ p | μ}ᵀ := by
  rw [contrBispinorDown_eq_metric_contr_contrBispinorUp]
  conv_lhs =>
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <| altRightMetric_contr_contrBispinorUp_assoc _]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_perm_right _ _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _ ]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_tensor_eq <| prod_contr _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    erw [perm_tensor_eq <| contr_tensor_eq <| contr_tensor_eq <|
        prod_assoc _ _ _ _ _ _]
    rw [perm_tensor_eq <| contr_tensor_eq <| perm_contr _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
  conv =>
    rhs
    rw [perm_tensor_eq <| contr_tensor_eq <| contr_prod _ _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    erw [perm_tensor_eq <| contr_tensor_eq <| perm_contr _ _]
    rw [perm_tensor_eq <| perm_contr _ _]
    rw [perm_perm]
    rw [perm_tensor_eq <| contr_contr _ _ _]
    rw [perm_perm]
  apply congrArg
  apply congrFun
  apply congrArg
  apply OverColor.Hom.fin_ext
  intro i
  fin_cases i
  exact rfl
  exact rfl

/-- Expansion of a `contrBispinorDown` into the original contravariant tensor nested
  between pauli matrices and metrics. -/
lemma contrBispinorDown_eq_metric_mul_self_mul_pauli (p : complexContr) :
    {contrBispinorDown p | α β}ᵀ.tensor = {Fermion.altLeftMetric | α α' ⊗
    Fermion.altRightMetric | β β' ⊗ (p | μ ⊗ pauliCo | μ α β)}ᵀ.tensor := by
  conv =>
    lhs
    rw [tensorNode_contrBispinorDown]
    rw [contr_tensor_eq <| contr_tensor_eq <| prod_tensor_eq_snd <| tensorNode_contrBispinorUp p]

end complexLorentzTensor
end
