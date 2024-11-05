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

/-! TODO: Generalize `basis_eq_FD`. -/
lemma basis_eq_FD {n : ℕ} (c : Fin n → complexLorentzTensor.C)
    (b : Π j, Fin (complexLorentzTensor.repDim (c j))) (i : Fin n)
    (h : { as := c i } = { as := c1 }) :
    (complexLorentzTensor.FD.map (eqToHom h)).hom
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
  rw [basis_eq_FD]

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
  simp only [ite_eq_right_iff, one_ne_zero, imp_false]
  exact h

lemma contrBasisVectorMul_pos {n : ℕ} {c : Fin n.succ.succ → complexLorentzTensor.C}
    {i : Fin n.succ.succ} {j : Fin n.succ} {b : Π k, Fin (complexLorentzTensor.repDim (c k))}
    (h : (b i).val = (b (i.succAbove j)).val) :
    contrBasisVectorMul i j b = 1 := by
  rw [contrBasisVectorMul]
  simp only [ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
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
  rw [basis_eq_FD]
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
  have h1 := OverColor.lift.μ_tmul_tprod_mk complexLorentzTensor.FD
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
  have h1 : Fin.ofNat' _ ↑j = j := by
    simp [Fin.ext_iff]
  rw [Basis.repr_self, Finsupp.single_apply, h1]
  exact ite_congr (Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a))
    (congrFun rfl) (congrFun rfl)

end complexLorentzTensor
end
