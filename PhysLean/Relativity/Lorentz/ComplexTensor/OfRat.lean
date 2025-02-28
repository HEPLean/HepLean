/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.ComplexTensor.Basic
import PhysLean.Mathematics.RatComplexNum
/-!

# Basis for tensors in a tensor species

-/

open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace complexLorentzTensor
open OverColor
open PhysLean.RatComplexNum
open PhysLean

variable (S : TensorSpecies)

/--A complex Lorentz tensor from a map
  `(Π j, Fin (complexLorentzTensor.repDim (c j))) → RatComplexNum`. All
  complex Lorentz tensors with rational coefficents with respect to the basis are of this
  form. -/
noncomputable def ofRat {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (f : (Π j, Fin (complexLorentzTensor.repDim (c j))) → RatComplexNum) :
    complexLorentzTensor.F.obj (OverColor.mk c) :=
  (complexLorentzTensor.tensorBasis c).repr.symm <|
  (Finsupp.linearEquivFunOnFinite complexLorentzTensor.k complexLorentzTensor.k
  ((j : Fin n) → Fin (complexLorentzTensor.repDim (c j)))).symm <|
  (fun j => toComplexNum (f j))

@[simp]
lemma ofRat_tensorBasis_repr_apply {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (f : (Π j, Fin (complexLorentzTensor.repDim (c j))) → RatComplexNum)
    (b : Π j, Fin (complexLorentzTensor.repDim (c j))) :
  (complexLorentzTensor.tensorBasis c).repr (ofRat f) b = toComplexNum (f b) := by
  simp [ofRat]
  rfl

lemma ofRat_add {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (f f1 : (Π j, Fin (complexLorentzTensor.repDim (c j))) → RatComplexNum) :
    ofRat (f + f1) = ofRat f + ofRat f1 := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  simp

lemma tensorBasis_eq_ofRat {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (b : Π j, Fin (complexLorentzTensor.repDim (c j))) :
    complexLorentzTensor.tensorBasis c b
    = ofRat (fun b' => if b = b' then ⟨1, 0⟩ else ⟨0, 0⟩) := by
  apply (complexLorentzTensor.tensorBasis c).repr.injective
  simp only [Basis.repr_self]
  ext b'
  simp only [ofRat_tensorBasis_repr_apply]
  rw [Finsupp.single_apply, toComplexNum]
  simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  split
  simp only [Rat.cast_one, Rat.cast_zero, zero_mul, add_zero]
  simp

lemma contr_basis_ratComplexNum {c : complexLorentzTensor.C}
    (i : Fin (complexLorentzTensor.repDim c))
    (j : Fin (complexLorentzTensor.repDim (complexLorentzTensor.τ c))) :
    complexLorentzTensor.castToField
      ((complexLorentzTensor.contr.app (Discrete.mk c)).hom
      (complexLorentzTensor.basis c i ⊗ₜ
      complexLorentzTensor.basis (complexLorentzTensor.τ c) j))
      = toComplexNum (if i.val = j.val then 1 else 0) := by
  match c with
  | Color.upL =>
    change Fermion.leftAltContraction.hom (Fermion.leftBasis i ⊗ₜ Fermion.altLeftBasis j) = _
    rw [Fermion.leftAltContraction_basis]
    simp
  | Color.downL =>
    change Fermion.altLeftContraction.hom (Fermion.altLeftBasis i ⊗ₜ Fermion.leftBasis j) = _
    rw [Fermion.altLeftContraction_basis]
    simp
  | Color.upR =>
    change Fermion.rightAltContraction.hom (Fermion.rightBasis i ⊗ₜ Fermion.altRightBasis j) = _
    rw [Fermion.rightAltContraction_basis]
    simp
  | Color.downR =>
    change Fermion.rightAltContraction.hom (Fermion.rightBasis i ⊗ₜ Fermion.altRightBasis j) = _
    rw [Fermion.rightAltContraction_basis]
    simp
  | Color.up =>
    change Lorentz.contrCoContraction.hom
      (Lorentz.complexContrBasisFin4 i ⊗ₜ Lorentz.complexCoBasisFin4 j) = _
    rw [Lorentz.contrCoContraction_basis]
    simp
  | Color.down =>
    change Lorentz.contrCoContraction.hom
      (Lorentz.complexContrBasisFin4 i ⊗ₜ Lorentz.complexCoBasisFin4 j) = _
    rw [Lorentz.contrCoContraction_basis]
    simp
open TensorTree

lemma prod_ofRat_ofRat {n n1 : ℕ} {c : Fin n → complexLorentzTensor.C}
    (f : (Π j, Fin (complexLorentzTensor.repDim (c j))) → RatComplexNum)
    {c1 : Fin n1 → complexLorentzTensor.C}
    (f1 : (Π j, Fin (complexLorentzTensor.repDim (c1 j))) → RatComplexNum) :
    (TensorTree.prod (tensorNode (ofRat f)) (tensorNode (ofRat f1))).tensor =
    (tensorNode (ofRat (fun b => f (TensorSpecies.TensorBasis.prodEquiv b).1 *
      f1 (TensorSpecies.TensorBasis.prodEquiv b).2))).tensor := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [prod_tensorBasis_repr_apply]
  simp only [tensorNode_tensor, ofRat_tensorBasis_repr_apply, Function.comp_apply]
  erw [ofRat_tensorBasis_repr_apply]
  simp

lemma contr_ofRat {n : ℕ} {c : Fin (n + 1 + 1) → complexLorentzTensor.C} {i : Fin (n + 1 + 1)}
    {j : Fin (n + 1)} {h : c (i.succAbove j) = complexLorentzTensor.τ (c i)}
    (f : (Π k, Fin (complexLorentzTensor.repDim (c k))) → RatComplexNum) :
  (contr i j h (tensorNode (ofRat f))).tensor = (tensorNode (ofRat (fun b =>
    (∑ x : { x // x ∈ TensorSpecies.TensorBasis.ContrSection b },
      f x.1 * if (x.1 i).1 = (x.1 (i.succAbove j)).1 then 1 else 0)))).tensor := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  rw [contr_tensorBasis_repr_apply]
  conv_lhs =>
    enter [2, x]
    rw [contr_basis_ratComplexNum]
    simp only [Nat.succ_eq_add_one, Finset.univ_eq_attach, tensorNode_tensor,
    ofRat_tensorBasis_repr_apply, Fin.coe_cast, mul_one,
    mul_zero, Function.comp_apply]
    rw [← PhysLean.RatComplexNum.toComplexNum.map_mul]
  rw [← map_sum PhysLean.RatComplexNum.toComplexNum]
  erw [ofRat_tensorBasis_repr_apply]

lemma smul_nat_ofRat {c : Fin n → complexLorentzTensor.C} (n : ℕ)
    (f1 : (Π j, Fin (complexLorentzTensor.repDim (c j))) → RatComplexNum) :
    (TensorTree.smul n (tensorNode (ofRat f1))).tensor =
    (tensorNode (ofRat (fun b => n * f1 b))).tensor := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  simp

lemma perm_ofRat {n m : ℕ} {c : Fin n → complexLorentzTensor.C}
    {c1 : Fin m → complexLorentzTensor.C}
    {σ : (OverColor.mk c) ⟶ (OverColor.mk c1)}
    (f : (Π j, Fin (complexLorentzTensor.repDim (c j))) → RatComplexNum) :
    (perm σ (tensorNode (ofRat f))).tensor =
    (tensorNode (ofRat (fun b => f ((TensorSpecies.TensorBasis.congr (Hom.toEquiv σ)
    (OverColor.Hom.toEquiv_comp_apply σ)) b)))).tensor := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  simp only [perm_tensorBasis_repr_apply, tensorNode_tensor, mk_hom, ofRat_tensorBasis_repr_apply]

lemma add_ofRat {n : ℕ} {c : Fin n → complexLorentzTensor.C}
    (f f1 : (Π j, Fin (complexLorentzTensor.repDim (c j))) → RatComplexNum) :
    (add (tensorNode (ofRat f)) (tensorNode (ofRat f1))).tensor =
    (tensorNode (ofRat (fun b => f b + f1 b))).tensor := by
  rw [add_tensor]
  simp [← ofRat_add]
  rfl

end complexLorentzTensor
