/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Lorentz.ComplexTensor.Basic
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

end complexLorentzTensor
