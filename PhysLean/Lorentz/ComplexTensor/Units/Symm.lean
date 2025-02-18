/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Lorentz.ComplexTensor.Metrics.Basis
import PhysLean.Lorentz.ComplexTensor.Units.Basis
/-!

## Symmetry lemmas relating to units

-/
open IndexNotation
open Matrix
open TensorTree

namespace complexLorentzTensor

/-!

## Symmetry properties

-/

/-- Swapping indices of `coContrUnit` returns `contrCoUnit`: `{δ' | μ ν = δ | ν μ}ᵀ`. -/
lemma coContrUnit_symm : {δ' | μ ν = δ | ν μ}ᵀ := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, coContrUnit_eq_ofRat,
    contrCoUnit_eq_ofRat, Fin.isValue, cons_val_zero,
    cons_val_one, head_cons, tensorNode_tensor, ofRat_tensorBasis_repr_apply,
    perm_tensorBasis_repr_apply, OverColor.mk_hom, OverColor.equivToHomEq_toEquiv]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide

/-- Swapping indices of `contrCoUnit` returns `coContrUnit`: `{δ | μ ν = δ' | ν μ}ᵀ`. -/
lemma contrCoUnit_symm : {δ | μ ν = δ' | ν μ}ᵀ := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, coContrUnit_eq_ofRat,
    contrCoUnit_eq_ofRat, Fin.isValue, cons_val_zero,
    cons_val_one, head_cons, tensorNode_tensor, ofRat_tensorBasis_repr_apply,
    perm_tensorBasis_repr_apply, OverColor.mk_hom, OverColor.equivToHomEq_toEquiv]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide

/-- Swapping indices of `altLeftLeftUnit` returns `leftAltLeftUnit`: `{δL' | α α' = δL | α' α}ᵀ`. -/
lemma altLeftLeftUnit_symm : {δL' | α α' = δL | α' α}ᵀ := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, altLeftLeftUnit_eq_ofRat,
    leftAltLeftUnit_eq_ofRat, Fin.isValue, cons_val_zero,
    cons_val_one, head_cons, tensorNode_tensor, ofRat_tensorBasis_repr_apply,
    perm_tensorBasis_repr_apply, OverColor.mk_hom, OverColor.equivToHomEq_toEquiv]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide

/-- Swapping indices of `leftAltLeftUnit` returns `altLeftLeftUnit`: `{δL | α α' = δL' | α' α}ᵀ`. -/
lemma leftAltLeftUnit_symm : {δL | α α' = δL' | α' α}ᵀ := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, altLeftLeftUnit_eq_ofRat,
    leftAltLeftUnit_eq_ofRat, Fin.isValue, cons_val_zero,
    cons_val_one, head_cons, tensorNode_tensor, ofRat_tensorBasis_repr_apply,
    perm_tensorBasis_repr_apply, OverColor.mk_hom, OverColor.equivToHomEq_toEquiv]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide

/-- Swapping indices of `altRightRightUnit` returns `rightAltRightUnit`:
`{δR' | β β' = δR | β' β}ᵀ`.
-/
lemma altRightRightUnit_symm : {δR' | β β' = δR | β' β}ᵀ := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, altRightRightUnit_eq_ofRat,
    rightAltRightUnit_eq_ofRat, Fin.isValue, cons_val_zero,
    cons_val_one, head_cons, tensorNode_tensor, ofRat_tensorBasis_repr_apply,
    perm_tensorBasis_repr_apply, OverColor.mk_hom, OverColor.equivToHomEq_toEquiv]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide

/-- Swapping indices of `rightAltRightUnit` returns `altRightRightUnit`:
`{δR | β β' = δR' | β' β}ᵀ`.
-/
lemma rightAltRightUnit_symm : {δR | β β' = δR' | β' β}ᵀ := by
  apply (complexLorentzTensor.tensorBasis _).repr.injective
  ext b
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, altRightRightUnit_eq_ofRat,
    rightAltRightUnit_eq_ofRat, Fin.isValue, cons_val_zero,
    cons_val_one, head_cons, tensorNode_tensor, ofRat_tensorBasis_repr_apply,
    perm_tensorBasis_repr_apply, OverColor.mk_hom, OverColor.equivToHomEq_toEquiv]
  apply (Function.Injective.eq_iff PhysLean.RatComplexNum.toComplexNum_injective).mpr
  revert b
  decide

end complexLorentzTensor
