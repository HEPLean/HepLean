/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.Basic
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Shifts and point operations of a crystal

Every crystal symmetry can be separated into a point operation and a label-dependent shift.

## i. Overview

A crystal symmetry transforms lattice directions and unit-cell labels. It also sends reference
sites into translated cells. Its action has the form

`⟨n, i⟩ ↦ ⟨A n + bᵢ, σ i⟩`.

Here `A` transforms lattice vectors. The permutation `σ` acts on unit-cell labels. The offset
`bᵢ` gives the cell containing the image of reference site `i`. Each label has its own offset.
A lattice translation uses the same offset for every label.

The lattice automorphism and label permutation define a *point operation*. Label-dependent
*shifts* account for the offsets. Every symmetry is a point operation followed by a shift.
Point operations also transform shifts. This action gives the symmetry group its semidirect
product structure. The construction uses the lattice group and unit-cell labels.

## ii. Key results

- `Crystal.Symmetry.ofSemidirect` : apply the lattice automorphism `A` and label permutation
  `σ` first. Then apply the shift `b` to obtain `(n, i) ↦ (A n + b (σ i), σ i)`.
- `Crystal.Symmetry.semidirectEquiv` : the symmetry group is isomorphic to the semidirect product
  `(UnitCell → G) ⋊ (Aut G × Perm UnitCell)` of the shifts and the point operations.
- `Crystal.Symmetry.shift` and `Crystal.Symmetry.linear` : label-dependent shifts and zero-offset
  point operations.
- `Crystal.Symmetry.pointOp` : the point operation of a symmetry, a homomorphism.
- `Crystal.Symmetry.pointOp_eq_one_iff` : the symmetries with trivial point operation are the
  shifts.

## iii. Table of contents

- A. The symmetry group as a semidirect product
- B. Shifts and point operations

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L4, Sections 4.3 and 4.4.
  [ref: goehmann_solid_state_2021]

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Symmetry

variable {C : Crystal G} (A B : G ≃+ G) (σ τ : Equiv.Perm C.UnitCell)
  (b b' : Offsets C)

/-! ## A. The symmetry group as a semidirect product -/

/-- The action of the point operations on the shifts. A lattice automorphism `A` and a label
permutation `σ` send `b` to `A ∘ b ∘ σ⁻¹`. -/
def shiftAction (C : Crystal G) :
    Multiplicative (AddAut G) × Equiv.Perm C.UnitCell →*
      MulAut (Multiplicative (Offsets C)) where
  toFun p := (AddEquiv.arrowCongr p.2 (Multiplicative.toAdd p.1)).toMultiplicative
  map_one' := MulEquiv.ext (congrFun rfl)
  map_mul' _ _ := MulEquiv.ext (congrFun rfl)

/-- The semidirect product of label-dependent shifts by lattice automorphisms and label
permutations. -/
abbrev ShiftPointOp (C : Crystal G) :=
  Multiplicative (Offsets C) ⋊[shiftAction C] (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell)

/-- The site equivalence of `(b, (A, σ))`. It sends `⟨n, i⟩` to `⟨A n + b (σ i), σ i⟩`. -/
def ofSemidirectEquiv (C : Crystal G) (y : ShiftPointOp C) : C.Site ≃ C.Site where
  toFun x := ⟨Multiplicative.toAdd y.right.1 x.cell +
    Multiplicative.toAdd y.left (y.right.2 x.label), y.right.2 x.label⟩
  invFun x := ⟨(Multiplicative.toAdd y.right.1).symm
    (x.cell - Multiplicative.toAdd y.left x.label), y.right.2.symm x.label⟩
  left_inv x := Site.ext (by simp) (by simp)
  right_inv x := Site.ext (by simp) (by simp)

/-- The symmetry associated with a shift and a point operation. -/
def ofSemidirect (C : Crystal G) (y : ShiftPointOp C) : Symmetry C :=
  ⟨Multiplicative.toAdd y.right.1,
    ofSemidirectEquiv C y,
    fun _ _ => Site.ext (by simp [ofSemidirectEquiv, Site.vadd_def, add_assoc]) rfl⟩

/-- `ofSemidirect C (b, (A, σ))` sends `⟨n, i⟩` to `⟨A n + b (σ i), σ i⟩`. -/
@[simp] lemma ofSemidirect_apply (y : ShiftPointOp C) (x : C.Site) :
    ofSemidirect C y x = ⟨Multiplicative.toAdd y.right.1 x.cell +
      Multiplicative.toAdd y.left (y.right.2 x.label), y.right.2 x.label⟩ := rfl

/-- The lattice automorphism of `ofSemidirect C (b, (A, σ))` is `A`. -/
@[simp] lemma lattice_ofSemidirect (y : ShiftPointOp C) :
    (ofSemidirect C y).lattice = Multiplicative.toAdd y.right.1 := rfl

/-- The label permutation of `ofSemidirect C (b, (A, σ))` is `σ`. -/
@[simp] lemma labelHom_ofSemidirect (y : ShiftPointOp C) :
    labelHom C (ofSemidirect C y) = y.right.2 :=
  Equiv.ext (congrFun rfl)

/-- `ofSemidirect` respects multiplication. -/
lemma ofSemidirect_mul (x y : ShiftPointOp C) :
    ofSemidirect C (x * y) = ofSemidirect C x * ofSemidirect C y := by
  ext z : 1
  refine Site.ext ?_ rfl
  simp [shiftAction, AddEquiv.arrowCongr]
  rw [← add_assoc, add_right_comm]

/-- An isomorphism between the symmetry group and `(UnitCell → G) ⋊ (Aut G × Perm UnitCell)`.
The point operations act on shifts through `shiftAction`. -/
def semidirectEquiv (C : Crystal G) : ShiftPointOp C ≃* Symmetry C where
  toFun := ofSemidirect C
  invFun φ := ⟨Multiplicative.ofAdd (φ.offset ∘ (labelHom C φ).symm),
    Multiplicative.ofAdd φ.lattice, labelHom C φ⟩
  left_inv y := by
    refine SemidirectProduct.ext (Multiplicative.toAdd.injective ?_)
      (Prod.ext (by simp) (by simp))
    ext i
    simp [offset]
  right_inv φ := by
    ext x : 1
    refine Site.ext ?_ ?_
    · simp [cell_apply]
    · exact (label_apply φ x.cell x.label).symm
  map_mul' := ofSemidirect_mul

/-! ## B. Shifts and point operations -/

/-- The symmetry `⟨n, i⟩ ↦ ⟨n + b i, i⟩` with identity lattice and label actions. -/
def shift (C : Crystal G) (b : Offsets C) : Symmetry C :=
  ofSemidirect C (SemidirectProduct.inl (Multiplicative.ofAdd b))

/-- The zero-offset symmetry `⟨n, i⟩ ↦ ⟨A n, σ i⟩`. -/
def linear (C : Crystal G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) : Symmetry C :=
  ofSemidirect C (SemidirectProduct.inr (Multiplicative.ofAdd A, σ))

/-- The homomorphism retaining the lattice automorphism and label permutation and setting all
offsets to zero. -/
def pointOp (C : Crystal G) : Symmetry C →* Symmetry C :=
  (semidirectEquiv C).toMonoidHom.comp (SemidirectProduct.inr.comp
    (SemidirectProduct.rightHom.comp (semidirectEquiv C).symm.toMonoidHom))

/-- A shift has trivial lattice automorphism. -/
@[simp] lemma lattice_shift : (shift C b).lattice = 0 := rfl

/-- `shift C b` sends `⟨n, i⟩` to `⟨n + bᵢ, i⟩`. -/
@[simp] lemma shift_apply (x : C.Site) : shift C b x = ⟨x.cell + b x.label, x.label⟩ := rfl

/-- The lattice automorphism of `linear C A σ` is `A`. -/
@[simp] lemma lattice_linear : (linear C A σ).lattice = A := rfl

/-- `linear C A σ` sends `⟨n, i⟩` to `⟨A n, σ i⟩`. -/
@[simp] lemma linear_apply (x : C.Site) : linear C A σ x = ⟨A x.cell, σ x.label⟩ :=
  Site.ext (add_zero _) rfl

/-- Shifts compose by adding their vectors: `shift (b + b') = shift b * shift b'`. -/
lemma shift_add : shift C (b + b') = shift C b * shift C b' := by
  simp only [shift, ofAdd_add, map_mul, ofSemidirect_mul]

/-- Point operations compose through their components: `linear (A + B) (σ * τ) = linear A σ * linear
B τ`. -/
lemma linear_add_mul : linear C (A + B) (σ * τ) = linear C A σ * linear C B τ := by
  rw [linear, linear, linear, ← ofSemidirect_mul, ← map_mul]
  rfl

/-- A shift by the same vector `a` on every label is the translation by `a`. -/
lemma shift_const (a : G) : shift C (Function.const C.UnitCell a) = translation C a := by
  ext x : 1
  exact Site.ext (add_comm _ _) rfl

/-- A shift preserves the label permutation of a point operation. -/
@[simp] lemma labelHom_shift_mul_linear : labelHom C (shift C b * linear C A σ) = σ := by
  simp [shift, linear]

/-- The offsets of the point operation `(A, σ)` followed by the shift `b` are `b ∘ σ`. -/
@[simp] lemma offset_shift_mul_linear : (shift C b * linear C A σ).offset = b ∘ σ := by
  ext i
  simp [offset, shift_apply, linear_apply]

/-- Composition in shift and point-operation form:
`(b, A, σ) * (b', B, τ) = (b + A ∘ b' ∘ σ⁻¹, A + B, σ * τ)`.
Here `A + B` denotes composition `A ∘ B`. -/
lemma shift_mul_linear_mul :
    (shift C b * linear C A σ) * (shift C b' * linear C B τ) =
      shift C (b + A ∘ b' ∘ σ.symm) * linear C (A + B) (σ * τ) := by
  ext x : 1
  apply Site.ext
  · simp [map_add, add_comm, add_left_comm]
  · rfl

/-- Every symmetry is a point operation followed by a shift. The shift vectors are `offset ∘ σ⁻¹`. -/
lemma eq_shift_mul_linear (φ : Symmetry C) :
    φ = shift C (φ.offset ∘ (labelHom C φ).symm) * linear C φ.lattice (labelHom C φ) := by
  change φ = semidirectEquiv C _ * semidirectEquiv C _
  rw [← map_mul, ← SemidirectProduct.mk_eq_inl_mul_inr]
  exact ((semidirectEquiv C).apply_symm_apply φ).symm

/-- Every symmetry is a point operation followed by a shift. -/
lemma exists_eq_shift_mul_pointOp (φ : Symmetry C) : ∃ b, φ = shift C b * pointOp C φ :=
  ⟨_, eq_shift_mul_linear φ⟩

/-- A shift has trivial point operation. -/
@[simp] lemma pointOp_shift : pointOp C (shift C b) = 1 := by
  change pointOp C (semidirectEquiv C _) = 1
  simp [pointOp]

/-- A symmetry has trivial point operation exactly when it is a shift. -/
lemma pointOp_eq_one_iff (φ : Symmetry C) : pointOp C φ = 1 ↔ ∃ b, φ = shift C b := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := exists_eq_shift_mul_pointOp φ
    exact ⟨b, by rw [hb, h, mul_one]⟩
  · rintro ⟨b, rfl⟩
    exact pointOp_shift b

/-- A translation has trivial point operation. -/
lemma pointOp_translation (a : G) : pointOp C (translation C a) = 1 := by
  rw [← shift_const, pointOp_shift]

end Symmetry

end Physlib.CondensedMatter.Crystal
