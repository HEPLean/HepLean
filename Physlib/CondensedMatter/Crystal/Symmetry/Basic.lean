/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Bonds
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Symmetries of a crystal

A crystal symmetry is an invertible rearrangement of sites compatible with lattice translations.

## i. Overview

A crystal consists of a unit cell repeated along the lattice directions. A symmetry transforms
the lattice translations and the sites of the reference cell. These two transformations determine
its action on the entire crystal.

A quarter-turn exchanges the lattice directions of a square pattern. A half-cell shift can
exchange two equivalent sites in a chain with two sites per cell. Both operations extend to the
entire crystal through compatibility with translations.

The resulting group contains all transformations compatible with the lattice translations.
Site positions, bonds and species assignments impose further restrictions. Their stabilizers
select the symmetries preserving the chosen physical structure.

## ii. Key results

- `Crystal.Symmetry` : a symmetry of a crystal, a group.
- `Crystal.Symmetry.apply_eq` : a symmetry acts on every site through the image of the reference
  cell and its lattice automorphism.
- `Crystal.Symmetry.apply_eq_components` : a symmetry sends `⟨n, i⟩` to `⟨A n + bᵢ, σ i⟩`.
- `Crystal.Symmetry.lattice_mul` : the lattice automorphism of a product is the composite.
- `Crystal.Symmetry.labelHom` : the permutation of the labels by a symmetry, a homomorphism.
- `Crystal.Symmetry.Offsets` : one lattice vector for each unit-cell label.
- `Crystal.Symmetry.offset` : the cell in which a symmetry sends the reference site of a label.
- `Crystal.Symmetry.translations` : the translations, a normal subgroup of the symmetries.
- `Crystal.Symmetry.mapBond` : the image of a bond under a symmetry, an action on the bonds.

## iii. Table of contents

- A. Symmetries
  - A.1. Action on the sites
  - A.2. Group structure
  - A.3. Permutation of the labels
  - A.4. Offsets
- B. The translations
- C. Action on bonds

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

/-! ## A. Symmetries -/

/-- A lattice automorphism `A` and an equivalence `φ` of sites satisfying
`φ (a +ᵥ x) = A a +ᵥ φ x`. -/
structure Symmetry (C : Crystal G) where
  /-- The automorphism of the translation group. -/
  lattice : G ≃+ G
  /-- The equivalence of the sites. -/
  sites : C.Site ≃ C.Site
  /-- The site equivalence carries translations along the lattice automorphism. -/
  map_vadd' : ∀ a x, sites (a +ᵥ x) = lattice a +ᵥ sites x

namespace Symmetry

variable {C : Crystal G}

/-! ### A.1. Action on the sites -/

/-- The site action as an `AddActionHom` for `lattice`. -/
def toHom (φ : Symmetry C) : AddActionHom ⇑φ.lattice C.Site C.Site :=
  ⟨φ.sites, φ.map_vadd'⟩

/-- Equality of symmetries follows from equality of their site maps. -/
lemma ext' {φ ψ : Symmetry C} (h : ∀ x, φ.toHom x = ψ.toHom x) : φ = ψ := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C.Site)
  have hA (a : G) : φ.lattice a = ψ.lattice a := by
    refine IsCancelVAdd.right_cancel _ _ (φ.toHom x₀) ?_
    rw [← map_vaddₛₗ φ.toHom, h (a +ᵥ x₀), map_vaddₛₗ ψ.toHom, h x₀]
  obtain ⟨A, f, hf⟩ := φ
  obtain ⟨B, g, hg⟩ := ψ
  obtain rfl : A = B := AddEquiv.ext hA
  obtain rfl : f = g := Equiv.ext h
  rfl

/-- Function application of a symmetry to a site. -/
instance : FunLike (Symmetry C) C.Site C.Site where
  coe φ := φ.toHom
  coe_injective _ _ h := ext' (congrFun h)

/-- Extensionality for the site action. -/
@[ext] lemma ext {φ ψ : Symmetry C} (h : ∀ x, φ x = ψ x) : φ = ψ := ext' h

/-- The site action is bijective. -/
lemma bijective (φ : Symmetry C) : Function.Bijective φ := φ.sites.bijective

/-- Equivariance of the site action under lattice translations. -/
lemma map_vadd (φ : Symmetry C) (a : G) (x : C.Site) : φ (a +ᵥ x) = φ.lattice a +ᵥ φ x :=
  map_vaddₛₗ φ.toHom a x

/-- The image of `⟨n, i⟩` is determined by the image of `⟨0, i⟩` and the lattice map. -/
lemma apply_eq (φ : Symmetry C) (n : G) (i : C.UnitCell) :
    φ ⟨n, i⟩ = ⟨φ.lattice n + (φ (Site.ref i)).cell, (φ (Site.ref i)).label⟩ := by
  simpa [Site.vadd_def] using φ.map_vadd n (Site.ref i)

/-- A symmetry as a permutation of the sites. -/
def toEquiv (φ : Symmetry C) : C.Site ≃ C.Site := φ.sites

/-- Composing equivariant maps gives an equivariant map. -/
lemma comp_map_vadd (φ ψ : Symmetry C) (a : G) (x : C.Site) :
    (φ ∘ ψ) (a +ᵥ x) = (ψ.lattice.trans φ.lattice) a +ᵥ (φ ∘ ψ) x := by
  rw [Function.comp_apply, ψ.map_vadd, φ.map_vadd]
  rfl

/-- The identity is equivariant for the identity automorphism. -/
lemma id_map_vadd (a : G) (x : C.Site) : id (a +ᵥ x) = AddEquiv.refl G a +ᵥ id x := rfl

/-- The inverse of an equivariant bijection is equivariant for the inverse automorphism. -/
lemma symm_map_vadd (φ : Symmetry C) (a : G) (x : C.Site) :
    φ.toEquiv.symm (a +ᵥ x) = φ.lattice.symm a +ᵥ φ.toEquiv.symm x :=
  map_vaddₛₗ (φ.toHom.inverse' φ.toEquiv.symm φ.lattice.apply_symm_apply
    φ.toEquiv.symm_apply_apply φ.toEquiv.apply_symm_apply) a x

/-! ### A.2. Group structure -/

/-- Symmetries form a group under composition. -/
instance (C : Crystal G) : Group (Symmetry C) where
  mul φ ψ := ⟨ψ.lattice.trans φ.lattice, ψ.sites.trans φ.sites, comp_map_vadd φ ψ⟩
  one := ⟨AddEquiv.refl G, Equiv.refl _, id_map_vadd⟩
  inv φ := ⟨φ.lattice.symm, φ.sites.symm, symm_map_vadd φ⟩
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel φ := ext φ.toEquiv.symm_apply_apply

/-- The product of symmetries acts by composition. -/
@[simp] lemma mul_apply (φ ψ : Symmetry C) (x : C.Site) : (φ * ψ) x = φ (ψ x) := rfl

/-- Applying a symmetry and then its inverse fixes every site. -/
@[simp] lemma inv_apply_apply (φ : Symmetry C) (x : C.Site) : φ⁻¹ (φ x) = x :=
  φ.toEquiv.symm_apply_apply x

/-- Applying the inverse and then the symmetry fixes every site. -/
@[simp] lemma apply_inv_apply (φ : Symmetry C) (x : C.Site) : φ (φ⁻¹ x) = x :=
  φ.toEquiv.apply_symm_apply x

/-- The site equivalence viewed as a permutation. -/
def toPerm (C : Crystal G) : Symmetry C →* Equiv.Perm C.Site where
  toFun := toEquiv
  map_one' := Equiv.ext (congrFun rfl)
  map_mul' _ _ := Equiv.ext (congrFun rfl)

/-- The action of `Symmetry C` on `C.Site`. -/
instance : MulAction (Symmetry C) C.Site where
  smul φ x := φ x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The site action agrees with function application. -/
lemma smul_site (φ : Symmetry C) (x : C.Site) : φ • x = φ x := rfl

/-- The lattice automorphism of a product is the composite of the lattice automorphisms. -/
@[simp] lemma lattice_mul (φ ψ : Symmetry C) : (φ * ψ).lattice = φ.lattice + ψ.lattice := rfl

/-- The lattice automorphism of the identity is the identity. -/
@[simp] lemma lattice_one : (1 : Symmetry C).lattice = 0 := rfl

/-! ### A.3. Permutation of the labels -/

/-- The output label of `⟨n, i⟩` equals the output label of its reference site. -/
lemma label_apply (φ : Symmetry C) (n : G) (i : C.UnitCell) :
    (φ ⟨n, i⟩).label = (φ (Site.ref i)).label := by
  rw [apply_eq φ n i]

/-- A symmetry permutes the labels: it sends `i` to the label of the image of `⟨0, i⟩`. -/
instance : MulAction (Symmetry C) C.UnitCell where
  smul φ i := (φ (Site.ref i)).label
  one_smul _ := rfl
  mul_smul φ ψ i := label_apply φ (ψ (Site.ref i)).cell (ψ (Site.ref i)).label

/-- The label-permutation homomorphism of a symmetry. -/
def labelHom (C : Crystal G) : Symmetry C →* Equiv.Perm C.UnitCell :=
  MulAction.toPermHom (Symmetry C) C.UnitCell

/-- Evaluation of the label permutation at `i`. -/
lemma labelHom_apply (φ : Symmetry C) (i : C.UnitCell) :
    labelHom C φ i = (φ (Site.ref i)).label := rfl

/-! ### A.4. Offsets -/

/-- An offset is a lattice vector assigned to each unit-cell label. -/
abbrev Offsets (C : Crystal G) := C.UnitCell → G

/-- The cell coordinates of the images of the reference-cell sites indexed by label. -/
def offset (φ : Symmetry C) : Offsets C := fun i => (φ (Site.ref i)).cell

/-- A symmetry sends `⟨n, i⟩` to `⟨A n + bᵢ, σ i⟩`. Here `A` is its lattice automorphism.
The permutation `σ` acts on labels and `bᵢ` is the offset at `i`. -/
lemma apply_eq_components (φ : Symmetry C) (x : C.Site) :
    φ x = ⟨φ.lattice x.cell + φ.offset x.label, labelHom C φ x.label⟩ :=
  apply_eq φ x.cell x.label

/-- The cell of the image of `⟨n, i⟩` is `A n + bᵢ`. -/
lemma cell_apply (φ : Symmetry C) (x : C.Site) :
    (φ x).cell = φ.lattice x.cell + φ.offset x.label :=
  congrArg Site.cell (apply_eq_components φ x)

/-! ## B. The translations -/

/-- Translation by a fixed vector commutes with the lattice action. -/
lemma vadd_map_vadd (c b : G) (x : C.Site) : c +ᵥ (b +ᵥ x) = AddEquiv.refl G b +ᵥ (c +ᵥ x) :=
  vadd_comm c b x

/-- The homomorphism from the multiplicative lattice to the symmetry group.
Use `translation` for individual translations. -/
def translationHom (C : Crystal G) : Multiplicative G →* Symmetry C where
  toFun a := ⟨AddEquiv.refl G, AddAction.toPerm (Multiplicative.toAdd a), vadd_map_vadd _⟩
  map_one' := ext (zero_vadd G)
  map_mul' a b := ext (add_vadd (Multiplicative.toAdd a) (Multiplicative.toAdd b))

/-- Translation by a lattice vector as a symmetry. -/
def translation (C : Crystal G) (a : G) : Symmetry C :=
  translationHom C (Multiplicative.ofAdd a)

/-- The translation by `a` moves a site by `a`. -/
@[simp] lemma translation_apply (a : G) (x : C.Site) : translation C a x = a +ᵥ x := rfl

/-- Composition of translations corresponds to addition of lattice vectors. -/
lemma translation_add (a b : G) : translation C (a + b) = translation C a * translation C b :=
  map_mul (translationHom C) (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

/-- Translation by zero is the identity. -/
lemma translation_zero : translation C 0 = 1 := map_one (translationHom C)

/-- The subgroup of lattice translations. -/
def translations (C : Crystal G) : Subgroup (Symmetry C) :=
  (translationHom C).range

/-- Translations have trivial lattice automorphism. -/
@[simp] lemma lattice_translation (a : G) : (translation C a).lattice = 0 := rfl

/-- Conjugating a translation by a symmetry translates by the image of the vector. -/
lemma conj_translation (φ : Symmetry C) (a : G) :
    φ * translation C a * φ⁻¹ = translation C (φ.lattice a) := by
  ext x : 1
  show φ (a +ᵥ φ⁻¹ x) = φ.lattice a +ᵥ x
  rw [φ.map_vadd, apply_inv_apply]

/-- Normality of the lattice-translation subgroup. -/
instance : (translations C).Normal where
  conj_mem := by
    rintro _ ⟨a, rfl⟩ φ
    exact ⟨_, (conj_translation φ (Multiplicative.toAdd a)).symm⟩

/-! ## C. Action on bonds -/

section Bonds

variable (φ : Symmetry C)

/-- The image of a bond from label `i` to label `j` has endpoint labels `σ i` and `σ j`.
Its displacement is `A δ + bⱼ - bᵢ`. -/
def mapBond (b : Bond C) : Bond C where
  source := φ • b.source
  target := φ • b.target
  displacement := φ.lattice b.displacement + φ.offset b.target - φ.offset b.source

/-- A symmetry maps sites connected by a bond to sites connected by its image. -/
lemma mapBond_links {b : Bond C} {x y : C.Site} (h : b.Links x y) :
    (φ.mapBond b).Links (φ x) (φ y) := by
  obtain ⟨s, t, d⟩ := b
  obtain ⟨n, i⟩ := x
  obtain ⟨m, j⟩ := y
  simp only [Bond.Links] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨label_apply φ n i, label_apply φ _ j, by
    simp [mapBond, cell_apply, map_add, add_assoc]⟩

/-- The image of a bond under a product is the iterated image. -/
lemma mapBond_mul (ψ : Symmetry C) (b : Bond C) :
    (φ * ψ).mapBond b = φ.mapBond (ψ.mapBond b) := by
  have hl := b.links_reference
  exact Bond.eq_of_links ((φ * ψ).mapBond_links hl) (φ.mapBond_links (ψ.mapBond_links hl))

/-- The identity symmetry fixes every bond. -/
lemma mapBond_one (b : Bond C) : (1 : Symmetry C).mapBond b = b := by
  have hl := b.links_reference
  exact Bond.eq_of_links ((1 : Symmetry C).mapBond_links hl) hl

/-- The induced action of crystal symmetries on bonds. -/
instance : MulAction (Symmetry C) (Bond C) where
  smul φ b := φ.mapBond b
  one_smul := mapBond_one
  mul_smul := mapBond_mul

end Bonds

end Symmetry

end Physlib.CondensedMatter.Crystal
