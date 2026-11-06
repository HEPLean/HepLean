/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.PointOperations

/-!
# Species-preserving crystal symmetries

A species assignment selects the crystal symmetries preserving each site's species.

## i. Overview

A species assignment records a chemical element or another site type at each unit-cell label.
The assignment repeats throughout the crystal.

Consider an equally spaced chain of alternating A and B atoms. A shift by one site preserves
distances and nearest-neighbour bonds. It exchanges the A and B labels. The species assignment
selects the subgroup preserving the two atomic species.

A symmetry preserves species when it exchanges labels carrying the same species. A uniform
assignment admits every crystal symmetry. An injective assignment admits precisely the
symmetries fixing every label.

Shifts preserve all labels and every species assignment. Species preservation can be imposed
alongside distance and bond preservation.

## ii. Key results

- `Symmetry.speciesGroup` : the symmetries preserving a species assignment.
- `Symmetry.speciesGroup_const` : a constant assignment admits every symmetry.
- `Symmetry.speciesGroup_eq_ker_labelHom` : an injective assignment admits exactly the symmetries
  that fix every label.
- `Symmetry.speciesGroup_le_comp` : merging species enlarges the symmetry group.
- `Symmetry.shift_mem_speciesGroup` : shifts preserve every assignment.
- `Symmetry.translations_le_speciesGroup` : translations preserve every assignment.

## iii. Table of contents

- A. Species-preserving symmetries
- B. Merging species
- C. Shifts and translations

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Symmetry

variable {C : Crystal G} {Q : Type*}

/-! ## A. Species-preserving symmetries -/

/-- The pullback action on species assignments induced by the action on unit-cell labels. -/
local instance : MulAction (Symmetry C) (Species C Q) := arrowAction

/-- The stabilizer of the species assignment `q` under the induced action on functions. -/
def speciesGroup (q : Species C Q) : Subgroup (Symmetry C) :=
  MulAction.stabilizer (Symmetry C) q

/-- A symmetry preserves `q` exactly when it sends every label to one of the same species. -/
lemma mem_speciesGroup_iff {q : Species C Q} {φ : Symmetry C} :
    φ ∈ speciesGroup q ↔ ∀ i, q (φ • i) = q i := by
  rw [← inv_mem_iff, speciesGroup, MulAction.mem_stabilizer_iff, funext_iff]
  show (∀ i, q ((φ⁻¹)⁻¹ • i) = q i) ↔ _
  rw [inv_inv]

/-- Every crystal symmetry preserves a constant species assignment. -/
lemma speciesGroup_const (c : Q) : speciesGroup (C := C) (Function.const _ c) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro φ
  exact mem_speciesGroup_iff.2 (congrFun rfl)

/-- The kernel of `labelHom` preserves every species assignment. -/
lemma ker_labelHom_le_speciesGroup (q : Species C Q) : (labelHom C).ker ≤ speciesGroup q := by
  intro φ hφ
  rw [mem_speciesGroup_iff]
  intro i
  exact congrArg q (Equiv.ext_iff.1 hφ i)

/-- An injective species assignment has stabilizer `ker labelHom`. -/
lemma speciesGroup_eq_ker_labelHom {q : Species C Q} (hq : Function.Injective q) :
    speciesGroup q = (labelHom C).ker := by
  refine le_antisymm ?_ (ker_labelHom_le_speciesGroup q)
  intro φ hφ
  ext i
  exact hq (mem_speciesGroup_iff.1 hφ i)

/-! ## B. Merging species -/

/-- Composing a species assignment with any map `f` can only enlarge its stabilizer. -/
lemma speciesGroup_le_comp (q : Species C Q) {Q' : Type*} (f : Q → Q') :
    speciesGroup q ≤ speciesGroup (f ∘ q) := by
  intro φ h
  rw [mem_speciesGroup_iff] at h ⊢
  intro i
  exact congrArg f (h i)

/-! ## C. Shifts and translations -/

/-- Every shift fixes the unit-cell labels and so preserves species. -/
lemma shift_mem_speciesGroup (q : Species C Q) (b : C.UnitCell → G) :
    shift C b ∈ speciesGroup q :=
  mem_speciesGroup_iff.2 (congrFun rfl)

/-- The translation subgroup preserves every species assignment. -/
lemma translations_le_speciesGroup (q : Species C Q) : translations C ≤ speciesGroup q := by
  rintro _ ⟨a, rfl⟩
  exact mem_speciesGroup_iff.2 (congrFun rfl)

end Symmetry

end Physlib.CondensedMatter.Crystal
