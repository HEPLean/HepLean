/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

# Commuting products

The results here follow from the properties of Monoidal categories and monoidal functors.
-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorTree

variable {S : TensorStruct} {n n2 : ℕ}
    (c : Fin n → S.C) (c2 : Fin n2 → S.C)

def braidPerm : OverColor.mk (Sum.elim c2 c ∘ ⇑finSumFinEquiv.symm) ⟶
    OverColor.mk (Sum.elim c c2 ∘ ⇑finSumFinEquiv.symm) :=
  (equivToIso finSumFinEquiv).inv ≫
  (BraidedCategory.braiding (OverColor.mk c2) (OverColor.mk c)).hom
  ≫ (equivToIso finSumFinEquiv).hom

theorem prod_comm (t : TensorTree S c) (t2 : TensorTree S c2) :
    (prod t t2).tensor = (perm (braidPerm c c2) (prod t2 t)).tensor := by

  sorry
end TensorTree
