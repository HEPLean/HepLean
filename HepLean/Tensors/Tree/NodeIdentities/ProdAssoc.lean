/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
/-!

# Associativity of products

The results here follow from the properties of braided categories and braided functors.
-/

open IndexNotation
open CategoryTheory
open MonoidalCategory
open OverColor
open HepLean.Fin

namespace TensorTree

variable {S : TensorSpecies} {n n2 n3 : ℕ}
    (c : Fin n → S.C) (c2 : Fin n2 → S.C) (c3 : Fin n3 → S.C )


/-- The permutation that arises from assocativity of `prod` node.
  This permutation is defined using braiding and composition with `finSumFinEquiv`
  based-isomorphisms. -/
def assocPerm :  OverColor.mk (Sum.elim c (Sum.elim c2 c3 ∘ ⇑finSumFinEquiv.symm) ∘ ⇑finSumFinEquiv.symm) ≅
    OverColor.mk (Sum.elim (Sum.elim c c2 ∘ ⇑finSumFinEquiv.symm) c3 ∘ ⇑finSumFinEquiv.symm) :=
  (equivToIso finSumFinEquiv).symm.trans <|
  (whiskerLeftIso  (OverColor.mk c) (equivToIso finSumFinEquiv).symm).trans <|
  (α_ (OverColor.mk c) (OverColor.mk c2) (OverColor.mk c3)).symm.trans <|
  (whiskerRightIso (equivToIso finSumFinEquiv) (OverColor.mk c3)).trans <|
  (equivToIso finSumFinEquiv)


/-- The arguments of a `prod` node can be commuted using braiding. -/
theorem prod_assoc (t : TensorTree S c) (t2 : TensorTree S c2) (t3 : TensorTree S c3) :
    (prod (prod t t2) t3).tensor = (perm (assocPerm c c2 c3).hom (prod t (prod t2 t3))).tensor := by
  sorry


end TensorTree
