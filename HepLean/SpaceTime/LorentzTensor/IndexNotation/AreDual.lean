/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Basic
/-!

# Indices which are dual in an index list

-/

namespace IndexNotation

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

/-!

## Are dual indices

-/

/-- Two indices are dual if they are not equivalent, but have the same id. -/
def AreDualInSelf (i j : Fin l.length) : Prop :=
    i ≠ j ∧ l.idMap i = l.idMap j

/-- Two indices in different `IndexLists` are dual to one another if they have the same `id`. -/
def AreDualInOther (i : Fin l.length) (j : Fin l2.length) :
    Prop := l.idMap i = l2.idMap j

namespace AreDualInSelf

variable {l l2 : IndexList X} {i j : Fin l.length}

instance (i j : Fin l.length) : Decidable (l.AreDualInSelf i j) :=
  instDecidableAnd

@[symm]
lemma symm (h : l.AreDualInSelf i j) : l.AreDualInSelf j i := by
  simp only [AreDualInSelf] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

@[simp]
lemma self_false (i : Fin l.length) : ¬ l.AreDualInSelf i i := by
  simp [AreDualInSelf]

@[simp]
lemma append_inl_inl : (l ++ l2).AreDualInSelf (appendEquiv (Sum.inl i)) (appendEquiv (Sum.inl j))
    ↔ l.AreDualInSelf i j := by
  simp [AreDualInSelf]

@[simp]
lemma append_inr_inr (l l2 : IndexList X) (i j : Fin l2.length) :
    (l ++ l2).AreDualInSelf (appendEquiv (Sum.inr i)) (appendEquiv (Sum.inr j))
    ↔ l2.AreDualInSelf i j := by
  simp [AreDualInSelf]

@[simp]
lemma append_inl_inr (l l2 : IndexList X) (i : Fin l.length) (j : Fin l2.length) :
    (l ++ l2).AreDualInSelf (appendEquiv (Sum.inl i)) (appendEquiv (Sum.inr j)) =
    l.AreDualInOther l2 i j := by
  simp [AreDualInSelf, AreDualInOther]

@[simp]
lemma append_inr_inl (l l2 : IndexList X) (i : Fin l2.length) (j : Fin l.length) :
    (l ++ l2).AreDualInSelf (appendEquiv (Sum.inr i)) (appendEquiv (Sum.inl j)) =
    l2.AreDualInOther l i j := by
  simp [AreDualInSelf, AreDualInOther]

end AreDualInSelf

namespace AreDualInOther

variable {l l2 l3 : IndexList X} {i : Fin l.length} {j : Fin l2.length}

instance {l : IndexList X} {l2 : IndexList X} (i : Fin l.length) (j : Fin l2.length) :
    Decidable (l.AreDualInOther l2 i j) := (l.idMap i).decEq (l2.idMap j)

@[symm]
lemma symm (h : l.AreDualInOther l2 i j) : l2.AreDualInOther l j i := by
  rw [AreDualInOther] at h ⊢
  exact h.symm

@[simp]
lemma append_of_inl (i : Fin l.length) (j : Fin l3.length) :
    (l ++ l2).AreDualInOther l3 (appendEquiv (Sum.inl i)) j ↔ l.AreDualInOther l3 i j := by
  simp [AreDualInOther]

@[simp]
lemma append_of_inr (i : Fin l2.length) (j : Fin l3.length) :
    (l ++ l2).AreDualInOther l3 (appendEquiv (Sum.inr i)) j ↔ l2.AreDualInOther l3 i j := by
  simp [AreDualInOther]

@[simp]
lemma of_append_inl (i : Fin l.length) (j : Fin l2.length) :
    l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inl j)) ↔ l.AreDualInOther l2 i j := by
  simp [AreDualInOther]

@[simp]
lemma of_append_inr (i : Fin l.length) (j : Fin l3.length) :
    l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inr j)) ↔ l.AreDualInOther l3 i j := by
  simp [AreDualInOther]

end AreDualInOther

end IndexList

end IndexNotation
