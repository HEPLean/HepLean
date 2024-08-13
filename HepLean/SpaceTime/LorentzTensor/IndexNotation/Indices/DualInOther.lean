/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.Basic
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Dual in other list

-/
namespace IndexNotation


namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 : IndexList X)

def AreDualInOther  (i : Fin l.length) (j : Fin l2.length) :
    Prop := l.idMap i = l2.idMap j

instance {l : IndexList X} {l2 : IndexList X}  (i : Fin l.length) (j : Fin l2.length) :
    Decidable (l.AreDualInOther l2 i j) := (l.idMap i).decEq (l2.idMap j)

namespace AreDualInOther

variable {l l2 : IndexList X} {i : Fin l.length} {j : Fin l2.length}

@[symm]
lemma symm  (h : l.AreDualInOther l2 i j) : l2.AreDualInOther l j i := by
  rw [AreDualInOther] at h ⊢
  exact h.symm

end AreDualInOther

/-- Given an `i`, if a dual exists in the other list,
   outputs the first such dual, otherwise outputs `none`. -/
def getDualInOther? (i : Fin l.length) : Option (Fin l2.length) :=
  Fin.find (fun j => l.AreDualInOther l2 i j)


/-!

## With dual other.

-/

def withDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDualInOther? l2 i).isSome) Finset.univ

@[simp]
lemma mem_withInDualOther_iff_isSome (i : Fin l.length) :
    i ∈ l.withDualInOther l2 ↔ (l.getDualInOther? l2 i).isSome := by
  simp only [withDualInOther, getDualInOther?, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_withInDualOther_iff_exists :
    i ∈ l.withDualInOther l2 ↔ ∃ (j : Fin l2.length), l.AreDualInOther l2 i j := by
  simp [withDualInOther, Finset.mem_filter, Finset.mem_univ, getDualInOther?]
  rw [Fin.isSome_find_iff]

def getDualInOther! (i : l.withDualInOther l2) : Fin l2.length :=
  (l.getDualInOther? l2 i).get (by simpa [withDualInOther] using i.2)


lemma getDualInOther?_eq_some_getDualInOther! (i : l.withDualInOther l2) :
    l.getDualInOther? l2 i = some (l.getDualInOther! l2 i) := by
  simp [getDualInOther!]

lemma getDualInOther?_eq_none_on_not_mem (i : Fin l.length) (h : i ∉ l.withDualInOther l2) :
    l.getDualInOther? l2 i = none := by
  simpa [getDualInOther?, Fin.find_eq_none_iff, mem_withInDualOther_iff_exists]  using h


lemma areDualInOther_getDualInOther! (i : l.withDualInOther l2) :
    l.AreDualInOther l2 i (l.getDualInOther! l2 i) := by
  have h := l.getDualInOther?_eq_some_getDualInOther! l2 i
  rw [getDualInOther?, Fin.find_eq_some_iff] at h
  exact h.1

@[simp]
lemma getDualInOther!_id (i : l.withDualInOther l2) :
    l2.idMap (l.getDualInOther! l2 i) = l.idMap i := by
  simpa using (l.areDualInOther_getDualInOther! l2 i).symm

lemma getDualInOther_mem_withDualInOther (i : l.withDualInOther l2) :
    l.getDualInOther! l2 i ∈ l2.withDualInOther l :=
  (l2.mem_withInDualOther_iff_exists l).mpr ⟨i, (areDualInOther_getDualInOther! l l2 i).symm⟩

def getDualInOther (i : l.withDualInOther l2) : l2.withDualInOther l :=
  ⟨l.getDualInOther! l2 i, l.getDualInOther_mem_withDualInOther l2 i⟩

@[simp]
lemma getDualInOther_id (i : l.withDualInOther l2) :
    l2.idMap (l.getDualInOther l2 i) = l.idMap i := by
  simp [getDualInOther]

lemma getDualInOther_coe (i : l.withDualInOther l2) :
    (l.getDualInOther l2 i).1 = l.getDualInOther! l2 i := by
  rfl

end IndexList

end IndexNotation
