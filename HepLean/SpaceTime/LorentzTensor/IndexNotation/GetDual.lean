/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.DualIndex
/-!

# Dual indices

-/

namespace IndexNotation


namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 : IndexList X)


def getDual (i : Fin l.length) : Option (Fin l.length) :=
  if h : l.HasDualInSelf i then
    some h.getFirst
  else
    none

lemma getDual_of_hasDualInSelf {i : Fin l.length} (h : l.HasDualInSelf i) :
    l.getDual i = some h.getFirst := by
  simp [getDual, h]

lemma getDual_of_not_hasDualInSelf {i : Fin l.length} (h :  ¬l.HasDualInSelf i) :
    l.getDual i = none := by
  simp [getDual, h]

def getDualOther (i : Fin l.length) : Option (Fin l2.length) :=
  if h : l.HasDualInOther l2 i then
    some h.getFirst
  else
    none

lemma getDualOther_of_hasDualInOther {i : Fin l.length} (h : l.HasDualInOther l2 i) :
    l.getDualOther l2 i = some h.getFirst := by
  simp [getDualOther, h]

lemma getDualOther_of_not_hasDualInOther {i : Fin l.length} (h :  ¬l.HasDualInOther l2 i) :
    l.getDualOther l2 i = none := by
  simp [getDualOther, h]

/-!

## Append relations

-/

@[simp]
lemma getDual_append_inl (i : Fin l.length) : (l ++ l2).getDual (appendEquiv (Sum.inl i)) =
    Option.or (Option.map (appendEquiv ∘ Sum.inl) (l.getDual i))
    (Option.map (appendEquiv ∘ Sum.inr) (l.getDualOther l2 i)) := by
  by_cases h : (l ++ l2).HasDualInSelf (appendEquiv (Sum.inl i))
  · rw [(l ++ l2).getDual_of_hasDualInSelf h]
    by_cases hl : l.HasDualInSelf i
    · rw [l.getDual_of_hasDualInSelf hl]
      simp
      exact HasDualInSelf.getFirst_append_inl_of_hasDualInSelf l l2 h hl
    · rw [l.getDual_of_not_hasDualInSelf hl]
      simp at h hl
      simp_all
      rw [l.getDualOther_of_hasDualInOther l2 h]
      simp only [Option.map_some', Function.comp_apply]
  · rw [(l ++ l2).getDual_of_not_hasDualInSelf h]
    simp at h
    rw [l.getDual_of_not_hasDualInSelf h.1]
    rw [l.getDualOther_of_not_hasDualInOther l2 h.2]
    rfl

@[simp]
lemma getDual_append_inr (i : Fin l2.length) : (l ++ l2).getDual (appendEquiv (Sum.inr i)) =
    Option.or (Option.map (appendEquiv ∘ Sum.inl) (l2.getDualOther l i))
    (Option.map (appendEquiv ∘ Sum.inr) (l2.getDual i)) := by
  by_cases h : (l ++ l2).HasDualInSelf (appendEquiv (Sum.inr i))
  · rw [(l ++ l2).getDual_of_hasDualInSelf h]
    by_cases hl1 : l2.HasDualInOther l i
    · rw [l2.getDualOther_of_hasDualInOther l hl1]
      simp
      exact HasDualInSelf.getFirst_append_inr_of_hasDualInOther l l2 h hl1
    · rw [l2.getDualOther_of_not_hasDualInOther l hl1]
      simp at h hl1
      simp_all
      rw [l2.getDual_of_hasDualInSelf h]
      simp only [Option.map_some', Function.comp_apply]
  · rw [(l ++ l2).getDual_of_not_hasDualInSelf h]
    simp at h
    rw [l2.getDual_of_not_hasDualInSelf h.1]
    rw [l2.getDualOther_of_not_hasDualInOther l h.2]
    rfl

def HasSingDualsInSelf : Prop :=
  ∀ i, (l.getDual i).bind l.getDual = some i

def HasSingDualsInOther : Prop :=
  (∀ i, (l.getDualOther l2 i).bind (l2.getDualOther l) = some i)
  ∧ (∀ i, (l2.getDualOther l i).bind (l.getDualOther l2) = some i)

def HasNoDualsInSelf : Prop := l.getDual = fun _ => none

lemma hasSingDualsInSelf_append :
    (l ++ l2).HasSingDualsInSelf ↔
    l.HasSingDualsInSelf ∧ l2.HasSingDualsInSelf ∧ HasSingDualsInOther l1 l2 := by
  sorry
end IndexList

end IndexNotation
