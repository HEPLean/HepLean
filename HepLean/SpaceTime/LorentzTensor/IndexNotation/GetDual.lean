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

def getDual? (i : Fin l.length) : Option (Fin l.length) :=
  Fin.find (fun j => i ≠ j ∧ l.idMap i = l.idMap j)

def getDualInOther? (i : Fin l.length) : Option (Fin l2.length) :=
  Fin.find (fun j => l.idMap i = l2.idMap j)

/-!

## Finite sets of duals

-/

def withDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isSome) Finset.univ

def withoutDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isNone) Finset.univ

def withDualOther : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDualInOther? l2 i).isSome) Finset.univ

def withoutDualOther : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDualInOther? l2 i).isNone) Finset.univ

lemma withDual_disjoint_withoutDual : Disjoint l.withDual l.withoutDual := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  by_contra hn
  subst hn
  simp_all only [withDual, Finset.mem_filter, Finset.mem_univ, true_and, withoutDual,
    Option.isNone_iff_eq_none, Option.isSome_none, Bool.false_eq_true]

lemma withDual_union_withoutDual : l.withDual ∪ l.withoutDual = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  by_cases h : (l.getDual? i).isSome
  · simp [withDual, Finset.mem_filter, Finset.mem_univ, h]
  · simp at h
    simp [withoutDual, Finset.mem_filter, Finset.mem_univ, h]

lemma withDualOther_disjoint_withoutDualOther :
    Disjoint (l.withDualOther l2) (l.withoutDualOther l2) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  by_contra hn
  subst hn
  simp_all only [withDualOther, Finset.mem_filter, Finset.mem_univ, true_and, withoutDualOther,
    Option.isNone_iff_eq_none, Option.isSome_none, Bool.false_eq_true]

lemma withDualOther_union_withoutDualOther :
    l.withDualOther l2 ∪ l.withoutDualOther l2 = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  by_cases h : (l.getDualInOther? l2 i).isSome
  · simp [withDualOther, Finset.mem_filter, Finset.mem_univ, h]
  · simp at h
    simp [withoutDualOther, Finset.mem_filter, Finset.mem_univ, h]

def dualEquiv : l.withDual ⊕ l.withoutDual ≃ Fin l.length :=
  (Equiv.Finset.union _ _ l.withDual_disjoint_withoutDual).trans <|
  Equiv.subtypeUnivEquiv (Finset.eq_univ_iff_forall.mp l.withDual_union_withoutDual)

def dualEquivOther : l.withDualOther l2 ⊕ l.withoutDualOther l2 ≃ Fin l.length :=
  (Equiv.Finset.union _ _ (l.withDualOther_disjoint_withoutDualOther l2)).trans
  (Equiv.subtypeUnivEquiv
    (Finset.eq_univ_iff_forall.mp (l.withDualOther_union_withoutDualOther l2)))

/-!

## Index lists where `getDual?` is invertiable.
-/

def InverDual : Prop :=
  ∀ i, (l.getDual? i).bind l.getDual? = some i

namespace InverDual

end InverDual

def InvertDualOther : Prop :=
  ∀ i, (l.getDualInOther? l2 i).bind (l2.getDualInOther? l) = some i
  ∧ ∀ i, (l2.getDualInOther? l i).bind (l.getDualInOther? l2) = some i

section Color

variable {𝓒 : TensorColor}
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
variable (l l2 : IndexList 𝓒.Color)
/-!

## Has single dual of correct color

-/

def IndexListColor (𝓒 : TensorColor) [IndexNotation 𝓒.Color] : Type := {l : IndexList X //
  ∀ i, (l.getDual? i).bind l.getDual? = some i ∧
  Option.map (l.colorMap) ∘ l.getDual? = Option.map ()
  }

end color
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

lemma hasSingDualsInSelf_append (h1 : l.HasNoDualsInSelf) (h2 : l2.HasNoDualsInSelf) :
    (l ++ l2).HasSingDualsInSelf ↔ HasSingDualsInOther l l2 := by
  apply Iff.intro
  · intro h
    simp [HasSingDualsInOther]
    apply And.intro
    · intro i
      have h3 := h (appendEquiv (Sum.inl i))
      simp at h3
      rw [h1] at h3
      simp at h3
      by_cases hn : l.HasDualInOther l2 i
      · rw [l.getDualOther_of_hasDualInOther l2 hn] at h3 ⊢
        simp only [Option.map_some', Function.comp_apply, Option.some_bind, getDual_append_inr] at h3
        rw [h2] at h3
        simpa using h3
      · rw [l.getDualOther_of_not_hasDualInOther l2 hn] at h3 ⊢
        simp at h3
    · intro i
      have h3 := h (appendEquiv (Sum.inr i))
      simp at h3
      rw [h2] at h3
      simp at h3
      by_cases hn : l2.HasDualInOther l i
      · rw [l2.getDualOther_of_hasDualInOther l hn] at h3 ⊢
        simp only [Option.map_some', Function.comp_apply, Option.some_bind, getDual_append_inl] at h3
        rw [h1] at h3
        simpa using h3
      · rw [l2.getDualOther_of_not_hasDualInOther l hn] at h3 ⊢
        simp at h3
  · intro h
    intro i
    obtain ⟨k, hk⟩ := appendEquiv.surjective i

    sorry

end IndexList

end IndexNotation
