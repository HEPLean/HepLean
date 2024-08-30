/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.Basic
/-!

# Indices which are dual in an index list

Given an list of indices we say two indices are dual if they have the same id.

For example the `0`, `2` and `3` index in `l₁ := ['ᵘ¹', 'ᵘ²', 'ᵤ₁', 'ᵘ¹']` are pairwise dual to
  one another. The `1` (`'ᵘ²'`) index is not dual to any other index in the list.

We also define the notion of dual indices in different lists. For example,
  the `1` index in `l₁` is dual to the `1` and the `4` indices in
  `l₂ := ['ᵘ³', 'ᵘ²', 'ᵘ⁴', 'ᵤ₂']`.

-/

namespace IndexNotation

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

/-!

## Definitions

-/

/-- Two indices are dual if they are not equivalent, but have the same id. -/
def AreDualInSelf (i j : Fin l.length) : Prop :=
    i ≠ j ∧ l.idMap i = l.idMap j

instance (i j : Fin l.length) : Decidable (l.AreDualInSelf i j) :=
  instDecidableAnd

/-- Two indices in different `IndexLists` are dual to one another if they have the same `id`. -/
def AreDualInOther (i : Fin l.length) (j : Fin l2.length) :
    Prop := l.idMap i = l2.idMap j

instance {l : IndexList X} {l2 : IndexList X} (i : Fin l.length) (j : Fin l2.length) :
    Decidable (l.AreDualInOther l2 i j) := (l.idMap i).decEq (l2.idMap j)

/-- Given an `i`, if a dual exists in the same list,
    outputs the first such dual, otherwise outputs `none`. -/
def getDual? (i : Fin l.length) : Option (Fin l.length) :=
  Fin.find (fun j => l.AreDualInSelf i j)

/-- Given an `i`, if a dual exists in the other list,
    outputs the first such dual, otherwise outputs `none`. -/
def getDualInOther? (i : Fin l.length) : Option (Fin l2.length) :=
  Fin.find (fun j => l.AreDualInOther l2 i j)

/-- The finite set of indices of an index list which have a dual in that index list. -/
def withDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isSome) Finset.univ

/-- The finite set of indices of an index list which do not have a dual. -/
def withoutDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isNone) Finset.univ

/-- The finite set of indices of an index list which have a dual in another provided index list. -/
def withDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDualInOther? l2 i).isSome) Finset.univ

/-- The finite set of indices of an index list which have a unique dual in that index list. -/
def withUniqueDual : Finset (Fin l.length) :=
  Finset.filter (fun i => i ∈ l.withDual ∧
    ∀ j, l.AreDualInSelf i j → j = l.getDual? i) Finset.univ

instance (i j : Option (Fin l.length)) : Decidable (i < j) :=
  match i, j with
  | none, none => isFalse (fun a => a)
  | none, some _ => isTrue (by trivial)
  | some _, none => isFalse (fun a => a)
  | some i, some j => Fin.decLt i j

/-- The finite set of those indices of `l` which have a unique dual, and for which
  that dual is greater-then (determined by the ordering on `Fin`) then the index itself. -/
def withUniqueDualLT : Finset (Fin l.length) :=
  Finset.filter (fun i => i < l.getDual? i) l.withUniqueDual

/-- The finite set of those indices of `l` which have a unique dual, and for which
  that dual is less-then (determined by the ordering on `Fin`) then the index itself. -/
def withUniqueDualGT : Finset (Fin l.length) :=
  Finset.filter (fun i => ¬ i < l.getDual? i) l.withUniqueDual

/-- The finite set of indices of an index list which have a unique dual in another, provided, index
  list. -/
def withUniqueDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => i ∉ l.withDual ∧ i ∈ l.withDualInOther l2
    ∧ (∀ j, l.AreDualInOther l2 i j → j = l.getDualInOther? l2 i)) Finset.univ

/-!

## Basic properties

-/

@[simp, nolint simpNF]
lemma mem_withDual_of_mem_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    i ∈ l.withDual := by
  simp only [withUniqueDual, Finset.mem_filter, Finset.mem_univ, true_and] at h
  simpa using h.1

lemma mem_withDual_of_withUniqueDual (i : l.withUniqueDual) :
    i.1 ∈ l.withDual :=
  mem_withDual_of_mem_withUniqueDual l (↑i) i.2

lemma not_mem_withDual_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    i.1 ∉ l.withDual := by
  have hi := i.2
  simp only [withUniqueDualInOther, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
    true_and] at hi
  exact hi.2.1

lemma mem_withDualInOther_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    i.1 ∈ l.withDualInOther l2 := by
  have hi := i.2
  simp only [withUniqueDualInOther, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
    true_and] at hi
  exact hi.2.2.1

@[simp]
lemma withDual_isSome (i : l.withDual) : (l.getDual? i).isSome := by
  simpa [withDual] using i.2

@[simp]
lemma mem_withDual_iff_isSome (i : Fin l.length) : i ∈ l.withDual ↔ (l.getDual? i).isSome := by
  simp [withDual]

@[simp]
lemma mem_withUniqueDual_isSome (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    (l.getDual? i).isSome := by
  simpa [withDual] using mem_withDual_of_mem_withUniqueDual l i h

@[simp]
lemma mem_withInDualOther_iff_isSome (i : Fin l.length) :
    i ∈ l.withDualInOther l2 ↔ (l.getDualInOther? l2 i).isSome := by
  simp only [withDualInOther, getDualInOther?, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp]
lemma mem_withUniqueDualInOther_isSome (i : Fin l.length) (hi : i ∈ l.withUniqueDualInOther l2) :
    (l.getDualInOther? l2 i).isSome := by
  simp only [withUniqueDualInOther, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact (mem_withInDualOther_iff_isSome l l2 i).mp hi.2.1

lemma not_mem_withDual_iff_isNone (i : Fin l.length) :
    i ∉ l.withDual ↔ (l.getDual? i).isNone := by
  simp only [mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none]

lemma mem_withDual_iff_exists : i ∈ l.withDual ↔ ∃ j, l.AreDualInSelf i j := by
  simp [withDual, Finset.mem_filter, Finset.mem_univ, getDual?]
  exact Fin.isSome_find_iff

lemma mem_withInDualOther_iff_exists :
    i ∈ l.withDualInOther l2 ↔ ∃ (j : Fin l2.length), l.AreDualInOther l2 i j := by
  simp [withDualInOther, Finset.mem_filter, Finset.mem_univ, getDualInOther?]
  exact Fin.isSome_find_iff

lemma withDual_disjoint_withoutDual : Disjoint l.withDual l.withoutDual := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  by_contra hn
  subst hn
  simp_all only [withDual, Finset.mem_filter, Finset.mem_univ, true_and, withoutDual,
    Option.isNone_iff_eq_none, Option.isSome_none, Bool.false_eq_true]

lemma not_mem_withDual_of_mem_withoutDual (i : Fin l.length) (h : i ∈ l.withoutDual) :
    i ∉ l.withDual := by
  have h1 := l.withDual_disjoint_withoutDual
  exact Finset.disjoint_right.mp h1 h

lemma withDual_union_withoutDual : l.withDual ∪ l.withoutDual = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  by_cases h : (l.getDual? i).isSome
  · simp [withDual, Finset.mem_filter, Finset.mem_univ, h]
  · simp at h
    simp [withoutDual, Finset.mem_filter, Finset.mem_univ, h]

lemma mem_withUniqueDual_of_mem_withUniqueDualLt (i : Fin l.length) (h : i ∈ l.withUniqueDualLT) :
    i ∈ l.withUniqueDual := by
  simp only [withUniqueDualLT, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.1

lemma mem_withUniqueDual_of_mem_withUniqueDualGt (i : Fin l.length) (h : i ∈ l.withUniqueDualGT) :
    i ∈ l.withUniqueDual := by
  simp only [withUniqueDualGT, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.1

lemma withUniqueDualLT_disjoint_withUniqueDualGT :
    Disjoint l.withUniqueDualLT l.withUniqueDualGT := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact @Finset.filter_inter_filter_neg_eq (Fin l.length) _ _ _ _ _

lemma withUniqueDualLT_union_withUniqueDualGT :
    l.withUniqueDualLT ∪ l.withUniqueDualGT = l.withUniqueDual :=
  Finset.filter_union_filter_neg_eq _ _
/-!
## Are dual properties
-/

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

/-!

## Basic properties of getDual?

-/

lemma getDual?_isSome_iff_exists (i : Fin l.length) :
    (l.getDual? i).isSome ↔ ∃ j, l.AreDualInSelf i j := by
  rw [getDual?, Fin.isSome_find_iff]

lemma getDual?_of_areDualInSelf (h : l.AreDualInSelf i j) :
    l.getDual? j = i ∨ l.getDual? i = j ∨ l.getDual? j = l.getDual? i := by
  have h3 : (l.getDual? i).isSome := by
    simpa [getDual?, Fin.isSome_find_iff] using ⟨j, h⟩
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp h3
  rw [hk]
  rw [getDual?, Fin.find_eq_some_iff] at hk
  by_cases hik : i < k
  · apply Or.inl
    rw [getDual?, Fin.find_eq_some_iff]
    apply And.intro h.symm
    intro k' hk'
    by_cases hik' : i = k'
    · exact Fin.ge_of_eq (id (Eq.symm hik'))
    · have hik'' : l.AreDualInSelf i k' := by
        simp [AreDualInSelf, hik']
        simp_all [AreDualInSelf]
      have hk'' := hk.2 k' hik''
      exact (lt_of_lt_of_le hik hk'').le
  · by_cases hjk : j ≤ k
    · apply Or.inr
      apply Or.inl
      have hj := hk.2 j h
      simp only [Option.some.injEq]
      exact Fin.le_antisymm hj hjk
    · apply Or.inr
      apply Or.inr
      rw [getDual?, Fin.find_eq_some_iff]
      apply And.intro
      · simp_all [AreDualInSelf]
        exact Fin.ne_of_gt hjk
      intro k' hk'
      by_cases hik' : i = k'
      · subst hik'
        exact Lean.Omega.Fin.le_of_not_lt hik
      · have hik'' : l.AreDualInSelf i k' := by
          simp [AreDualInSelf, hik']
          simp_all [AreDualInSelf]
        exact hk.2 k' hik''

@[simp]
lemma getDual?_neq_self (i : Fin l.length) : ¬ l.getDual? i = some i := by
  intro h
  simp [getDual?] at h
  rw [Fin.find_eq_some_iff] at h
  simp [AreDualInSelf] at h

@[simp]
lemma getDual?_get_neq_self (i : Fin l.length) (h : (l.getDual? i).isSome) :
    ¬ (l.getDual? i).get h = i := by
  have h1 := l.getDual?_neq_self i
  by_contra hn
  have h' : l.getDual? i = some i := by
    nth_rewrite 2 [← hn]
    exact Option.eq_some_of_isSome h
  exact h1 h'

@[simp]
lemma getDual?_get_id (i : Fin l.length) (h : (l.getDual? i).isSome) :
    l.idMap ((l.getDual? i).get h) = l.idMap i := by
  have h1 : l.getDual? i = some ((l.getDual? i).get h) := Option.eq_some_of_isSome h
  nth_rewrite 1 [getDual?] at h1
  rw [Fin.find_eq_some_iff] at h1
  simp [AreDualInSelf] at h1
  exact h1.1.2.symm

@[simp]
lemma getDual?_get_areDualInSelf (i : Fin l.length) (h : (l.getDual? i).isSome) :
    l.AreDualInSelf ((l.getDual? i).get h) i := by
  simp [AreDualInSelf]

@[simp]
lemma getDual?_areDualInSelf_get (i : Fin l.length) (h : (l.getDual? i).isSome) :
    l.AreDualInSelf i ((l.getDual? i).get h) :=
  AreDualInSelf.symm (getDual?_get_areDualInSelf l i h)

@[simp]
lemma getDual?_getDual?_get_isSome (i : Fin l.length) (h : (l.getDual? i).isSome) :
    (l.getDual? ((l.getDual? i).get h)).isSome := by
  rw [getDual?, Fin.isSome_find_iff]
  exact ⟨i, getDual?_get_areDualInSelf l i h⟩

/-!

## Basic properties of getDualInOther?

-/

lemma getDualInOther?_isSome_iff_exists (i : Fin l.length) :
    (l.getDualInOther? l2 i).isSome ↔ ∃ j, l.AreDualInOther l2 i j := by
  rw [getDualInOther?, Fin.isSome_find_iff]

@[simp]
lemma getDualInOther?_id (i : Fin l.length) (h : (l.getDualInOther? l2 i).isSome) :
    l2.idMap ((l.getDualInOther? l2 i).get h) = l.idMap i := by
  have h1 : l.getDualInOther? l2 i = some ((l.getDualInOther? l2 i).get h) :=
    Option.eq_some_of_isSome h
  nth_rewrite 1 [getDualInOther?] at h1
  rw [Fin.find_eq_some_iff] at h1
  simp [AreDualInOther] at h1
  exact h1.1.symm

@[simp]
lemma getDualInOther?_get_areDualInOther (i : Fin l.length) (h : (l.getDualInOther? l2 i).isSome) :
    l2.AreDualInOther l ((l.getDualInOther? l2 i).get h) i := by
  simp [AreDualInOther]

@[simp]
lemma getDualInOther?_areDualInOther_get (i : Fin l.length) (h : (l.getDualInOther? l2 i).isSome) :
    l.AreDualInOther l2 i ((l.getDualInOther? l2 i).get h) :=
  AreDualInOther.symm (getDualInOther?_get_areDualInOther l l2 i h)

@[simp]
lemma getDualInOther?_getDualInOther?_get_isSome (i : Fin l.length)
    (h : (l.getDualInOther? l2 i).isSome) :
    (l2.getDualInOther? l ((l.getDualInOther? l2 i).get h)).isSome := by
  rw [getDualInOther?, Fin.isSome_find_iff]
  exact ⟨i, getDualInOther?_get_areDualInOther l l2 i h⟩

@[simp]
lemma getDualInOther?_self_isSome (i : Fin l.length) :
    (l.getDualInOther? l i).isSome := by
  simp [getDualInOther?]
  rw [@Fin.isSome_find_iff]
  exact ⟨i, rfl⟩

@[simp]
lemma getDualInOther?_getDualInOther?_get_self (i : Fin l.length) :
    l.getDualInOther? l ((l.getDualInOther? l i).get (getDualInOther?_self_isSome l i)) =
    some ((l.getDualInOther? l i).get (getDualInOther?_self_isSome l i)) := by
  nth_rewrite 1 [getDualInOther?]
  rw [Fin.find_eq_some_iff]
  simp [AreDualInOther]
  intro j hj
  have h1 := Option.eq_some_of_isSome (getDualInOther?_self_isSome l i)
  nth_rewrite 1 [getDualInOther?] at h1
  rw [Fin.find_eq_some_iff] at h1
  apply h1.2 j
  simpa [AreDualInOther] using hj



end IndexList

end IndexNotation
