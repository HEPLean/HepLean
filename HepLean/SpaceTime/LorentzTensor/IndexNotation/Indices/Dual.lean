/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.Basic
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Dual indices

-/

namespace IndexNotation


namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 : IndexList X)

/-!

## Are dual indices

-/

/-- Two indices are dual if they are not equivalent, but have the same id. -/
def AreDualInSelf (i j : Fin l.length) : Prop :=
    i ≠ j ∧ l.idMap i = l.idMap j

def AreDualInOther  (i : Fin l.length) (j : Fin l2.length) :
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

instance {l : IndexList X} {l2 : IndexList X}  (i : Fin l.length) (j : Fin l2.length) :
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
lemma append_of_inr (i : Fin l2.length)  (j : Fin l3.length) :
    (l ++ l2).AreDualInOther l3 (appendEquiv (Sum.inr i)) j ↔ l2.AreDualInOther l3 i j := by
  simp [AreDualInOther]

@[simp]
lemma of_append_inl (i : Fin l.length)  (j : Fin l2.length) :
    l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inl j)) ↔ l.AreDualInOther l2 i j := by
  simp [AreDualInOther]

@[simp]
lemma of_append_inr (i : Fin l.length)  (j : Fin l3.length) :
    l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inr j)) ↔ l.AreDualInOther l3 i j := by
  simp [AreDualInOther]

end AreDualInOther

/-!

## The getDual? Function

-/

/-- Given an `i`, if a dual exists in the same list,
   outputs the first such dual, otherwise outputs `none`. -/
def getDual? (i : Fin l.length) : Option (Fin l.length) :=
  Fin.find (fun j => l.AreDualInSelf i j)


/-- Given an `i`, if a dual exists in the other list,
   outputs the first such dual, otherwise outputs `none`. -/
def getDualInOther? (i : Fin l.length) : Option (Fin l2.length) :=
  Fin.find (fun j => l.AreDualInOther l2 i j)


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
    subst hik'
    rfl
    have hik'' :  l.AreDualInSelf i k' := by
      simp [AreDualInSelf, hik']
      simp_all [AreDualInSelf]
    have hk'' := hk.2 k' hik''
    exact (lt_of_lt_of_le hik hk'').le
  · by_cases hjk : j ≤ k
    · apply Or.inr
      apply Or.inl
      have hj := hk.2 j h
      simp
      omega
    · apply Or.inr
      apply Or.inr
      rw [getDual?, Fin.find_eq_some_iff]
      apply And.intro
      · simp_all [AreDualInSelf]
        exact Fin.ne_of_gt hjk
      intro k' hk'
      by_cases hik' : i = k'
      subst hik'
      exact Lean.Omega.Fin.le_of_not_lt hik
      have hik'' :  l.AreDualInSelf i k' := by
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
    simp
  exact h1 h'

@[simp]
lemma getDual?_get_id (i : Fin l.length) (h : (l.getDual? i).isSome) :
    l.idMap ((l.getDual? i).get h) = l.idMap i := by
  have h1 : l.getDual? i = some ((l.getDual? i).get h) := by simp
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
    l.AreDualInSelf i ((l.getDual? i).get h):= by
  symm
  simp

@[simp]
lemma getDual?_getDual?_get_isSome (i : Fin l.length) (h : (l.getDual? i).isSome) :
    (l.getDual? ((l.getDual? i).get h)).isSome := by
  rw [getDual?, Fin.isSome_find_iff]
  exact ⟨i, by simp⟩

/-!

## Basic properties of getDualInOther?

-/

lemma getDualInOther?_isSome_iff_exists (i : Fin l.length) :
    (l.getDualInOther? l2 i).isSome ↔ ∃ j, l.AreDualInOther l2 i j := by
  rw [getDualInOther?, Fin.isSome_find_iff]

@[simp]
lemma getDualInOther?_id (i : Fin l.length) (h : (l.getDualInOther? l2 i).isSome) :
    l2.idMap ((l.getDualInOther? l2 i).get h) = l.idMap i := by
  have h1 : l.getDualInOther? l2 i = some ((l.getDualInOther? l2 i).get h) := by simp
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
    l.AreDualInOther l2 i ((l.getDualInOther? l2 i).get h) := by
  simp [AreDualInOther]

@[simp]
lemma getDualInOther?_getDualInOther?_get_isSome (i : Fin l.length)
    (h : (l.getDualInOther? l2 i).isSome) :
    (l2.getDualInOther? l ((l.getDualInOther? l2 i).get h)).isSome := by
  rw [getDualInOther?, Fin.isSome_find_iff]
  exact ⟨i, by simp⟩

@[simp]
lemma getDualInOther?_self_isSome (i : Fin l.length) :
    (l.getDualInOther? l i).isSome := by
  simp [getDualInOther?]
  rw [@Fin.isSome_find_iff]
  use i
  simp [AreDualInOther]

/-!

## Append properties of getDual?

-/

@[simp]
lemma getDual?_isSome_append_inl_iff (i : Fin l.length) :
    ((l ++ l2).getDual? (appendEquiv (Sum.inl i))).isSome ↔
    (l.getDual? i).isSome ∨ (l.getDualInOther? l2 i).isSome := by
  rw [getDual?_isSome_iff_exists, getDual?_isSome_iff_exists, getDualInOther?_isSome_iff_exists]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨j, hj⟩ := h
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      exact Or.inl ⟨k, by simpa using hj⟩
    | Sum.inr k =>
      exact Or.inr ⟨k, by simpa using hj⟩
  · cases' h with h h <;>
      obtain ⟨j, hj⟩ := h
    · use appendEquiv (Sum.inl j)
      simpa using hj
    · use appendEquiv (Sum.inr j)
      simpa using hj

@[simp]
lemma getDual?_isSome_append_inr_iff (i : Fin l2.length) :
    ((l ++ l2).getDual? (appendEquiv (Sum.inr i))).isSome ↔
    (l2.getDual? i).isSome ∨ (l2.getDualInOther? l i).isSome  := by
  rw [getDual?_isSome_iff_exists, getDual?_isSome_iff_exists, getDualInOther?_isSome_iff_exists]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨j, hj⟩ := h
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      exact Or.inr ⟨k, by simpa using hj⟩
    | Sum.inr k =>
      exact Or.inl ⟨k, by simpa using hj⟩
  · cases' h with h h <;>
      obtain ⟨j, hj⟩ := h
    · use appendEquiv (Sum.inr j)
      simpa using hj
    · use appendEquiv (Sum.inl j)
      simpa using hj

lemma getDual?_isSome_append_symm (i : Fin l.length) :
    ((l ++ l2).getDual? (appendEquiv (Sum.inl i))).isSome ↔
    ((l2 ++ l).getDual? (appendEquiv (Sum.inr i))).isSome := by
  simp

@[simp]
lemma getDual?_eq_none_append_inl_iff (i : Fin l.length) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = none ↔
    l.getDual? i = none ∧ l.getDualInOther? l2 i = none := by
  apply Iff.intro
  · intro h
    have h1 := (l.getDual?_isSome_append_inl_iff l2 i).mpr.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h
  · intro h
    have h1 := (l.getDual?_isSome_append_inl_iff l2 i).mp.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h

@[simp]
lemma getDual?_eq_none_append_inr_iff  (i : Fin l2.length) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = none ↔
    (l2.getDual? i = none ∧ l2.getDualInOther? l i = none) := by
  apply Iff.intro
  · intro h
    have h1 := (l.getDual?_isSome_append_inr_iff l2 i).mpr.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h
  · intro h
    have h1 := (l.getDual?_isSome_append_inr_iff l2 i).mp.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h

@[simp]
lemma getDual?_append_inl_of_getDual?_isSome (i : Fin l.length) (h : (l.getDual? i).isSome) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) =
    some (appendEquiv (Sum.inl ((l.getDual? i).get h))) := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inl_inl]
  apply And.intro (getDual?_get_areDualInSelf l i h).symm
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, ge_iff_le]
    rw [Fin.le_def]
    have h2 : l.getDual? i = some (((l.getDual? i).get h)) := by simp
    nth_rewrite 1 [getDual?] at h2
    rw [Fin.find_eq_some_iff] at h2
    exact h2.2 k (by simpa using hj)
  | Sum.inr k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, finSumFinEquiv_apply_right, ge_iff_le]
    rw [Fin.le_def]
    simp only [length, append_val, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd]
    omega

@[simp]
lemma getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome (i : Fin l.length)
    (hi : (l.getDual? i).isNone) (h : (l.getDualInOther? l2 i).isSome) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = some
    (appendEquiv (Sum.inr ((l.getDualInOther? l2 i).get h)))  := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inl_inr]
  apply And.intro
  simp
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    rw [AreDualInSelf.append_inl_inl] at hj
    simp only [getDual?, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true,
      Option.not_isSome, Option.isNone_iff_eq_none, Fin.find_eq_none_iff] at hi
    exact False.elim (hi k hj)
  | Sum.inr k =>
    simp [appendEquiv]
    rw [Fin.le_def]
    have h1 : l.getDualInOther? l2 i = some (((l.getDualInOther? l2 i).get h)) := by simp
    nth_rewrite 1 [getDualInOther?] at h1
    rw [Fin.find_eq_some_iff] at h1
    simp only [length, append_val, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
      Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le, ge_iff_le]
    refine h1.2 k (by simpa using hj)

lemma getDual?_append_inl (i : Fin l.length) : (l ++ l2).getDual? (appendEquiv (Sum.inl i)) =
    Option.or (Option.map (appendEquiv ∘ Sum.inl) (l.getDual? i))
    (Option.map (appendEquiv ∘ Sum.inr) (l.getDualInOther? l2 i)) := by
  by_cases h : (l.getDual? i).isSome
  · simp_all
    rw [congrArg (Option.map (appendEquiv ∘ Sum.inl)) (Option.eq_some_of_isSome h)]
    rfl
  by_cases ho : (l.getDualInOther? l2 i).isSome
  · simp_all
    rw [congrArg (Option.map (appendEquiv ∘ Sum.inr)) (Option.eq_some_of_isSome ho)]
    rfl
  simp_all

@[simp]
lemma getDual?_append_inr_getDualInOther?_isSome (i : Fin l2.length)
    (h : (l2.getDualInOther? l i).isSome) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) =
    some (appendEquiv (Sum.inl ((l2.getDualInOther? l i).get h))) := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inr_inl]
  apply And.intro
  simp
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, ge_iff_le]
    rw [Fin.le_def]
    have h1 : l2.getDualInOther? l i = some (((l2.getDualInOther? l i).get h)) := by simp
    nth_rewrite 1 [getDualInOther?] at h1
    rw [Fin.find_eq_some_iff] at h1
    simp only [Fin.coe_cast, Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le, ge_iff_le]
    refine h1.2 k (by simpa using hj)
  | Sum.inr k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, finSumFinEquiv_apply_right, ge_iff_le]
    rw [Fin.le_def]
    simp only [length, append_val, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd]
    omega

@[simp]
lemma getDual?_inr_getDualInOther?_isNone_getDual?_isSome (i : Fin l2.length)
    (h : (l2.getDualInOther? l i).isNone) (hi : (l2.getDual? i).isSome) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = some
    (appendEquiv (Sum.inr ((l2.getDual? i).get hi))) := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inr_inr]
  apply And.intro
  simp
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp at hj
    simp only [getDualInOther?, Option.isNone_iff_eq_none, Fin.find_eq_none_iff] at h
    exact False.elim (h k hj)
  | Sum.inr k =>
    simp [appendEquiv, IndexList.length]
    rw [Fin.le_def]
    simp
    have h2 : l2.getDual? i = some ((l2.getDual? i).get hi) := by simp
    nth_rewrite 1 [getDual?] at h2
    rw [Fin.find_eq_some_iff] at h2
    simp only [AreDualInSelf.append_inr_inr] at hj
    exact h2.2 k hj

lemma getDual?_append_inr (i : Fin l2.length) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) =
    Option.or (Option.map (appendEquiv ∘ Sum.inl) (l2.getDualInOther? l i))
    (Option.map (appendEquiv ∘ Sum.inr) (l2.getDual? i)) := by
  by_cases h : (l2.getDualInOther? l i).isSome
  · simp_all
    rw [congrArg (Option.map (appendEquiv ∘ Sum.inl)) (Option.eq_some_of_isSome h)]
    rfl
  by_cases ho : (l2.getDual? i).isSome
  · simp_all
    rw [congrArg (Option.map (appendEquiv ∘ Sum.inr)) (Option.eq_some_of_isSome ho)]
    rfl
  simp_all

/-!

## Properties of getDualInOther? and append

-/
variable (l3 : IndexList X)

@[simp]
lemma getDualInOther?_append_of_inl (i : Fin l.length) :
    (l ++ l2).getDualInOther? l3 (appendEquiv (Sum.inl i)) = l.getDualInOther? l3 i := by
  simp [getDualInOther?]

@[simp]
lemma getDualInOther?_append_of_inr (i : Fin l2.length) :
    (l ++ l2).getDualInOther? l3 (appendEquiv (Sum.inr i)) = l2.getDualInOther? l3 i := by
  simp [getDualInOther?]

@[simp]
lemma getDualInOther?_isSome_of_append_iff (i : Fin l.length) :
    (l.getDualInOther? (l2 ++ l3) i).isSome ↔
    (l.getDualInOther? l2 i).isSome ∨ (l.getDualInOther? l3 i).isSome := by
  rw [getDualInOther?_isSome_iff_exists, getDualInOther?_isSome_iff_exists,
    getDualInOther?_isSome_iff_exists]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · obtain ⟨j, hj⟩ := h
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      exact Or.inl ⟨k, by simpa using hj⟩
    | Sum.inr k =>
      exact Or.inr ⟨k, by simpa using hj⟩
  · cases' h with h h <;>
      obtain ⟨j, hj⟩ := h
    · use appendEquiv (Sum.inl j)
      simpa using hj
    · use appendEquiv (Sum.inr j)
      simpa using hj

@[simp]
lemma getDualInOther?_eq_none_of_append_iff (i : Fin l.length) :
    (l.getDualInOther? (l2 ++ l3) i) = none ↔
    (l.getDualInOther? l2 i) = none ∧ (l.getDualInOther? l3 i) = none := by
  apply Iff.intro
  · intro h
    have h1 := (l.getDualInOther?_isSome_of_append_iff l2 l3 i).mpr.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h
  · intro h
    have h1 := (l.getDualInOther?_isSome_of_append_iff l2 l3 i).mp.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h

@[simp]
lemma getDualInOther?_of_append_of_isSome (i : Fin l.length)
    (hi : (l.getDualInOther? l2 i).isSome) : l.getDualInOther? (l2 ++ l3) i =
    some (appendEquiv (Sum.inl ((l.getDualInOther? l2 i).get hi))) := by
  rw [getDualInOther?, Fin.find_eq_some_iff, AreDualInOther.of_append_inl]
  apply And.intro
  simp
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, ge_iff_le]
    rw [Fin.le_def]
    have h1 : l.getDualInOther? l2 i = some (((l.getDualInOther? l2 i).get hi)) := by simp
    nth_rewrite 1 [getDualInOther?] at h1
    rw [Fin.find_eq_some_iff] at h1
    simp only [Fin.coe_cast, Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le, ge_iff_le]
    refine h1.2 k (by simpa using hj)
  | Sum.inr k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, finSumFinEquiv_apply_right, ge_iff_le]
    rw [Fin.le_def]
    simp only [length, append_val, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
      Fin.coe_castAdd, Fin.coe_natAdd]
    omega

@[simp]
lemma getDualInOther?_of_append_of_isNone_isSome (i : Fin l.length)
    (hi : (l.getDualInOther? l2 i) = none) (h2 : (l.getDualInOther? l3 i).isSome) :
    l.getDualInOther? (l2 ++ l3) i =
    some (appendEquiv (Sum.inr ((l.getDualInOther? l3 i).get h2))) := by
  rw [getDualInOther?, Fin.find_eq_some_iff, AreDualInOther.of_append_inr]
  apply And.intro
  simp
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp at hj
    simp only [getDualInOther?, Option.isNone_iff_eq_none, Fin.find_eq_none_iff] at hi
    exact False.elim (hi k hj)
  | Sum.inr k =>
    simp [appendEquiv, IndexList.length]
    rw [Fin.le_def]
    simp
    have h1 : l.getDualInOther? l3 i = some ((l.getDualInOther? l3 i).get h2) := by simp
    nth_rewrite 1 [getDualInOther?] at h1
    rw [Fin.find_eq_some_iff] at h1
    simp only [AreDualInOther.of_append_inr] at hj
    exact h1.2 k hj

/-!

## Finsets on which getDual? and getDualInOther? are some.

-/

def withDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isSome) Finset.univ

def withDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDualInOther? l2 i).isSome) Finset.univ

/-!

## Basic properties of withDual

-/

@[simp]
lemma withDual_isSome (i : l.withDual) : (l.getDual? i).isSome := by
  simpa [withDual] using i.2

@[simp]
lemma mem_withDual_iff_isSome (i : Fin l.length) : i ∈ l.withDual ↔ (l.getDual? i).isSome := by
  simp [withDual]

@[simp]
lemma not_mem_withDual_iff_isNone (i : Fin l.length) :
    i ∉ l.withDual ↔ (l.getDual? i).isNone := by
  simp [withDual]

lemma mem_withDual_iff_exists : i ∈ l.withDual ↔ ∃ j, l.AreDualInSelf i j := by
  simp [withDual, Finset.mem_filter, Finset.mem_univ, getDual?]
  rw [Fin.isSome_find_iff]

/-!

## Basic properties of withDualInOther

-/


@[simp]
lemma mem_withInDualOther_iff_isSome (i : Fin l.length) :
    i ∈ l.withDualInOther l2 ↔ (l.getDualInOther? l2 i).isSome := by
  simp only [withDualInOther, getDualInOther?, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_withInDualOther_iff_exists :
    i ∈ l.withDualInOther l2 ↔ ∃ (j : Fin l2.length), l.AreDualInOther l2 i j := by
  simp [withDualInOther, Finset.mem_filter, Finset.mem_univ, getDualInOther?]
  rw [Fin.isSome_find_iff]

/-!

## Append properties of withDual

-/

lemma withDual_append_eq_disjSum : (l ++ l2).withDual =
    Equiv.finsetCongr appendEquiv
      ((l.withDual ∪ l.withDualInOther l2).disjSum
      (l2.withDual ∪ l2.withDualInOther l)) := by
  ext i
  obtain ⟨k, hk⟩ := appendEquiv.surjective i
  subst hk
  match k with
  | Sum.inl k =>
    simp
  | Sum.inr k =>
    simp

/-!

## Append properties of withDualInOther

-/

lemma append_withDualInOther_eq :
    (l ++ l2).withDualInOther l3 =
    Equiv.finsetCongr appendEquiv ((l.withDualInOther l3).disjSum (l2.withDualInOther l3)) := by
  rw [Finset.ext_iff]
  intro i
  obtain ⟨k, hk⟩ := appendEquiv.surjective i
  subst hk
  match k with
  | Sum.inl k =>
    simp
  | Sum.inr k =>
    simp


lemma withDualInOther_append_eq : l.withDualInOther (l2 ++ l3) =
    l.withDualInOther l2 ∪ l.withDualInOther l3 := by
  ext i
  simp

/-!

## Unique duals

-/

def withUniqueDual : Finset (Fin l.length) :=
  Finset.filter (fun i => i ∈ l.withDual ∧
    ∀ j, l.AreDualInSelf i j → j = l.getDual? i) Finset.univ

def withUniqueDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => i ∉ l.withDual ∧ i ∈ l.withDualInOther l2
     ∧ (∀ j, l.AreDualInOther l2 i j → j = l.getDualInOther? l2 i)) Finset.univ

/-!

## Basic properties of withUniqueDual

-/

@[simp]
lemma mem_withDual_of_mem_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    i ∈ l.withDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and] at h
  simpa using h.1

@[simp]
lemma mem_withUniqueDual_isSome (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    (l.getDual? i).isSome := by
  simpa using mem_withDual_of_mem_withUniqueDual l i h

lemma mem_withDual_of_withUniqueDual (i : l.withUniqueDual) :
    i.1 ∈ l.withDual := by
  have hi := i.2
  simp only [withUniqueDual, Finset.mem_filter, Finset.mem_univ] at hi
  exact hi.2.1


/-!

## Basic properties of withUniqueDualInOther

-/

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
lemma mem_withUniqueDualInOther_isSome (i : Fin l.length) (hi : i ∈ l.withUniqueDualInOther l2) :
    (l.getDualInOther? l2 i).isSome := by
  simp only [withUniqueDualInOther, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hi2 := hi.2.1
  simpa using hi2

/-!

## Properties of getDual? and withUniqueDual

-/

lemma all_dual_eq_getDual?_of_mem_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    ∀ j, l.AreDualInSelf i j → j = l.getDual? i := by
  simp [withUniqueDual] at h
  exact fun j hj => h.2 j hj

lemma some_eq_getDual?_of_withUniqueDual_iff (i j : Fin l.length) (h : i ∈ l.withUniqueDual) :
    l.AreDualInSelf i j ↔ some j = l.getDual? i := by
  apply Iff.intro
  intro h'
  exact all_dual_eq_getDual?_of_mem_withUniqueDual l i h j h'
  intro h'
  have hj : j = (l.getDual? i).get (mem_withUniqueDual_isSome l i h) :=
    Eq.symm (Option.get_of_mem (mem_withUniqueDual_isSome l i h) (id (Eq.symm h')))
  subst hj
  exact (getDual?_get_areDualInSelf l i (mem_withUniqueDual_isSome l i h)).symm

@[simp]
lemma eq_getDual?_get_of_withUniqueDual_iff (i j : Fin l.length) (h : i ∈ l.withUniqueDual) :
    l.AreDualInSelf i j ↔ j = (l.getDual? i).get (mem_withUniqueDual_isSome l i h) := by
  rw [l.some_eq_getDual?_of_withUniqueDual_iff i j h]
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  exact Eq.symm (Option.get_of_mem (mem_withUniqueDual_isSome l i h) (id (Eq.symm h')))
  simp [h']

lemma eq_of_areDualInSelf_withUniqueDual {j k : Fin l.length} (i : l.withUniqueDual)
    (hj : l.AreDualInSelf i j) (hk : l.AreDualInSelf i k) : j = k := by
  simp at hj hk
  exact hj.trans hk.symm

@[simp]
lemma getDual?_get_getDual?_get_of_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    (l.getDual? ((l.getDual? i).get (mem_withUniqueDual_isSome l i h))).get
      (l.getDual?_getDual?_get_isSome i (mem_withUniqueDual_isSome l i h)) = i := by
  by_contra hn
  have h' : l.AreDualInSelf i  ((l.getDual? ((l.getDual? i).get (mem_withUniqueDual_isSome l i h))).get (
      getDual?_getDual?_get_isSome l i (mem_withUniqueDual_isSome l i h))) := by
    simp [AreDualInSelf, hn]
    exact fun a => hn (id (Eq.symm a))
  simp [h] at h'

@[simp]
lemma getDual?_getDual?_get_of_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    l.getDual? ((l.getDual? i).get (mem_withUniqueDual_isSome l i h)) = some i := by
  nth_rewrite 3 [← l.getDual?_get_getDual?_get_of_withUniqueDual i h]
  simp

@[simp]
lemma getDual?_getDual?_of_withUniqueDual (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    (l.getDual? i).bind l.getDual? = some i := by
  have h1 : (l.getDual? i) = some ((l.getDual? i).get (mem_withUniqueDual_isSome l i h)) := by simp
  nth_rewrite 1 [h1]
  rw [Option.some_bind']
  simp [h]

@[simp]
lemma getDual?_get_of_mem_withUnique_mem (i : Fin l.length) (h : i ∈ l.withUniqueDual) :
    (l.getDual? i).get (l.mem_withUniqueDual_isSome i h) ∈ l.withUniqueDual := by
  simp [withUniqueDual, h]
  intro j hj
  have h1 : i = j := by
    by_contra hn
    have h' : l.AreDualInSelf i j := by
      simp [AreDualInSelf, hn]
      simp_all [AreDualInSelf]
    simp [h] at h'
    subst h'
    simp_all
  subst h1
  exact Eq.symm (getDual?_getDual?_get_of_withUniqueDual l i h)


/-!

## Properties of getDualInOther? and withUniqueDualInOther

-/

lemma all_dual_eq_of_withUniqueDualInOther (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    ∀ j, l.AreDualInOther l2 i j → j = l.getDualInOther? l2 i := by
  simp [withUniqueDualInOther] at h
  exact fun j hj => h.2.2 j hj

lemma some_eq_getDualInOther?_of_withUniqueDualInOther_iff (i : Fin l.length) (j : Fin l2.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    l.AreDualInOther l2 i j ↔ some j = l.getDualInOther? l2 i := by
  apply Iff.intro
  intro h'
  exact l.all_dual_eq_of_withUniqueDualInOther l2 i h j h'
  intro h'
  have hj : j = (l.getDualInOther? l2 i).get (mem_withUniqueDualInOther_isSome l l2 i h) :=
    Eq.symm (Option.get_of_mem  (mem_withUniqueDualInOther_isSome l l2 i h) (id (Eq.symm h')))
  subst hj
  simp only [getDualInOther?_areDualInOther_get]

@[simp]
lemma eq_getDualInOther?_get_of_withUniqueDualInOther_iff (i : Fin l.length) (j : Fin l2.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    l.AreDualInOther l2 i j ↔ j = (l.getDualInOther? l2 i).get
      (mem_withUniqueDualInOther_isSome l l2 i h) := by
  rw [l.some_eq_getDualInOther?_of_withUniqueDualInOther_iff l2 i j h]
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  exact Eq.symm (Option.get_of_mem (mem_withUniqueDualInOther_isSome l l2 i h) (id (Eq.symm h')))
  simp [h']

@[simp]
lemma getDualInOther?_get_getDualInOther?_get_of_withUniqueDualInOther
       (i : Fin l.length) (h : i ∈ l.withUniqueDualInOther l2) :
    (l2.getDualInOther? l ((l.getDualInOther? l2 i).get (mem_withUniqueDualInOther_isSome l l2 i h))).get
      (l.getDualInOther?_getDualInOther?_get_isSome l2 i (mem_withUniqueDualInOther_isSome l l2 i h)) = i := by
  by_contra hn
  have h' : l.AreDualInSelf i  ((l2.getDualInOther? l ((l.getDualInOther? l2 i).get (mem_withUniqueDualInOther_isSome l l2 i h))).get
      (l.getDualInOther?_getDualInOther?_get_isSome l2 i (mem_withUniqueDualInOther_isSome l l2 i h))):= by
    simp [AreDualInSelf, hn]
    exact fun a => hn (id (Eq.symm a))
  have h1 := l.not_mem_withDual_of_withUniqueDualInOther l2 ⟨i, h⟩
  simp [getDual?] at h1
  rw [Fin.find_eq_none_iff] at h1
  simp_all

@[simp]
lemma getDualInOther?_getDualInOther?_get_of_withUniqueDualInOther (i : Fin l.length) (h : i ∈ l.withUniqueDualInOther l2) :
    l2.getDualInOther? l ((l.getDualInOther? l2 i).get (mem_withUniqueDualInOther_isSome l l2 i h))
      = some i := by
  nth_rewrite 3 [← l.getDualInOther?_get_getDualInOther?_get_of_withUniqueDualInOther l2 i h]
  simp

@[simp]
lemma getDualInOther?_getDualInOther?_of_withUniqueDualInOther
    (i : Fin l.length) (h : i ∈ l.withUniqueDualInOther l2) :
    (l.getDualInOther? l2 i).bind (l2.getDualInOther? l) = some i := by
  have h1 : (l.getDualInOther? l2 i) = some ((l.getDualInOther? l2 i).get (mem_withUniqueDualInOther_isSome l l2 i h)) := by simp
  nth_rewrite 1 [h1]
  rw [Option.some_bind']
  simp [h]

lemma eq_of_areDualInOther_withUniqueDualInOther {j k : Fin l2.length} (i : l.withUniqueDualInOther l2)
    (hj : l.AreDualInOther l2 i j) (hk : l.AreDualInOther l2 i k) : j = k := by
  simp at hj hk
  exact hj.trans hk.symm

lemma getDual?_of_getDualInOther?_of_mem_withUniqueInOther_eq_none (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    l2.getDual? ((l.getDualInOther? l2 i).get (l.mem_withUniqueDualInOther_isSome l2 i h)) = none
    := by
  by_contra hn
  rw [← @Option.not_isSome_iff_eq_none, not_not] at hn
  rw [@getDual?_isSome_iff_exists] at hn
  obtain ⟨j, hj⟩ := hn
  have hx : l.AreDualInOther l2 i j := by
    simp [AreDualInOther, hj]
    simp [AreDualInSelf] at hj
    exact hj.2
  have hn := l.eq_of_areDualInOther_withUniqueDualInOther l2 ⟨i, h⟩ hx
    (getDualInOther?_areDualInOther_get l l2 i (mem_withUniqueDualInOther_isSome l l2 i h))
  subst hn
  simp_all

@[simp]
lemma getDualInOther?_get_of_mem_withUniqueInOther_mem (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l2) :
    (l.getDualInOther? l2 i).get (l.mem_withUniqueDualInOther_isSome l2 i h) ∈ l2.withUniqueDualInOther l := by
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDualInOther?_getDualInOther?_get_isSome, true_and]
  apply And.intro
  exact getDual?_of_getDualInOther?_of_mem_withUniqueInOther_eq_none l l2 i h
  intro j hj
  simp [h]
  by_contra hn
  have hx : l.AreDualInSelf i j := by
    simp [AreDualInSelf, hn]
    simp [AreDualInOther] at hj
    simp [hj]
    exact fun a => hn (id (Eq.symm a))
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, getDual?, Bool.not_eq_true,
    Option.not_isSome, Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter,
    Finset.mem_univ, true_and] at h
  rw [Fin.find_eq_none_iff] at h
  simp_all only



@[simp]
lemma getDualInOther?_self_of_mem_withUniqueInOther (i : Fin l.length)
    (h : i ∈ l.withUniqueDualInOther l) :
    l.getDualInOther? l i = some i := by
  rw [all_dual_eq_of_withUniqueDualInOther l l i h i rfl]




/-!

## Properties of getDual?, withUniqueDual and append

-/

lemma append_inl_not_mem_withDual_of_withDualInOther (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l.withDual ↔ ¬ i ∈ l.withDualInOther l2 := by
  refine Iff.intro (fun hs => ?_) (fun ho => ?_)
  · by_contra ho
    obtain ⟨j, hj⟩ := (l.mem_withDual_iff_exists).mp hs
    obtain ⟨k, hk⟩ := (l.mem_withInDualOther_iff_exists l2).mp ho
    have h1 : appendEquiv (Sum.inl j) = appendEquiv (Sum.inr k) := by
      refine (l ++ l2).eq_of_areDualInSelf_withUniqueDual ⟨appendEquiv (Sum.inl i), h⟩ ?_ ?_
      simpa using hj
      simpa using hk
    simp at h1
  · have ht : ((l ++ l2).getDual? (appendEquiv (Sum.inl i))).isSome := by simp [h]
    simp only [getDual?_isSome_append_inl_iff] at ht
    simp_all


lemma append_inr_not_mem_withDual_of_withDualInOther (i : Fin l2.length)
    (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l2.withDual ↔ ¬ i ∈ l2.withDualInOther l := by
  refine Iff.intro (fun hs => ?_) (fun ho => ?_)
  · by_contra ho
    obtain ⟨j, hj⟩ := (l2.mem_withDual_iff_exists).mp hs
    obtain ⟨k, hk⟩ := (l2.mem_withInDualOther_iff_exists l).mp ho
    have h1 : appendEquiv (Sum.inr j) = appendEquiv (Sum.inl k) := by
      refine (l ++ l2).eq_of_areDualInSelf_withUniqueDual ⟨appendEquiv (Sum.inr i), h⟩ ?_ ?_
      simpa using hj
      simpa using hk
    simp at h1
  · have ht : ((l ++ l2).getDual? (appendEquiv (Sum.inr i))).isSome := by simp [h]
    simp only [getDual?_isSome_append_inr_iff] at ht
    simp_all


lemma getDual?_append_symm_of_withUniqueDual_of_inl (i : Fin l.length) (k : Fin l2.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = some (appendEquiv (Sum.inr k))
    ↔ (l2 ++ l).getDual? (appendEquiv (Sum.inr i)) = some (appendEquiv (Sum.inl k)) := by
  have h := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  by_cases hs : (l.getDual? i).isSome
  <;> by_cases ho : (l.getDualInOther? l2 i).isSome
  <;> simp_all [hs, ho]

lemma getDual?_append_symm_of_withUniqueDual_of_inl' (i k : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = some (appendEquiv (Sum.inl k))
    ↔ (l2 ++ l).getDual? (appendEquiv (Sum.inr i)) = some (appendEquiv (Sum.inr k)) := by
  have h := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  by_cases hs : (l.getDual? i).isSome
  <;> by_cases ho : (l.getDualInOther? l2 i).isSome
  <;> simp_all [hs, ho]

lemma getDual?_append_symm_of_withUniqueDual_of_inr (i : Fin l2.length) (k : Fin l.length)
    (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = some (appendEquiv (Sum.inl k))
    ↔ (l2 ++ l).getDual? (appendEquiv (Sum.inl i)) = some (appendEquiv (Sum.inr k)) := by
  have h := l.append_inr_not_mem_withDual_of_withDualInOther l2 i h
  by_cases hs : (l2.getDual? i).isSome
  <;> by_cases ho : (l2.getDualInOther? l i).isSome
  <;> simp_all [hs, ho]

lemma getDual?_append_symm_of_withUniqueDual_of_inr' (i k : Fin l2.length)
    (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = some (appendEquiv (Sum.inr k))
    ↔ (l2 ++ l).getDual? (appendEquiv (Sum.inl i)) = some (appendEquiv (Sum.inl k)) := by
  have h := l.append_inr_not_mem_withDual_of_withDualInOther l2 i h
  by_cases hs : (l2.getDual? i).isSome
  <;> by_cases ho : (l2.getDualInOther? l i).isSome
  <;> simp_all [hs, ho]

lemma mem_withUniqueDual_append_symm (i : Fin l.length) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual ↔
    appendEquiv (Sum.inr i) ∈ (l2 ++ l).withUniqueDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_isSome_append_inl_iff, true_and, getDual?_isSome_append_inr_iff, and_congr_right_iff]
  intro h
  refine Iff.intro (fun h' j hj => ?_) (fun h' j hj => ?_)
  · obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      have hk' := h' (appendEquiv (Sum.inr k))
      simp only [AreDualInSelf.append_inl_inr] at hk'
      simp only [AreDualInSelf.append_inr_inl] at hj
      refine ((l.getDual?_append_symm_of_withUniqueDual_of_inl l2 _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inl_inr, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, getDual?_isSome_append_inl_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        getDual?_areDualInSelf_get]
    | Sum.inr k =>
      have hk' :=  h' (appendEquiv (Sum.inl k))
      simp only [AreDualInSelf.append_inl_inl] at hk'
      simp only [AreDualInSelf.append_inr_inr] at hj
      refine  ((l.getDual?_append_symm_of_withUniqueDual_of_inl' l2 _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inl_inl, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, getDual?_isSome_append_inl_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        getDual?_areDualInSelf_get]
  · obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      have hk' := h' (appendEquiv (Sum.inr k))
      simp only [AreDualInSelf.append_inr_inr] at hk'
      simp only [AreDualInSelf.append_inl_inl] at hj
      refine ((l2.getDual?_append_symm_of_withUniqueDual_of_inr' l _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inr_inr, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, getDual?_isSome_append_inr_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        getDual?_areDualInSelf_get]
    | Sum.inr k =>
      have hk' :=  h' (appendEquiv (Sum.inl k))
      simp only [AreDualInSelf.append_inr_inl] at hk'
      simp only [AreDualInSelf.append_inl_inr] at hj
      refine  ((l2.getDual?_append_symm_of_withUniqueDual_of_inr l _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inr_inl, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, getDual?_isSome_append_inr_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        getDual?_areDualInSelf_get]

@[simp]
lemma not_mem_withDualInOther_of_inl_mem_withUniqueDual  (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) (hs : i ∈ l.withUniqueDual) :
    ¬ i ∈ l.withUniqueDualInOther l2 := by
  have hn := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  simp_all
  by_contra ho
  have ho' :  (l.getDualInOther? l2 i).isSome := by
    simp [ho]
  simp_all [Option.isSome_none, Bool.false_eq_true]

@[simp]
lemma not_mem_withUniqueDual_of_inl_mem_withUnqieuDual (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) (hi : i ∈ l.withUniqueDualInOther l2) :
    ¬ i ∈ l.withUniqueDual  := by
  have hn := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  simp_all
  by_contra hs
  simp_all [Option.isSome_none, Bool.false_eq_true]

@[simp]
lemma mem_withUniqueDual_of_inl (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) (hi : (l.getDual? i).isSome) :
    i ∈ l.withUniqueDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_isSome_append_inl_iff, true_and] at h ⊢
  apply And.intro hi
  intro j hj
  have hj' := h.2 (appendEquiv (Sum.inl j))
  simp at hj'
  have hj'' := hj' hj
  simp [hi] at hj''
  simp_all

@[simp]
lemma mem_withUniqueDualInOther_of_inl_withDualInOther  (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) (hi : (l.getDualInOther? l2 i).isSome) :
    i ∈ l.withUniqueDualInOther l2 := by
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and]
  have hn := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  simp_all only [mem_withDual_iff_isSome, mem_withInDualOther_iff_isSome, not_true_eq_false,
    iff_false, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none, true_and]
  intro j hj
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_isSome_append_inl_iff, true_and] at h
  have hj' := h.2 (appendEquiv (Sum.inr j))
  simp only [AreDualInSelf.append_inl_inr] at hj'
  have hj'' := hj' hj
  simp [hi, hn] at hj''
  simp_all

lemma withUniqueDual_iff_not_withUniqueDualInOther_of_inl_withUniqueDualInOther
    (i : Fin l.length) (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l.withUniqueDual ↔ ¬ i ∈ l.withUniqueDualInOther l2 := by
  by_cases h' : (l.getDual? i).isSome
  have hn : i ∈ l.withUniqueDual := mem_withUniqueDual_of_inl l l2 i h h'
  simp_all
  have hn := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h
  simp_all
  simp [withUniqueDual]
  simp_all
  have hx : (l.getDualInOther? l2 i).isSome := by
    rw [← @Option.isNone_iff_eq_none] at hn
    rw [← @Option.not_isSome] at hn
    exact Eq.symm ((fun {a b} => Bool.not_not_eq.mp) fun a => hn (id (Eq.symm a)))
  simp_all

lemma append_inl_mem_withUniqueDual_of_withUniqueDual (i : Fin l.length)
    (h : i ∈ l.withUniqueDual) (hn : i ∉ l.withDualInOther l2) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
  simp [withUniqueDual]
  apply And.intro
  simp_all
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k => simp_all
  | Sum.inr k =>
    simp at hj
    refine False.elim (hn ?_)
    exact (l.mem_withInDualOther_iff_exists _).mpr ⟨k, hj⟩

lemma append_inl_mem_of_withUniqueDualInOther (i : Fin l.length)
    (ho : i ∈ l.withUniqueDualInOther l2) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_isSome_append_inl_iff, true_and]
  apply And.intro
  simp_all only [mem_withUniqueDualInOther_isSome, or_true]
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  have hs := l.not_mem_withDual_of_withUniqueDualInOther l2 ⟨i, ho⟩
  match k with
  | Sum.inl k =>
    refine False.elim (hs ?_)
    simp at hj
    exact (l.mem_withDual_iff_exists).mpr ⟨k, hj⟩
  | Sum.inr k =>
    simp_all

@[simp]
lemma append_inl_mem_withUniqueDual_iff (i : Fin l.length) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual ↔
    ((i ∈ l.withUniqueDual ∧ i ∉ l.withDualInOther l2) ↔ ¬ i ∈ l.withUniqueDualInOther l2) := by
  apply Iff.intro
  · intro h
    apply Iff.intro
    · intro hs
      exact (l.withUniqueDual_iff_not_withUniqueDualInOther_of_inl_withUniqueDualInOther l2 i
        h).mp hs.1
    · intro ho
      have hs := ((l.withUniqueDual_iff_not_withUniqueDualInOther_of_inl_withUniqueDualInOther l2 i
        h).mpr ho)
      apply And.intro hs
      refine (l.append_inl_not_mem_withDual_of_withDualInOther l2 i h).mp ?_
      exact (l.mem_withDual_of_withUniqueDual ⟨i, hs⟩)
  · intro h
    by_cases ho : i ∈ l.withUniqueDualInOther l2
    · exact append_inl_mem_of_withUniqueDualInOther l l2 i ho
    · exact append_inl_mem_withUniqueDual_of_withUniqueDual l l2 i (h.mpr ho).1 (h.mpr ho).2

@[simp]
lemma append_inr_mem_withUniqueDual_iff (i : Fin l2.length) :
    appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual ↔
    ((i ∈ l2.withUniqueDual ∧ i ∉ l2.withDualInOther l) ↔ ¬ i ∈ l2.withUniqueDualInOther l) := by
  rw [← mem_withUniqueDual_append_symm]
  simp

lemma append_withUniqueDual : (l ++ l2).withUniqueDual =
    Finset.map (l.appendInl l2) ((l.withUniqueDual ∩ (l.withDualInOther l2)ᶜ) ∪ l.withUniqueDualInOther l2)
    ∪ Finset.map (l.appendInr l2) ((l2.withUniqueDual ∩ (l2.withDualInOther l)ᶜ) ∪ l2.withUniqueDualInOther l) := by
  rw [Finset.ext_iff]
  intro j
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [append_inl_mem_withUniqueDual_iff, Finset.mem_union]
    apply Iff.intro
    · intro h
      apply Or.inl
      simp only [Finset.mem_map, Finset.mem_union, Finset.mem_inter, Finset.mem_compl,
        mem_withInDualOther_iff_isSome, Bool.not_eq_true, Option.not_isSome,
        Option.isNone_iff_eq_none]
      use k
      simp only [appendInl, Function.Embedding.coeFn_mk, Function.comp_apply, and_true]
      by_cases hk : k ∈ l.withUniqueDualInOther l2
      simp_all
      have hk' := h.mpr hk
      simp_all
    · intro h
      simp at h
      cases' h with h h
      · obtain ⟨j, hj⟩ := h
        have hjk : j = k := by
          simp [appendInl] at hj
          exact hj.2
        subst hjk
        have hj1 := hj.1
        cases' hj1 with hj1 hj1
        · simp_all
          by_contra hn
          have h' := l.mem_withDualInOther_of_withUniqueDualInOther l2 ⟨j, hn⟩
          simp_all only [mem_withInDualOther_iff_isSome, Option.isSome_none, Bool.false_eq_true]
        · simp_all only [or_true, true_and, mem_withInDualOther_iff_isSome,
          mem_withUniqueDualInOther_isSome, not_true_eq_false, and_false]
      · obtain ⟨j, hj⟩ := h
        simp [appendInr] at hj
  | Sum.inr k =>
    simp only [append_inr_mem_withUniqueDual_iff, Finset.mem_union]
    apply Iff.intro
    · intro h
      apply Or.inr
      simp
      use k
      simp [appendInr]
      by_cases hk : k ∈ l2.withUniqueDualInOther l
      simp_all only [mem_withInDualOther_iff_isSome, mem_withUniqueDualInOther_isSome,
        not_true_eq_false, and_false, or_true]
      have hk' := h.mpr hk
      simp_all only [not_false_eq_true, and_self, mem_withInDualOther_iff_isSome, Bool.not_eq_true,
        Option.not_isSome, Option.isNone_iff_eq_none, or_false]
    · intro h
      simp at h
      cases' h with h h
      · obtain ⟨j, hj⟩ := h
        simp [appendInl] at hj
      · obtain ⟨j, hj⟩ := h
        have hjk : j = k := by
          simp [appendInr] at hj
          exact hj.2
        subst hjk
        have hj1 := hj.1
        cases' hj1 with hj1 hj1
        · simp_all
          by_contra hn
          have h' := l2.mem_withDualInOther_of_withUniqueDualInOther l ⟨j, hn⟩
          simp_all
        · simp_all

lemma append_withUniqueDual_disjSum : (l ++ l2).withUniqueDual =
    Equiv.finsetCongr appendEquiv
    (((l.withUniqueDual ∩ (l.withDualInOther l2)ᶜ) ∪ l.withUniqueDualInOther l2).disjSum
     ((l2.withUniqueDual ∩ (l2.withDualInOther l)ᶜ) ∪ l2.withUniqueDualInOther l)) := by
  rw [← Equiv.symm_apply_eq]
  simp [append_withUniqueDual]
  rw [Finset.map_union]
  rw [Finset.map_map, Finset.map_map]
  ext1 a
  cases a with
  | inl val => simp
  | inr val_1 => simp

/-!

## Properties of getDualInOther?, withUniqueDualInOther and appendInOther

-/



lemma mem_append_withUniqueDualInOther_symm (i : Fin l.length) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDualInOther l3 ↔
    appendEquiv (Sum.inr i) ∈ (l2 ++ l).withUniqueDualInOther l3 := by
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    getDual?_eq_none_append_inl_iff, getDualInOther?_append_of_inl, AreDualInOther.append_of_inl,
    true_and, getDual?_eq_none_append_inr_iff, getDualInOther?_append_of_inr,
    AreDualInOther.append_of_inr]

@[simp]
lemma withUniqueDualInOther_append_not_isSome_snd_of_isSome_fst (i : Fin l.length)
    (h1 : i ∈ l.withUniqueDualInOther (l2 ++ l3)) (h2 : (l.getDualInOther? l2 i).isSome) :
    (l.getDualInOther? l3 i) = none := by
  by_contra hn
  simp only [getDualInOther?] at h2 hn
  rw [← @Option.not_isSome_iff_eq_none, not_not] at hn
  rw [Fin.isSome_find_iff] at h2 hn
  obtain ⟨j2, hj2⟩ := h2
  obtain ⟨j3, hj3⟩ := hn
  have h1' : l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inl j2)) := by
    simpa using hj2
  have h2 : l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inr j3)) := by
    simpa using hj3
  have h3 := l.eq_of_areDualInOther_withUniqueDualInOther (l2 ++ l3) ⟨i, h1⟩ h1' h2
  simp only [EmbeddingLike.apply_eq_iff_eq] at h3

@[simp]
lemma withUniqueDualInOther_append_not_isSome_fst_of_isSome_snd (i : Fin l.length)
    (h1 : i ∈ l.withUniqueDualInOther (l2 ++ l3)) (h2 : (l.getDualInOther? l3 i).isSome) :
    (l.getDualInOther? l2 i) = none := by
  by_contra hn
  simp only [getDualInOther?] at h2 hn
  rw [← @Option.not_isSome_iff_eq_none, not_not] at hn
  rw [Fin.isSome_find_iff] at h2 hn
  obtain ⟨j2, hj2⟩ := h2
  obtain ⟨j3, hj3⟩ := hn
  have h1' : l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inr j2)) := by
    simpa using hj2
  have h2 : l.AreDualInOther (l2 ++ l3) i (appendEquiv (Sum.inl j3)) := by
    simpa using hj3
  have h3 := l.eq_of_areDualInOther_withUniqueDualInOther (l2 ++ l3) ⟨i, h1⟩ h1' h2
  simp only [EmbeddingLike.apply_eq_iff_eq] at h3

@[simp]
lemma withUniqueDualInOther_append_isSome_snd_of_not_isSome_fst (i : Fin l.length)
    (h1 : i ∈ l.withUniqueDualInOther (l2 ++ l3)) (h2 : ¬ (l.getDualInOther? l2 i).isSome) :
    (l.getDualInOther? l3 i).isSome := by
  by_contra hn
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, getDualInOther?_isSome_of_append_iff,
    Finset.mem_filter, Finset.mem_univ, true_and] at h1
  simp_all only [withUniqueDualInOther, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none, Option.isSome_none,
    Bool.false_eq_true, or_self, false_and, and_false]

lemma withUniqueDualInOther_append_isSome_fst_iff_not_isSome_snd (i : Fin l.length)
    (h1 : i ∈ l.withUniqueDualInOther (l2 ++ l3)) :
    (l.getDualInOther? l2 i).isSome ↔ (l.getDualInOther? l3 i) = none := by
  by_cases hs : (l.getDualInOther? l2 i).isSome
  simp [hs, h1]
  exact l.withUniqueDualInOther_append_not_isSome_snd_of_isSome_fst l2 l3 i h1 hs
  simp [hs]
  rw [← @Option.not_isSome_iff_eq_none, not_not]
  exact withUniqueDualInOther_append_isSome_snd_of_not_isSome_fst l l2 l3 i h1 hs

lemma getDualInOther?_append_symm_of_withUniqueDual_of_inl (i : Fin l.length)
    (k : Fin l2.length) (h : i ∈ l.withUniqueDualInOther (l2 ++ l3)) :
    l.getDualInOther? (l2 ++ l3) i = some (appendEquiv (Sum.inl k))
    ↔ l.getDualInOther? (l3 ++ l2) i  = some (appendEquiv (Sum.inr k)) := by
  have h := l.withUniqueDualInOther_append_isSome_fst_iff_not_isSome_snd l2 l3 i h
  by_cases hs : (l.getDualInOther? l2 i).isSome
  <;>  by_cases ho : (l.getDualInOther? l3 i).isSome
  <;> simp_all [hs]

lemma getDualInOther?_append_symm_of_withUniqueDual_of_inr (i : Fin l.length)
    (k : Fin l3.length) (h : i ∈ l.withUniqueDualInOther (l2 ++ l3)) :
    l.getDualInOther? (l2 ++ l3) i = some (appendEquiv (Sum.inr k))
    ↔ l.getDualInOther? (l3 ++ l2) i  = some (appendEquiv (Sum.inl k)) := by
  have h := l.withUniqueDualInOther_append_isSome_fst_iff_not_isSome_snd l2 l3 i h
  by_cases hs : (l.getDualInOther? l2 i).isSome
  <;>  by_cases ho : (l.getDualInOther? l3 i).isSome
  <;> simp_all [hs]


lemma mem_withUniqueDualInOther_symm' (i : Fin l.length)
    (h :  i ∈ l.withUniqueDualInOther (l2 ++ l3)):
    i ∈ l.withUniqueDualInOther (l3 ++ l2) := by
  have h' := h
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true,
    Option.not_isSome, Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome,
    getDualInOther?_isSome_of_append_iff, Finset.mem_filter, Finset.mem_univ, true_and,
    implies_true, and_self, eq_getDualInOther?_get_of_withUniqueDualInOther_iff,
    getDualInOther?_areDualInOther_get] at h ⊢
  apply And.intro h.1
  have hc := l.withUniqueDualInOther_append_isSome_fst_iff_not_isSome_snd l2 l3 i h'
  by_cases h1 : (l.getDualInOther? l2 i).isSome <;>
  by_cases h2 : (l.getDualInOther? l3 i).isSome
  · simp only [h1, h2, not_true_eq_false, imp_false] at hc
    rw [← @Option.not_isSome_iff_eq_none]  at hc
    simp [h2] at hc
  · simp only [h1, or_true, true_and]
    intro j
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp only [AreDualInOther.of_append_inl]
      have hk'' := h.2.2 (appendEquiv (Sum.inr k))
      simp at hk''
      exact fun h'' => ((getDualInOther?_append_symm_of_withUniqueDual_of_inr l l2 l3 i k h').mp
        (hk'' h'').symm).symm
    | Sum.inr k =>
      simp only [AreDualInOther.of_append_inr]
      have hk'' := h.2.2 (appendEquiv (Sum.inl k))
      simp at hk''
      exact fun h'' => ((getDualInOther?_append_symm_of_withUniqueDual_of_inl l l2 l3 i k h').mp
        (hk'' h'').symm).symm
  · simp only [h2, true_or, Option.some.injEq, true_and]
    intro j
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp only [AreDualInOther.of_append_inl]
      have hk'' := h.2.2 (appendEquiv (Sum.inr k))
      simp at hk''
      exact fun h'' => ((getDualInOther?_append_symm_of_withUniqueDual_of_inr l l2 l3 i k h').mp
        (hk'' h'').symm).symm
    | Sum.inr k =>
      simp only [AreDualInOther.of_append_inr]
      have hk'' := h.2.2 (appendEquiv (Sum.inl k))
      simp at hk''
      exact fun h'' => ((getDualInOther?_append_symm_of_withUniqueDual_of_inl l l2 l3 i k h').mp
        (hk'' h'').symm).symm
  · simp [h1] at hc
    simp_all

lemma mem_withUniqueDualInOther_symm (i : Fin l.length) :
   i ∈ l.withUniqueDualInOther (l2 ++ l3) ↔ i ∈ l.withUniqueDualInOther (l3 ++ l2) :=
  Iff.intro (l.mem_withUniqueDualInOther_symm' l2 l3 i)
    (l.mem_withUniqueDualInOther_symm' l3 l2 i)

/-!

## withDual equal to withUniqueDual

-/


lemma withUnqiueDual_eq_withDual_iff_unique_forall :
    l.withUniqueDual = l.withDual ↔
    ∀ (i : l.withDual) j, l.AreDualInSelf i j → j = l.getDual? i := by
  apply Iff.intro
  · intro h i j hj
    rw [@Finset.ext_iff] at h
    simp [withUniqueDual] at h
    refine h i ?_ j hj
    simp
  · intro h
    apply Finset.ext
    intro i
    apply Iff.intro
    · intro hi
      simp [withUniqueDual] at hi
      simpa using hi.1
    · intro hi
      simp [withUniqueDual]
      apply And.intro
      simpa using hi
      intro j hj
      exact h ⟨i, hi⟩ j hj

lemma withUnqiueDual_eq_withDual_iff :
    l.withUniqueDual = l.withDual ↔
    ∀ i, (l.getDual? i).bind l.getDual? = Option.guard (fun i => i ∈ l.withDual) i := by
  apply Iff.intro
  · intro h i
    by_cases hi : i ∈ l.withDual
    · have hii : i ∈ l.withUniqueDual := by
        simp_all only
      change (l.getDual? i).bind l.getDual?  = _
      simp [hii]
      symm
      rw [Option.guard_eq_some]
      exact ⟨rfl, by simpa using hi⟩
    · simp at hi
      simp [Option.guard, hi]
  · intro h
    rw [withUnqiueDual_eq_withDual_iff_unique_forall]
    intro i j hj
    rcases l.getDual?_of_areDualInSelf hj with hi | hi | hi
    · have hj' := h j
      rw [hi] at hj'
      simp at hj'
      rw [hj']
      symm
      rw [Option.guard_eq_some, hi]
      exact ⟨rfl, rfl⟩
    · exact hi.symm
    · have hj' := h j
      rw [hi] at hj'
      rw [h i] at hj'
      have hi : Option.guard (fun i => i ∈ l.withDual) ↑i = some i := by
         apply Option.guard_eq_some.mpr
         simp
      rw [hi] at hj'
      simp at hj'
      have hj'' := Option.guard_eq_some.mp hj'.symm
      have hj''' := hj''.1
      rw [hj'''] at hj
      simp at hj

lemma withUnqiueDual_eq_withDual_iff_list_apply :
    l.withUniqueDual = l.withDual ↔
    (Fin.list l.length).map (fun i => (l.getDual? i).bind l.getDual?) =
    (Fin.list l.length).map (fun i => Option.guard (fun i => i ∈ l.withDual) i) := by
  rw [withUnqiueDual_eq_withDual_iff]
  apply Iff.intro
  intro h
  apply congrFun
  apply congrArg
  exact (Set.eqOn_univ (fun i => (l.getDual? i).bind l.getDual?) fun i =>
    Option.guard (fun i => i ∈ l.withDual) i).mp fun ⦃x⦄ _ => h x
  intro h
  intro i
  simp only [List.map_inj_left] at h
  have h1 {n : ℕ} (m : Fin n) : m ∈ Fin.list n := by
      have h1' : (Fin.list n)[m] = m := Fin.getElem_list _ _
      exact h1' ▸ List.getElem_mem _ _ _
  exact h i (h1 i)

def withUnqiueDualEqWithDualBool : Bool :=
  if (Fin.list l.length).map (fun i => (l.getDual? i).bind l.getDual?) =
    (Fin.list l.length).map (fun i => Option.guard (fun i => i ∈ l.withDual) i) then
    true
  else
    false

lemma withUnqiueDual_eq_withDual_iff_list_apply_bool :
    l.withUniqueDual = l.withDual ↔ l.withUnqiueDualEqWithDualBool := by
  rw [withUnqiueDual_eq_withDual_iff_list_apply]
  apply Iff.intro
  intro h
  simp [withUnqiueDualEqWithDualBool, h]
  intro h
  simpa [withUnqiueDualEqWithDualBool] using h

@[simp]
lemma withUnqiueDual_eq_withDual_of_empty (h : l.withDual = ∅) :
    l.withUniqueDual = l.withDual := by
  rw [h, Finset.eq_empty_iff_forall_not_mem]
  intro x
  by_contra hx
  have x' : l.withDual := ⟨x, l.mem_withDual_of_withUniqueDual ⟨x, hx⟩⟩
  have hx'  := x'.2
  simp [h] at hx'

/-!

## withUniqueDualInOther equal to withDualInOther append conditions

-/

lemma withUniqueDualInOther_eq_withDualInOther_append_of_symm'
    (h : (l ++ l2).withUniqueDualInOther l3 = (l ++ l2).withDualInOther l3) :
    (l2 ++ l).withUniqueDualInOther l3 = (l2 ++ l).withDualInOther l3  := by
  rw [Finset.ext_iff] at h ⊢
  intro j
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    rw [mem_append_withUniqueDualInOther_symm]
    simpa using h (appendEquiv (Sum.inr k))
  | Sum.inr k =>
    rw [← mem_append_withUniqueDualInOther_symm]
    simpa using h (appendEquiv (Sum.inl k))

lemma withUniqueDualInOther_eq_withDualInOther_append_of_symm :
    (l ++ l2).withUniqueDualInOther l3 = (l ++ l2).withDualInOther l3 ↔
    (l2 ++ l).withUniqueDualInOther l3 = (l2 ++ l).withDualInOther l3 := by
  apply Iff.intro
  exact l.withUniqueDualInOther_eq_withDualInOther_append_of_symm' l2 l3
  exact l2.withUniqueDualInOther_eq_withDualInOther_append_of_symm' l l3

lemma withUniqueDualInOther_eq_withDualInOther_of_append_symm'
    (h : l.withUniqueDualInOther (l2 ++ l3) = l.withDualInOther (l2 ++ l3)) :
    l.withUniqueDualInOther (l3 ++ l2) = l.withDualInOther (l3 ++ l2) := by
  rw [Finset.ext_iff] at h ⊢
  intro j
  rw [mem_withUniqueDualInOther_symm]
  rw [h j]
  simp
  simp_all only [mem_withInDualOther_iff_isSome, getDualInOther?_isSome_of_append_iff]
  apply Iff.intro
  · intro a
    cases a with
    | inl h_1 => simp_all only [or_true]
    | inr h_2 => simp_all only [true_or]
  · intro a
    cases a with
    | inl h_1 => simp_all only [or_true]
    | inr h_2 => simp_all only [true_or]

lemma withUniqueDualInOther_eq_withDualInOther_of_append_symm :
    l.withUniqueDualInOther (l2 ++ l3) = l.withDualInOther (l2 ++ l3) ↔
    l.withUniqueDualInOther (l3 ++ l2) = l.withDualInOther (l3 ++ l2) := by
  apply Iff.intro
  exact l.withUniqueDualInOther_eq_withDualInOther_of_append_symm' l2 l3
  exact l.withUniqueDualInOther_eq_withDualInOther_of_append_symm' l3 l2


/-!

## withDual equal to withUniqueDual append conditions

-/


lemma append_withDual_eq_withUniqueDual_iff :
    (l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    ((l.withUniqueDual ∩ (l.withDualInOther l2)ᶜ) ∪ l.withUniqueDualInOther l2)
    = l.withDual ∪ l.withDualInOther l2
    ∧ (l2.withUniqueDual ∩ (l2.withDualInOther l)ᶜ) ∪ l2.withUniqueDualInOther l
    =  l2.withDual ∪ l2.withDualInOther l := by
  rw [append_withUniqueDual_disjSum, withDual_append_eq_disjSum]
  simp
  have h (s s' : Finset (Fin l.length)) (t t' : Finset (Fin l2.length)) :
      s.disjSum t = s'.disjSum t' ↔ s = s' ∧ t = t' := by
    simp [Finset.ext_iff]
  rw [h]

lemma append_withDual_eq_withUniqueDual_symm :
    (l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    (l2 ++ l).withUniqueDual = (l2 ++ l).withDual := by
  rw [append_withDual_eq_withUniqueDual_iff, append_withDual_eq_withUniqueDual_iff]
  apply Iff.intro
  · intro a
    simp_all only [and_self]
  · intro a
    simp_all only [and_self]


@[simp]
lemma append_withDual_eq_withUniqueDual_inl (h : (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
    l.withUniqueDual = l.withDual := by
  rw [Finset.ext_iff]
  intro i
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  · simp [h']
  · have hn : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
      rw [h]
      simp_all
    refine l.mem_withUniqueDual_of_inl l2 i hn ?_
    simp_all

@[simp]
lemma append_withDual_eq_withUniqueDual_inr (h : (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
    l2.withUniqueDual = l2.withDual := by
  rw [append_withDual_eq_withUniqueDual_symm] at h
  exact append_withDual_eq_withUniqueDual_inl l2 l h

@[simp]
lemma append_withDual_eq_withUniqueDual_withUniqueDualInOther_inl
    (h :  (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
    l.withUniqueDualInOther l2 = l.withDualInOther l2 := by
  rw [Finset.ext_iff]
  intro i
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  · simp [h']
  · have hn : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
      rw [h]
      simp_all
    refine l.mem_withUniqueDualInOther_of_inl_withDualInOther l2 i hn ?_
    simp_all

@[simp]
lemma append_withDual_eq_withUniqueDual_withUniqueDualInOther_inr
    (h :  (l ++ l2).withUniqueDual = (l ++ l2).withDual) :
    l2.withUniqueDualInOther l = l2.withDualInOther l := by
  rw [append_withDual_eq_withUniqueDual_symm] at h
  exact append_withDual_eq_withUniqueDual_withUniqueDualInOther_inl l2 l h

lemma append_withDual_eq_withUniqueDual_iff' :
    (l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    l.withUniqueDual = l.withDual ∧ l2.withUniqueDual = l2.withDual
    ∧ l.withUniqueDualInOther l2 = l.withDualInOther l2 ∧
    l2.withUniqueDualInOther l = l2.withDualInOther l := by
  apply Iff.intro
  intro h
  exact ⟨append_withDual_eq_withUniqueDual_inl l l2 h, append_withDual_eq_withUniqueDual_inr l l2 h,
    append_withDual_eq_withUniqueDual_withUniqueDualInOther_inl l l2 h,
    append_withDual_eq_withUniqueDual_withUniqueDualInOther_inr l l2 h⟩
  intro h
  rw [append_withDual_eq_withUniqueDual_iff]
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2]
  have h1 : l.withDual ∩ (l.withDualInOther l2)ᶜ = l.withDual := by
    rw [Finset.inter_eq_left]
    rw [Finset.subset_iff]
    rw [← h.1, ← h.2.2.1]
    intro i hi
    simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.compl_filter, not_and,
      not_forall, Classical.not_imp, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hn
    simp_all
  have h2 : l2.withDual ∩ (l2.withDualInOther l)ᶜ = l2.withDual := by
    rw [Finset.inter_eq_left]
    rw [Finset.subset_iff]
    rw [← h.2.1, ← h.2.2.2]
    intro i hi
    simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.compl_filter, not_and,
      not_forall, Classical.not_imp, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hn
    simp_all
  rw [h1, h2]
  simp only [and_self]

lemma append_withDual_eq_withUniqueDual_swap :
    (l ++ l2 ++ l3).withUniqueDual = (l ++ l2 ++ l3).withDual
    ↔ (l2 ++ l ++ l3).withUniqueDual = (l2 ++ l ++ l3).withDual := by
  rw [append_withDual_eq_withUniqueDual_iff']
  rw [append_withDual_eq_withUniqueDual_iff' (l2 ++ l) l3]
  rw [append_withDual_eq_withUniqueDual_symm]
  rw [withUniqueDualInOther_eq_withDualInOther_of_append_symm]
  rw [withUniqueDualInOther_eq_withDualInOther_append_of_symm]

/-!

## Indices which do not have duals.

-/

def withoutDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isNone) Finset.univ

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

def withoutDualEquiv : Fin l.withoutDual.card ≃ l.withoutDual  :=
  (Finset.orderIsoOfFin l.withoutDual (by rfl)).toEquiv

def dualEquiv : l.withDual ⊕ Fin l.withoutDual.card ≃ Fin l.length :=
  (Equiv.sumCongr (Equiv.refl _) l.withoutDualEquiv).trans <|
  (Equiv.Finset.union _ _ l.withDual_disjoint_withoutDual).trans <|
  Equiv.subtypeUnivEquiv (by simp [withDual_union_withoutDual])


/-!

## The contraction list

-/

def contrIndexList : IndexList X where
  val := (Fin.list l.withoutDual.card).map (fun i => l.val.get (l.withoutDualEquiv i).1)

@[simp]
lemma contrIndexList_length : l.contrIndexList.length = l.withoutDual.card := by
  simp [contrIndexList, withoutDual, length]

@[simp]
lemma contrIndexList_idMap (i : Fin l.contrIndexList.length) : l.contrIndexList.idMap i
    = l.idMap (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)).1 := by
  simp [contrIndexList, idMap]
  rfl

@[simp]
lemma contrIndexList_colorMap (i : Fin l.contrIndexList.length) : l.contrIndexList.colorMap i
    = l.colorMap (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)).1 := by
  simp [contrIndexList, colorMap]
  rfl

lemma contrIndexList_areDualInSelf (i j : Fin l.contrIndexList.length) :
    l.contrIndexList.AreDualInSelf i j ↔
    l.AreDualInSelf (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)).1
      (l.withoutDualEquiv (Fin.cast l.contrIndexList_length j)).1 := by
  simp [AreDualInSelf]
  intro _
  trans ¬ (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)) =
    (l.withoutDualEquiv (Fin.cast l.contrIndexList_length j))
  rw [l.withoutDualEquiv.apply_eq_iff_eq]
  simp [Fin.ext_iff]
  exact Iff.symm Subtype.coe_ne_coe

@[simp]
lemma contrIndexList_getDual? (i : Fin l.contrIndexList.length) :
    l.contrIndexList.getDual? i = none := by
  rw [← Option.not_isSome_iff_eq_none, ← mem_withDual_iff_isSome, mem_withDual_iff_exists]
  simp [contrIndexList_areDualInSelf]
  have h1 := (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)).2
  have h1' := Finset.disjoint_right.mp l.withDual_disjoint_withoutDual h1
  rw [mem_withDual_iff_exists] at h1'
  simp [contrIndexList_areDualInSelf] at h1'
  exact fun x => h1' ↑(l.withoutDualEquiv (Fin.cast (contrIndexList_length l) x))

@[simp]
lemma contrIndexList_withDual : l.contrIndexList.withDual = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro x
  simp [withDual]

@[simp]
lemma contrIndexList_areDualInSelf_false (i j : Fin l.contrIndexList.length) :
    l.contrIndexList.AreDualInSelf i j ↔ False := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  have h1 : i ∈ l.contrIndexList.withDual := by
    rw [@mem_withDual_iff_exists]
    use j
  simp_all
  simp_all

@[simp]
lemma contrIndexList_of_withDual_empty (h : l.withDual = ∅) : l.contrIndexList = l := by
  have h1 := l.withDual_union_withoutDual
  rw [h , Finset.empty_union] at h1
  apply ext
  rw [@List.ext_get_iff]
  change l.contrIndexList.length = l.length  ∧ _
  rw [contrIndexList_length, h1]
  simp
  intro n h1' h2
  simp [contrIndexList]
  congr
  simp [withoutDualEquiv]
  simp [h1]
  rw [(Finset.orderEmbOfFin_unique' _
    (fun x => Finset.mem_univ ((Fin.castOrderIso _).toOrderEmbedding x))).symm]
  simp
  rw [h1]
  exact Finset.card_fin l.length

lemma contrIndexList_contrIndexList : l.contrIndexList.contrIndexList = l.contrIndexList := by
  simp

@[simp]
lemma contrIndexList_getDualInOther?_self  (i : Fin l.contrIndexList.length) :
    l.contrIndexList.getDualInOther? l.contrIndexList i = some i := by
  simp [getDualInOther?]
  rw [@Fin.find_eq_some_iff]
  simp [AreDualInOther]
  intro j hj
  have h1 : i = j := by
    by_contra hn
    have h :  l.contrIndexList.AreDualInSelf i j := by
      simp only [AreDualInSelf]
      simp [hj]
      exact hn
    simp at h
  subst h1
  rfl

/-!

## The equivalence defined by getDual?

-/

def getDualEquiv : l.withUniqueDual ≃ l.withUniqueDual where
  toFun x := ⟨(l.getDual? x).get (l.mem_withUniqueDual_isSome x.1 x.2), by simp only [Finset.coe_mem,
    getDual?_get_of_mem_withUnique_mem]⟩
  invFun x := ⟨(l.getDual? x).get (l.mem_withUniqueDual_isSome x.1 x.2), by simp⟩
  left_inv x := SetCoe.ext (by simp)
  right_inv x := SetCoe.ext (by simp)

@[simp]
lemma getDualEquiv_involutive : Function.Involutive l.getDualEquiv := by
  intro x
  simp [getDualEquiv]

/-!

## Equivalence for withUniqueDualInOther

-/

def getDualInOtherEquiv : l.withUniqueDualInOther l2 ≃ l2.withUniqueDualInOther l where
  toFun x := ⟨(l.getDualInOther? l2 x).get (l.mem_withUniqueDualInOther_isSome l2 x.1 x.2),
    by simp⟩
  invFun x := ⟨(l2.getDualInOther? l x).get (l2.mem_withUniqueDualInOther_isSome l x.1 x.2),
    by simp⟩
  left_inv x := SetCoe.ext (by simp)
  right_inv x := SetCoe.ext (by simp)

@[simp]
lemma getDualInOtherEquiv_self_refl : l.getDualInOtherEquiv l = Equiv.refl _ := by
  apply Equiv.ext
  intro x
  simp [getDualInOtherEquiv]

/-!

## Splitting withUniqueDual

-/

instance (i j : Option (Fin l.length)) : Decidable (i < j) :=
  match i, j with
  | none, none => isFalse (fun a => a)
  | none, some _ => isTrue (by trivial)
  | some _, none => isFalse (fun a => a)
  | some i, some j => Fin.decLt i j

def withUniqueDualLT : Finset (Fin l.length) :=
  Finset.filter (fun i => i < l.getDual? i) l.withUniqueDual

def withUniqueDualLTToWithUniqueDual (i : l.withUniqueDualLT) : l.withUniqueDual :=
  ⟨i.1, by
    have hi := i.2
    simp only [withUniqueDualLT, Finset.mem_filter] at hi
    exact hi.1⟩

instance : Coe l.withUniqueDualLT l.withUniqueDual where
  coe := l.withUniqueDualLTToWithUniqueDual

def withUniqueDualGT : Finset (Fin l.length) :=
  Finset.filter (fun i => ¬ i < l.getDual? i) l.withUniqueDual

def withUniqueDualGTToWithUniqueDual (i : l.withUniqueDualGT) : l.withUniqueDual :=
  ⟨i.1, by
    have hi := i.2
    simp only [withUniqueDualGT, Finset.mem_filter] at hi
    exact hi.1⟩

instance : Coe l.withUniqueDualGT l.withUniqueDual where
  coe := l.withUniqueDualGTToWithUniqueDual

lemma withUniqueDualLT_disjoint_withUniqueDualGT :
    Disjoint l.withUniqueDualLT l.withUniqueDualGT := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact @Finset.filter_inter_filter_neg_eq (Fin l.length) _ _ _ _ _

lemma withUniqueDualLT_union_withUniqueDualGT :
    l.withUniqueDualLT ∪ l.withUniqueDualGT = l.withUniqueDual :=
  Finset.filter_union_filter_neg_eq _ _

/-! TODO: Replace with a mathlib lemma. -/
lemma option_not_lt (i j : Option (Fin l.length)) : i < j → i ≠ j → ¬ j < i := by
  match i, j with
  | none, none =>
    intro _
    simp
  | none, some k =>
    intro _
    exact fun _ a => a
  | some i, none =>
    intro h
    exact fun _ _ => h
  | some i, some j =>
    intro h h'
    simp_all
    change i < j at h
    change ¬ j < i
    exact Fin.lt_asymm h

/-! TODO: Replace with a mathlib lemma. -/
lemma lt_option_of_not (i j : Option (Fin l.length)) : ¬ j < i → i ≠ j →  i < j  := by
  match i, j with
  | none, none =>
    intro _
    simp
  | none, some k =>
    intro _
    exact fun _ => trivial
  | some i, none =>
    intro h
    exact fun _ => h trivial
  | some i, some j =>
    intro h h'
    simp_all
    change ¬ j < i at h
    change  i < j
    omega

def withUniqueDualLTEquivGT : l.withUniqueDualLT ≃ l.withUniqueDualGT where
  toFun i := ⟨l.getDualEquiv i, by
    have hi := i.2
    simp [withUniqueDualGT]
    simp [getDualEquiv]
    simp [withUniqueDualLT] at hi
    apply option_not_lt
    simpa [withUniqueDualLTToWithUniqueDual] using hi.2
    exact Ne.symm (getDual?_neq_self l i)⟩
  invFun i := ⟨l.getDualEquiv.symm i, by
    have hi := i.2
    simp [withUniqueDualLT]
    simp [getDualEquiv]
    simp [withUniqueDualGT] at hi
    apply lt_option_of_not
    simpa [withUniqueDualLTToWithUniqueDual] using hi.2
    exact (getDual?_neq_self l i)⟩
  left_inv x := SetCoe.ext (by simp [withUniqueDualGTToWithUniqueDual,
    withUniqueDualLTToWithUniqueDual])
  right_inv x := SetCoe.ext (by simp [withUniqueDualGTToWithUniqueDual,
    withUniqueDualLTToWithUniqueDual])

def withUniqueLTGTEquiv : l.withUniqueDualLT ⊕ l.withUniqueDualLT ≃ l.withUniqueDual := by
  apply (Equiv.sumCongr (Equiv.refl _ ) l.withUniqueDualLTEquivGT).trans
  apply (Equiv.Finset.union _ _ l.withUniqueDualLT_disjoint_withUniqueDualGT).trans
  apply (Equiv.subtypeEquivRight (by simp [l.withUniqueDualLT_union_withUniqueDualGT]))

/-!

## withUniqueDualInOther equal univ

-/

lemma withUniqueDualInOther_eq_univ_fst_withDual_empty
    (h : l.withUniqueDualInOther l2 = Finset.univ)  : l.withDual = ∅ := by
  rw [@Finset.eq_empty_iff_forall_not_mem]
  intro x
  have hx : x ∈ l.withUniqueDualInOther l2 := by
    rw [h]
    simp
  rw [withUniqueDualInOther] at hx
  simp only [mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and] at hx
  simpa using hx.1

lemma withUniqueDualInOther_eq_univ_fst_eq_contrIndexList (h : l.withUniqueDualInOther l2 = Finset.univ) :
    l = l.contrIndexList := by
  refine Eq.symm (contrIndexList_of_withDual_empty l ?h)
  exact withUniqueDualInOther_eq_univ_fst_withDual_empty l l2 h

lemma withUniqueDualInOther_eq_univ_symm (hl : l.length = l2.length)
    (h : l.withUniqueDualInOther l2 = Finset.univ) :
    l2.withUniqueDualInOther l = Finset.univ := by
  let S' : Finset (Fin l2.length) :=
      Finset.map ⟨Subtype.val, Subtype.val_injective⟩
      (Equiv.finsetCongr
      (l.getDualInOtherEquiv l2) Finset.univ )
  have hSCard : S'.card = l2.length := by
    rw [Finset.card_map]
    simp
    rw [h, ← hl]
    simp
  have hsCardUn : S'.card = (@Finset.univ (Fin l2.length)).card := by
    rw [hSCard]
    simp
  have hS'Eq : S' =  (l2.withUniqueDualInOther l) := by
    rw [@Finset.ext_iff]
    intro a
    simp [S']
  rw [hS'Eq] at hsCardUn
  exact (Finset.card_eq_iff_eq_univ (l2.withUniqueDualInOther l)).mp hsCardUn

lemma withUniqueDualInOther_eq_univ_contr_refl :
    l.contrIndexList.withUniqueDualInOther l.contrIndexList = Finset.univ := by
  rw [@Finset.eq_univ_iff_forall]
  intro x
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome,
    Option.isSome_none, Bool.false_eq_true, not_false_eq_true, mem_withInDualOther_iff_isSome,
    getDualInOther?_self_isSome, true_and, Finset.mem_filter, Finset.mem_univ]
  simp only [contrIndexList_getDual?, Option.isSome_none, Bool.false_eq_true, not_false_eq_true,
    contrIndexList_getDualInOther?_self, Option.some.injEq, true_and]
  intro j hj
  have h1 : j = x := by
    by_contra hn
    have hj : l.contrIndexList.AreDualInSelf x j := by
      simp [AreDualInOther] at hj
      simp only [AreDualInSelf, ne_eq, contrIndexList_idMap, hj, and_true]
      exact fun a => hn (id (Eq.symm a))
    simp at hj
  simpa using h1

set_option maxHeartbeats 0
lemma withUniqueDualInOther_eq_univ_trans (h : l.withUniqueDualInOther l2 = Finset.univ)
    (h' : l2.withUniqueDualInOther l3 = Finset.univ) :
    l.withUniqueDualInOther l3 = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  intro i
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and]
  have hi : i ∈ l.withUniqueDualInOther l2 := by
    rw [h]
    simp
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi
  have hi2 : ((l.getDualInOther? l2 i).get hi.2.1) ∈ l2.withUniqueDualInOther l3 := by
    rw [h']
    simp
  simp only [withUniqueDualInOther, mem_withDual_iff_isSome, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, mem_withInDualOther_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi2
  apply And.intro hi.1
  apply And.intro
  · rw [@getDualInOther?_isSome_iff_exists]
    use (l2.getDualInOther? l3 ((l.getDualInOther? l2 i).get hi.2.1)).get hi2.2.1
    simp [AreDualInOther]
  intro j hj
  have hj' : j = (l2.getDualInOther? l3 ((l.getDualInOther? l2 i).get hi.2.1)).get hi2.2.1  := by
    rw [← eq_getDualInOther?_get_of_withUniqueDualInOther_iff]
    simpa [AreDualInOther] using hj
    rw [h']
    simp
  have hs : (l.getDualInOther? l3 i).isSome := by
    rw [@getDualInOther?_isSome_iff_exists]
    exact Exists.intro j hj
  have hs' : (l.getDualInOther? l3 i).get hs = (l2.getDualInOther? l3 ((l.getDualInOther? l2 i).get hi.2.1)).get hi2.2.1 := by
    rw [← eq_getDualInOther?_get_of_withUniqueDualInOther_iff]
    simp [AreDualInOther]
    rw [h']
    simp
  rw [← hj'] at hs'
  rw [← hs']
  simp



end IndexList

end IndexNotation
