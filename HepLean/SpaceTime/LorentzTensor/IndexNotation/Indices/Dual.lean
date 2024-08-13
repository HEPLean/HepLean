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

@[simp]
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
  simp
  have h1 := (l.withoutDualEquiv (Fin.cast l.contrIndexList_length i)).2
  have h1' := Finset.disjoint_right.mp l.withDual_disjoint_withoutDual h1
  rw [mem_withDual_iff_exists] at h1'
  simp at h1'
  exact fun x => h1' ↑(l.withoutDualEquiv (Fin.cast (contrIndexList_length l) x))

@[simp]
lemma contrIndexList_withDual : l.contrIndexList.withDual = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro x
  simp [withDual]

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

end IndexList

end IndexNotation
