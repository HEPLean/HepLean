/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.DualIndex
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Appending index lists and consquences thereof.

-/

namespace IndexNotation


namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 : IndexList X)

/-!

## Appending index lists.

-/

instance : HAppend (IndexList X) (IndexList X) (IndexList X) :=
    @instHAppendOfAppend (List (Index X)) List.instAppend

def appendEquiv {l l2 : IndexList X} : Fin l.length ⊕ Fin l2.length ≃ Fin (l ++ l2).length :=
  finSumFinEquiv.trans (Fin.castOrderIso (List.length_append _ _).symm).toEquiv

@[simp]
lemma idMap_append_inl {l l2 : IndexList X} (i : Fin l.length) :
    (l ++ l2).idMap (appendEquiv (Sum.inl i)) = l.idMap i := by
  simp [appendEquiv, idMap]
  rw [List.getElem_append_left]

@[simp]
lemma idMap_append_inr {l l2 : IndexList X} (i : Fin l2.length) :
    (l ++ l2).idMap (appendEquiv (Sum.inr i)) = l2.idMap i := by
  simp [appendEquiv, idMap]
  rw [List.getElem_append_right]
  simp
  omega
  omega

@[simp]
lemma colorMap_append_inl {l l2 : IndexList X} (i : Fin l.length) :
    (l ++ l2).colorMap (appendEquiv (Sum.inl i)) = l.colorMap i := by
  simp [appendEquiv, colorMap]
  rw [List.getElem_append_left]

@[simp]
lemma colorMap_append_inr {l l2 : IndexList X} (i : Fin l2.length) :
    (l ++ l2).colorMap (appendEquiv (Sum.inr i)) = l2.colorMap i := by
  simp [appendEquiv, colorMap]
  rw [List.getElem_append_right]
  simp
  omega
  omega


/-!

## AreDualInSelf

-/

namespace AreDualInSelf

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


/-!

## Member withDual append conditions

-/

@[simp]
lemma inl_mem_withDual_append_iff (i : Fin l.length) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withDual ↔ (i ∈ l.withDual ∨ i ∈ l.withDualInOther l2) := by
  simp only [mem_withDual_iff_exists, mem_withInDualOther_iff_exists]
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
lemma inr_mem_withDual_append_iff (i : Fin l2.length) :
    appendEquiv (Sum.inr i) ∈ (l ++ l2).withDual
    ↔ (i ∈ l2.withDual ∨ i ∈ l2.withDualInOther l) := by
  simp only [mem_withDual_iff_exists, mem_withInDualOther_iff_exists]
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

def appendInlWithDual (i : l.withDual) : (l ++ l2).withDual :=
  ⟨appendEquiv (Sum.inl i), by simp⟩


/-!

## getDual on appended lists

-/

@[simp]
lemma getDual?_append_inl_withDual (i : l.withDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = some (appendEquiv (Sum.inl (l.getDual! i))) := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inl_inl]
  apply And.intro (l.areDualInSelf_getDual! i)
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, ge_iff_le]
    rw [Fin.le_def]
    have h2 := l.getDual?_eq_some_getDual! i
    rw [getDual?, Fin.find_eq_some_iff] at h2
    exact h2.2 k (by simpa using hj)
  | Sum.inr k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, finSumFinEquiv_apply_right, ge_iff_le]
    rw [Fin.le_def]
    simp only [Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd]
    omega

@[simp]
lemma getDual_append_inl_withDual (i : l.withDual) :
    (l ++ l2).getDual ⟨appendEquiv (Sum.inl i), by simp⟩ =
    ⟨appendEquiv (Sum.inl (l.getDual i)), by simp⟩ := by
  simp [getDual, getDual!]

@[simp]
lemma getDual?_append_inl_not_withDual (i : Fin l.length) (hi : i ∉ l.withDual)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = some
      (appendEquiv (Sum.inr (l.getDualInOther! l2 ⟨i, by simp_all⟩)))  := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inl_inr]
  apply And.intro (l.areDualInOther_getDualInOther! l2 ⟨i, by simp_all⟩)
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    rw [AreDualInSelf.append_inl_inl] at hj
    simp only [withDual, getDual?, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true,
      Option.not_isSome, Option.isNone_iff_eq_none, Fin.find_eq_none_iff] at hi
    exact False.elim (hi k hj)
  | Sum.inr k =>
    simp [appendEquiv]
    rw [Fin.le_def]
    have h1 := l.getDualInOther?_eq_some_getDualInOther! l2 ⟨i, by simp_all⟩
    rw [getDualInOther?, Fin.find_eq_some_iff] at h1
    simp only [Fin.coe_cast, Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le, ge_iff_le]
    refine h1.2 k (by simpa using hj)

@[simp]
lemma getDual_append_inl_not_withDual (i : Fin l.length) (hi : i ∉ l.withDual)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withDual) :
    (l ++ l2).getDual ⟨appendEquiv (Sum.inl i), h⟩ =
    ⟨appendEquiv (Sum.inr (l.getDualInOther l2 ⟨i, by simp_all⟩)), by simp⟩ := by
  simp [getDual, getDual!, getDual?_append_inl_not_withDual l l2 i hi h]
  rfl

@[simp]
lemma getDual?_append_inr_withDualInOther (i : l2.withDualInOther l) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) =
    some (appendEquiv (Sum.inl (l2.getDualInOther! l i))) := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inr_inl]
  apply And.intro (l2.areDualInOther_getDualInOther! l ⟨i, by simp_all⟩)
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, ge_iff_le]
    rw [Fin.le_def]
    have h1 := l2.getDualInOther?_eq_some_getDualInOther! l ⟨i, by simp_all⟩
    rw [getDualInOther?, Fin.find_eq_some_iff] at h1
    simp only [Fin.coe_cast, Fin.coe_natAdd, add_le_add_iff_left, Fin.val_fin_le, ge_iff_le]
    refine h1.2 k (by simpa using hj)
  | Sum.inr k =>
    simp only [appendEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, finSumFinEquiv_apply_right, ge_iff_le]
    rw [Fin.le_def]
    simp only [Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd]
    omega

@[simp]
lemma getDual_append_inr_withDualInOther (i : l2.withDualInOther l) :
    (l ++ l2).getDual ⟨appendEquiv (Sum.inr i), by simp⟩ =
    ⟨appendEquiv (Sum.inl (l2.getDualInOther l i)), by simp⟩ := by
  simp [getDual, getDual!]
  rfl

@[simp]
lemma getDual?_append_inr_not_withDualInOther (i : Fin l2.length) (hi : i ∉ l2.withDualInOther l)
    (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withDual) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = some
    (appendEquiv (Sum.inr (l2.getDual! ⟨i, by simp_all⟩))) := by
  rw [getDual?, Fin.find_eq_some_iff, AreDualInSelf.append_inr_inr]
  apply And.intro (l2.areDualInSelf_getDual! ⟨i, by simp_all⟩)
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    simp at hj
    refine False.elim (hi ?_)
    simp [withDualInOther, getDualInOther?, Fin.isSome_find_iff]
    exact ⟨k, hj⟩
  | Sum.inr k =>
    simp [appendEquiv]
    rw [Fin.le_def]
    simp
    have h2 := l2.getDual?_eq_some_getDual! ⟨i, by simp_all⟩
    rw [getDual?, Fin.find_eq_some_iff] at h2
    simp only [AreDualInSelf.append_inr_inr] at hj
    exact h2.2 k hj

@[simp]
lemma getDual_append_inr_not_withDualInOther (i : Fin l2.length) (hi : i ∉ l2.withDualInOther l)
    (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withDual) :
    (l ++ l2).getDual ⟨appendEquiv (Sum.inr i), h⟩ =
    ⟨appendEquiv (Sum.inr (l2.getDual ⟨i, by simp_all⟩)), by simp⟩ := by
  simp [getDual, getDual!, getDual?_append_inr_not_withDualInOther l l2 i hi h]


@[simp]
lemma getDual?_append_inl (i : Fin l.length) : (l ++ l2).getDual? (appendEquiv (Sum.inl i)) =
    Option.or (Option.map (appendEquiv ∘ Sum.inl) (l.getDual? i))
    (Option.map (appendEquiv ∘ Sum.inr) (l.getDualInOther? l2 i)) := by
  by_cases h : (appendEquiv (Sum.inl i)) ∈ (l ++ l2).withDual
  · by_cases hl : i ∈ l.withDual
    · rw [(l ++ l2).getDual?_eq_some_getDual! ⟨(appendEquiv (Sum.inl i)), h⟩]
      rw [l.getDual?_eq_some_getDual! ⟨i, hl⟩]
      rw [getDual!]
      simp only [Option.some_get, Option.map_some', Function.comp_apply, Option.or_some]
      exact getDual?_append_inl_withDual l l2 ⟨i, hl⟩
    · let h' := h
      rw [l.getDual?_eq_none_on_not_mem i hl]
      simp only [inl_mem_withDual_append_iff] at h
      simp_all only [false_or, Option.map_none', Option.none_or]
      rw [l.getDualInOther?_eq_some_getDualInOther! l2 ⟨i, h⟩]
      rw [getDual?_append_inl_not_withDual l l2 i hl h']
      rfl
  · rw [(l ++ l2).getDual?_eq_none_on_not_mem _ h]
    simp only [inl_mem_withDual_append_iff, not_or, not_exists] at h
    rw [l.getDual?_eq_none_on_not_mem _ h.1, l.getDualInOther?_eq_none_on_not_mem l2 _ h.2]
    rfl

@[simp]
lemma getDual?_append_inr (i : Fin l2.length) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) =
    Option.or (Option.map (appendEquiv ∘ Sum.inl) (l2.getDualInOther? l i))
    (Option.map (appendEquiv ∘ Sum.inr) (l2.getDual? i)) := by
  by_cases h : (appendEquiv (Sum.inr i)) ∈ (l ++ l2).withDual
  · by_cases hl1 : i ∈ l2.withDualInOther l
    · rw [(l ++ l2).getDual?_eq_some_getDual! ⟨(appendEquiv (Sum.inr i)), h⟩]
      rw [l2.getDualInOther?_eq_some_getDualInOther! l ⟨i, hl1⟩]
      rw [getDual!]
      simp only [Option.some_get, Option.map_some', Function.comp_apply, Option.or_some]
      exact getDual?_append_inr_withDualInOther l l2 ⟨i, hl1⟩
    · have h' := h
      rw [l2.getDualInOther?_eq_none_on_not_mem l i hl1]
      simp only [inr_mem_withDual_append_iff, not_exists] at h hl1
      simp_all only [not_exists, exists_false, or_false,
        Option.map_none', Option.none_or]
      rw [l2.getDual?_eq_some_getDual! ⟨i, h⟩]
      simp only [Option.map_some', Function.comp_apply]
      exact getDual?_append_inr_not_withDualInOther l l2 i hl1 h'
  · rw [(l ++ l2).getDual?_eq_none_on_not_mem _ h]
    simp only [inr_mem_withDual_append_iff, not_or, not_exists] at h
    rw [l2.getDual?_eq_none_on_not_mem _ h.1, l2.getDualInOther?_eq_none_on_not_mem l _ h.2]
    rfl


/-!

## withUniqueDualInOther append conditions

-/

lemma append_inl_not_mem_withDual_of_withDualInOther (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l.withDual ↔ ¬ i ∈ l.withDualInOther l2 := by
  apply Iff.intro
  · intro hs
    by_contra ho
    obtain ⟨j, hj⟩ := (l.mem_withDual_iff_exists).mp hs
    obtain ⟨k, hk⟩ := (l.mem_withInDualOther_iff_exists l2).mp ho
    have h1 : appendEquiv (Sum.inl j) = appendEquiv (Sum.inr k) := by
      refine (l ++ l2).eq_of_areDualInSelf_withUniqueDual ⟨appendEquiv (Sum.inl i), h⟩ ?_ ?_
      simpa using hj
      simpa using hk
    simp at h1
  · intro ho
    by_contra hs
    have h1 :  appendEquiv (Sum.inl i) ∈ (l ++ l2).withDual := by
      exact (l ++ l2).mem_withDual_of_withUniqueDual ⟨appendEquiv (Sum.inl i), h⟩
    obtain ⟨j, hj⟩ := ((l ++ l2).mem_withDual_iff_exists).mp h1
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      rw [mem_withDual_iff_exists] at hs
      simp_all
    | Sum.inr k =>
      rw [mem_withInDualOther_iff_exists] at ho
      simp_all

lemma append_inr_not_mem_withDual_of_withDualInOther (i : Fin l2.length)
    (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l2.withDual ↔ ¬ i ∈ l2.withDualInOther l := by
  apply Iff.intro
  · intro hs
    by_contra ho
    obtain ⟨j, hj⟩ := (l2.mem_withDual_iff_exists).mp hs
    obtain ⟨k, hk⟩ := (l2.mem_withInDualOther_iff_exists l).mp ho
    have h1 : appendEquiv (Sum.inr j) = appendEquiv (Sum.inl k) := by
      refine (l ++ l2).eq_of_areDualInSelf_withUniqueDual ⟨appendEquiv (Sum.inr i), h⟩ ?_ ?_
      simpa using hj
      simpa using hk
    simp at h1
  · intro ho
    by_contra hs
    have h1 :  appendEquiv (Sum.inr i) ∈ (l ++ l2).withDual := by
      exact (l ++ l2).mem_withDual_of_withUniqueDual ⟨appendEquiv (Sum.inr i), h⟩
    obtain ⟨j, hj⟩ := ((l ++ l2).mem_withDual_iff_exists).mp h1
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      rw [mem_withInDualOther_iff_exists] at ho
      simp_all
    | Sum.inr k =>
      rw [mem_withDual_iff_exists] at hs
      simp_all


lemma append_inr_mem_withUniqueDual_of_append_inl (i : Fin l.length)
    (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    appendEquiv (Sum.inr i) ∈ (l2 ++ l).withUniqueDual := by
  have hinj : Function.Injective (Option.map (@appendEquiv _ _ l l2 ∘ Sum.inr)) := by
          apply Option.map_injective
          rw [@Equiv.comp_injective]
          exact Sum.inr_injective
  let h' := h
  simp [withUniqueDual] at h ⊢
  apply And.intro h.1
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    have h1 := h.2 (appendEquiv (Sum.inr k))
    simp at h1 hj
    have h2 := h1 hj
    by_cases hs : i ∈ l.withDual <;> rename_i hs
    · rw [l.getDual?_eq_some_getDual! ⟨i, hs⟩] at h2
      simp at h2
    · rw [l.getDual?_eq_none_on_not_mem i hs] at h2
      simp at h2
      rw [← Option.map_some', ← Option.map_some', Option.map_map] at h2
      rw [← hinj h2]
      rfl
  | Sum.inr k =>
    have h1 := h.2 (appendEquiv (Sum.inl k))
    simp at h1 hj
    have h2 := h1 hj
    by_cases hs : i ∈ l.withDual <;> rename_i hs
    · rw [l.getDual?_eq_some_getDual! ⟨i, hs⟩] at h2
      simp only [Option.map_some', Function.comp_apply, Option.or_some, Option.some.injEq,
        EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] at h2
      have ho := (l.append_inl_not_mem_withDual_of_withDualInOther l2 i h').mp hs
      rw [l.getDualInOther?_eq_none_on_not_mem _ _ ho]
      simp only [Option.map_none', Option.none_or]
      rw [← Option.map_some', ← Option.map_some', Option.map_map, h2]
      simp [some_dual!_eq_gual?]
    · have ho := (l.append_inl_not_mem_withDual_of_withDualInOther l2 i h').mpr.mt hs
      simp at ho
      rw [l.getDualInOther?_eq_some_getDualInOther! l2 ⟨i, ho⟩] at h2 ⊢
      simp at h2
      simp
      rw [l.getDual?_eq_none_on_not_mem _ hs] at h2
      simp at h2

lemma withUniqueDual_iff_not_withUniqueDualInOther_of_inl_withUniqueDualInOther
    (i : Fin l.length) (h : appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l.withUniqueDual ↔ ¬ i ∈ l.withUniqueDualInOther l2 := by
  have h' := h
  rw [withUniqueDual] at h
  simp only [Finset.mem_filter, Finset.mem_univ, inl_mem_withDual_append_iff,
    getDual?_append_inl, true_and] at h
  simp [withUniqueDual, withUniqueDualInOther]
  cases' h.1 with h1 h1
  · simp [h1]
    intro j hj
    have hj' := h.2 (appendEquiv (Sum.inl j))
    simp at hj'
    have hj'' := hj' hj
    rw [l.getDual?_eq_some_getDual! ⟨i, by rw [mem_withDual_iff_exists]; exact ⟨j, hj⟩⟩] at hj'' ⊢
    simpa using hj''
  · have hn := l.append_inl_not_mem_withDual_of_withDualInOther l2 i h'
    simp_all
    intro j hj
    have hj' := h (appendEquiv (Sum.inr j))
    simp at hj'
    have hj'' := hj' hj
    rw [l.getDual?_eq_none_on_not_mem _ hn] at hj''
    simp at hj''
    rw [l.getDualInOther?_eq_some_getDualInOther!
      l2 ⟨i, by rw [mem_withInDualOther_iff_exists]; exact ⟨j, hj⟩⟩] at hj'' ⊢
    simpa using hj''

lemma withUniqueDual_iff_not_withUniqueDualInOther_of_inr_withUniqueDualInOther
    (i : Fin l2.length) (h : appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual) :
    i ∈ l2.withUniqueDual ↔ ¬ i ∈ l2.withUniqueDualInOther l := by
  have h' := h
  rw [withUniqueDual] at h
  simp only [Finset.mem_filter, Finset.mem_univ, inr_mem_withDual_append_iff, getDual?_append_inr,
    true_and] at h
  simp [withUniqueDual, withUniqueDualInOther]
  cases' h.1 with h1 h1
  · have hn := (l.append_inr_not_mem_withDual_of_withDualInOther l2 i h').mp h1
    simp [h1]
    intro j hj
    have hj' := h.2 (appendEquiv (Sum.inr j))
    simp at hj'
    have hj'' := hj' hj
    rw [l2.getDual?_eq_some_getDual! ⟨i, by rw [mem_withDual_iff_exists]; exact ⟨j, hj⟩⟩] at hj'' ⊢
    rw [l2.getDualInOther?_eq_none_on_not_mem _ _ hn] at hj''
    simpa using hj''
  · have hn := l.append_inr_not_mem_withDual_of_withDualInOther l2 i h'
    simp_all
    intro j hj
    have hj' := h (appendEquiv (Sum.inl j))
    simp at hj'
    have hj'' := hj' hj
    rw [l2.getDual?_eq_none_on_not_mem _ hn] at hj''
    simp at hj''
    rw [l2.getDualInOther?_eq_some_getDualInOther!
      l ⟨i, by rw [mem_withInDualOther_iff_exists]; exact ⟨j, hj⟩⟩] at hj'' ⊢
    simpa using hj''

lemma append_inl_mem_withUniqueDual_of_withUniqueDual (i : Fin l.length)
    (h : i ∈ l.withUniqueDual) (hn : i ∉ l.withDualInOther l2) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
  simp [withUniqueDual]
  apply And.intro (Or.inl (l.mem_withDual_of_withUniqueDual ⟨i, h⟩))
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    rw [l.getDual?_eq_some_getDual! ⟨i, l.mem_withDual_of_withUniqueDual ⟨i, h⟩⟩]
    simp
    rw [← l.eq_getDual_of_withUniqueDual_iff ⟨i, h⟩ k]
    simpa using hj
  | Sum.inr k =>
    simp at hj
    refine False.elim (hn ?_)
    exact (l.mem_withInDualOther_iff_exists _).mpr ⟨k, hj⟩

lemma append_inl_mem_of_withUniqueDualInOther (i : Fin l.length) (ho : i ∈ l.withUniqueDualInOther l2) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
  simp [withUniqueDual]
  apply And.intro (Or.inr (l.mem_withDualInOther_of_withUniqueDualInOther l2 ⟨i, ho⟩))
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  have hs := l.not_mem_withDual_of_withUniqueDualInOther l2 ⟨i, ho⟩
  rw [l.getDual?_eq_none_on_not_mem _ hs]
  rw [l.getDualInOther?_eq_some_getDualInOther! l2
      ⟨i, (l.mem_withDualInOther_of_withUniqueDualInOther l2 ⟨i, ho⟩)⟩]
  match k with
  | Sum.inl k =>
    refine False.elim (hs ?_)
    simp at hj
    exact (l.mem_withDual_iff_exists).mpr ⟨k, hj⟩
  | Sum.inr k =>
    simp at hj
    simp
    erw [← l.eq_getDualInOther_of_withUniqueDual_iff l2 ⟨i, ho⟩ k]
    simpa using hj

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

lemma append_inl_mem_withUniqueDual_of_append_inr (i : Fin l.length)
    (h : appendEquiv (Sum.inr i) ∈ (l2 ++ l).withUniqueDual) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual := by
  simp
  apply Iff.intro
  · intro hs
    exact (l2.withUniqueDual_iff_not_withUniqueDualInOther_of_inr_withUniqueDualInOther
      l i h).mp hs.1
  · intro ho
    have hs := (l2.withUniqueDual_iff_not_withUniqueDualInOther_of_inr_withUniqueDualInOther
      l i h).mpr ho
    apply And.intro hs
    refine (l2.append_inr_not_mem_withDual_of_withDualInOther l i h).mp ?_
    exact (l.mem_withDual_of_withUniqueDual ⟨i, hs⟩)

  lemma append_mem_withUniqueDual_symm (i : Fin l.length) :
      appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual ↔
      appendEquiv (Sum.inr i) ∈ (l2 ++ l).withUniqueDual := by
    apply Iff.intro
    · intro h'
      exact append_inr_mem_withUniqueDual_of_append_inl l l2 i h'
    · intro h'
      exact append_inl_mem_withUniqueDual_of_append_inr l l2 i h'

@[simp]
lemma append_inr_mem_withUniqueDual_iff (i : Fin l2.length) :
    appendEquiv (Sum.inr i) ∈ (l ++ l2).withUniqueDual ↔
    ((i ∈ l2.withUniqueDual ∧ i ∉ l2.withDualInOther l) ↔ ¬ i ∈ l2.withUniqueDualInOther l) := by
  rw [← append_mem_withUniqueDual_symm]
  simp


end IndexList

end IndexNotation
