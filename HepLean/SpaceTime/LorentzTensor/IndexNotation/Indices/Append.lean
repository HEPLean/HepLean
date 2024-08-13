/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.UniqueDualInOther
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.UniqueDual
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Appending index lists and consquences thereof.

-/

namespace IndexNotation


namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

/-!

## Appending index lists.

-/

instance : HAppend (IndexList X) (IndexList X) (IndexList X) where
  hAppend := fun l l2 => {val := l.val ++ l2.val}

lemma append_assoc : l ++ l2 ++ l3 = l ++ (l2 ++ l3) := by
  apply ext
  change l.val ++ l2.val ++ l3.val = l.val ++ (l2.val ++ l3.val)
  exact List.append_assoc l.val l2.val l3.val

def appendEquiv {l l2 : IndexList X} : Fin l.length ⊕ Fin l2.length ≃ Fin (l ++ l2).length :=
  finSumFinEquiv.trans (Fin.castOrderIso (List.length_append _ _).symm).toEquiv

def appendInl : Fin l.length ↪ Fin (l ++ l2).length where
  toFun := appendEquiv ∘ Sum.inl
  inj' := by
    intro i j h
    simp [Function.comp] at h
    exact h

def appendInr : Fin l2.length ↪ Fin (l ++ l2).length where
  toFun := appendEquiv ∘ Sum.inr
  inj' := by
    intro i j h
    simp [Function.comp] at h
    exact h

@[simp]
lemma appendInl_appendEquiv :
    (l.appendInl l2).trans appendEquiv.symm.toEmbedding =
    {toFun := Sum.inl, inj' := Sum.inl_injective} := by
  ext i
  simp [appendInl]

@[simp]
lemma appendInr_appendEquiv :
    (l.appendInr l2).trans appendEquiv.symm.toEmbedding =
    {toFun := Sum.inr, inj' := Sum.inr_injective} := by
  ext i
  simp [appendInr]

@[simp]
lemma append_val {l l2 : IndexList X} : (l ++ l2).val = l.val ++ l2.val := by
  rfl

@[simp]
lemma idMap_append_inl {l l2 : IndexList X} (i : Fin l.length) :
    (l ++ l2).idMap (appendEquiv (Sum.inl i)) = l.idMap i := by
  simp [appendEquiv, idMap]
  rw [List.getElem_append_left]
  rfl

@[simp]
lemma idMap_append_inr {l l2 : IndexList X} (i : Fin l2.length) :
    (l ++ l2).idMap (appendEquiv (Sum.inr i)) = l2.idMap i := by
  simp [appendEquiv, idMap, IndexList.length]
  rw [List.getElem_append_right]
  simp
  omega
  omega

@[simp]
lemma colorMap_append_inl {l l2 : IndexList X} (i : Fin l.length) :
    (l ++ l2).colorMap (appendEquiv (Sum.inl i)) = l.colorMap i := by
  simp [appendEquiv, colorMap, IndexList.length]
  rw [List.getElem_append_left]

@[simp]
lemma colorMap_append_inl' :
    (l ++ l2).colorMap ∘ appendEquiv ∘ Sum.inl = l.colorMap := by
  funext i
  simp

@[simp]
lemma colorMap_append_inr {l l2 : IndexList X} (i : Fin l2.length) :
    (l ++ l2).colorMap (appendEquiv (Sum.inr i)) = l2.colorMap i := by
  simp [appendEquiv, colorMap, IndexList.length]
  rw [List.getElem_append_right]
  simp
  omega
  omega

@[simp]
lemma colorMap_append_inr' :
    (l ++ l2).colorMap ∘ appendEquiv ∘ Sum.inr = l2.colorMap := by
  funext i
  simp

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
lemma inl_getDual?_isSome_iff (i : Fin l.length) :
    ((l ++ l2).getDual? (appendEquiv (Sum.inl i))).isSome ↔
    ((l.getDual? i).isSome ∨ (l.getDualInOther? l2 i).isSome) := by
  simpa using l.inl_mem_withDual_append_iff l2 i

@[simp]
lemma inl_getDual?_eq_none_iff (i : Fin l.length) :
    (l ++ l2).getDual? (appendEquiv (Sum.inl i)) = none ↔
    (l.getDual? i = none ∧ l.getDualInOther? l2 i = none) := by
  apply Iff.intro
  · intro h
    have h1 := (l.inl_getDual?_isSome_iff l2 i).mpr.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h
  · intro h
    have h1 := (l.inl_getDual?_isSome_iff l2 i).mp.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h

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
@[simp]
lemma inr_getDual?_isSome_iff (i : Fin l2.length) :
    ((l ++ l2).getDual? (appendEquiv (Sum.inr i))).isSome ↔
    ((l2.getDual? i).isSome ∨ (l2.getDualInOther? l i).isSome) := by
  simpa using l.inr_mem_withDual_append_iff l2 i

@[simp]
lemma inr_getDual?_eq_none_iff (i : Fin l2.length) :
    (l ++ l2).getDual? (appendEquiv (Sum.inr i)) = none ↔
    (l2.getDual? i = none ∧ l2.getDualInOther? l i = none) := by
  apply Iff.intro
  · intro h
    have h1 := (l.inr_getDual?_isSome_iff l2 i).mpr.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h
  · intro h
    have h1 := (l.inr_getDual?_isSome_iff l2 i).mp.mt
    simp only [not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, imp_self] at h1
    exact h1 h

lemma append_getDual?_isSome_symm (i : Fin l.length) :
    ((l ++ l2).getDual? (appendEquiv (Sum.inl i))).isSome ↔
    ((l2 ++ l).getDual? (appendEquiv (Sum.inr i))).isSome := by
  simp

@[simp]
lemma getDual?_inl_of_getDual?_isSome (i : Fin l.length) (h : (l.getDual? i).isSome) :
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
  apply And.intro (l2.areDualInOther_getDualInOther! l ⟨i, by simp_all⟩)
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
  apply And.intro (l2.areDualInSelf_getDual! ⟨i, by simp_all⟩)
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

## Properties of the finite set withDual.

-/

def appendInlWithDual (i : l.withDual) : (l ++ l2).withDual :=
  ⟨appendEquiv (Sum.inl i), by simp⟩

lemma append_withDual : (l ++ l2).withDual =
    (Finset.map (l.appendInl l2) (l.withDual ∪ l.withDualInOther l2)) ∪
    (Finset.map (l.appendInr l2) (l2.withDual ∪ l2.withDualInOther l)) := by
  ext i
  obtain ⟨k, hk⟩ := appendEquiv.surjective i
  subst hk
  match k with
  | Sum.inl k =>
    simp
    apply Iff.intro
    intro h
    · apply Or.inl
      use k
      simp_all [appendInl]
    · intro h
      cases' h with h h
      · obtain ⟨j, hj⟩ := h
        simp  [appendInl] at hj
        have hj2 := hj.2
        subst hj2
        exact hj.1
      · obtain ⟨j, hj⟩ := h
        simp [appendInr] at hj
  | Sum.inr k =>
    simp
    apply Iff.intro
    intro h
    · apply Or.inr
      use k
      simp_all [appendInr]
    · intro h
      cases' h with h h
      · obtain ⟨j, hj⟩ := h
        simp [appendInl] at hj
      · obtain ⟨j, hj⟩ := h
        simp [appendInr] at hj
        have hj2 := hj.2
        subst hj2
        exact hj.1

lemma append_withDual_disjSum : (l ++ l2).withDual =
    Equiv.finsetCongr appendEquiv
      ((l.withDual ∪ l.withDualInOther l2).disjSum
      (l2.withDual ∪ l2.withDualInOther l)) := by
  rw [← Equiv.symm_apply_eq]
  simp [append_withDual]
  rw [Finset.map_union]
  rw [Finset.map_map, Finset.map_map]
  ext1 a
  cases a with
  | inl val => simp
  | inr val_1 => simp


/-!

## withUniqueDualInOther append conditions

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
    simp only [inl_getDual?_isSome_iff] at ht
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
    simp only [inr_getDual?_isSome_iff] at ht
    simp_all

/-!

## getDual? apply symmetry.

-/
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

/-!

## mem withUniqueDual symmetry

-/

lemma mem_withUniqueDual_append_symm (i : Fin l.length) :
    appendEquiv (Sum.inl i) ∈ (l ++ l2).withUniqueDual ↔
    appendEquiv (Sum.inr i) ∈ (l2 ++ l).withUniqueDual := by
  simp only [withUniqueDual, mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ,
    inl_getDual?_isSome_iff, true_and, inr_getDual?_isSome_iff, and_congr_right_iff]
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
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, inl_getDual?_isSome_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        Option.some_get]
    | Sum.inr k =>
      have hk' :=  h' (appendEquiv (Sum.inl k))
      simp only [AreDualInSelf.append_inl_inl] at hk'
      simp only [AreDualInSelf.append_inr_inr] at hj
      refine  ((l.getDual?_append_symm_of_withUniqueDual_of_inl' l2 _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inl_inr, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, inl_getDual?_isSome_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        Option.some_get]
  · obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      have hk' := h' (appendEquiv (Sum.inr k))
      simp only [AreDualInSelf.append_inr_inr] at hk'
      simp only [AreDualInSelf.append_inl_inl] at hj
      refine ((l2.getDual?_append_symm_of_withUniqueDual_of_inr' l _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inr_inr, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, inr_getDual?_isSome_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        Option.some_get]
    | Sum.inr k =>
      have hk' :=  h' (appendEquiv (Sum.inl k))
      simp only [AreDualInSelf.append_inr_inl] at hk'
      simp only [AreDualInSelf.append_inl_inr] at hj
      refine  ((l2.getDual?_append_symm_of_withUniqueDual_of_inr l _ _ ?_).mp (hk' hj).symm).symm
      simp_all only [AreDualInSelf.append_inr_inr, imp_self, withUniqueDual,
        mem_withDual_iff_isSome, Finset.mem_filter, Finset.mem_univ, inr_getDual?_isSome_iff,
        implies_true, and_self, mem_withUniqueDual_isSome, eq_getDual?_get_of_withUniqueDual_iff,
        Option.some_get]

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
    inl_getDual?_isSome_iff, true_and] at h ⊢
  apply And.intro hi
  intro j hj
  have hj' := h.2 (appendEquiv (Sum.inl j))
  simp at hj'
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
    inl_getDual?_isSome_iff, true_and] at h
  have hj' := h.2 (appendEquiv (Sum.inr j))
  simp only [AreDualInSelf.append_inl_inr] at hj'
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
    inl_getDual?_isSome_iff, true_and]
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

lemma append_withDual_eq_withUniqueDual_iff :
    (l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    ((l.withUniqueDual ∩ (l.withDualInOther l2)ᶜ) ∪ l.withUniqueDualInOther l2)
    = l.withDual ∪ l.withDualInOther l2
    ∧ (l2.withUniqueDual ∩ (l2.withDualInOther l)ᶜ) ∪ l2.withUniqueDualInOther l
    =  l2.withDual ∪ l2.withDualInOther l := by
  rw [append_withUniqueDual_disjSum, append_withDual_disjSum]
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

/-!

## AreDualInOther append conditions
-/
namespace AreDualInOther
variable {l l2 l3 : IndexList X}

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

## Append and getDualInOther?

-/
variable (l3 : IndexList X)

@[simp]
lemma getDualInOther?_append_inl (i : Fin l.length) :
    (l ++ l2).getDualInOther? l3 (appendEquiv (Sum.inl i)) = l.getDualInOther? l3 i := by
  simp [getDualInOther?]

/-!

## append in other

-/


lemma append_withDualInOther_eq :
    (l ++ l2).withDualInOther l3 =
    Equiv.finsetCongr appendEquiv ((l.withDualInOther l3).disjSum (l2.withDualInOther l3)) := by
  rw [Finset.ext_iff]
  intro i
  simp

  sorry

lemma withDualInOther_append_eq :
    l.withDualInOther (l2 ++ l3) =
    l.withDualInOther l2 ∪ l.withDualInOther l3 := by
  sorry

end IndexList

end IndexNotation
