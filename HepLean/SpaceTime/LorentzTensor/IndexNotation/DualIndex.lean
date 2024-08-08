/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Basic
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

instance (i j : Fin l.length) : Decidable (l.AreDualInSelf i j) :=
  instDecidableAnd

def AreDualInOther {l : IndexList X} {l2 : IndexList X} (i : Fin l.length) (j : Fin l2.length) :
    Prop := l.idMap i = l2.idMap j

instance {l : IndexList X} {l2 : IndexList X}  (i : Fin l.length) (j : Fin l2.length) :
    Decidable (AreDualInOther i j) := (l.idMap i).decEq (l2.idMap j)


namespace AreDualInSelf

variable {l l2 : IndexList X} {i j : Fin l.length}

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
    AreDualInOther i j := by
  simp [AreDualInSelf, AreDualInOther]

@[simp]
lemma append_inr_inl (l l2 : IndexList X) (i : Fin l2.length) (j : Fin l.length) :
    (l ++ l2).AreDualInSelf (appendEquiv (Sum.inr i)) (appendEquiv (Sum.inl j)) =
    AreDualInOther i j := by
  simp [AreDualInSelf, AreDualInOther]

end AreDualInSelf

namespace AreDualInOther

variable {l l2 : IndexList X} {i : Fin l.length} {j : Fin l2.length}

@[symm]
lemma symm  (h : AreDualInOther i j) : AreDualInOther j i := by
  rw [AreDualInOther] at h ⊢
  exact h.symm

end AreDualInOther

/-!

## Has a dual

-/

def HasDualInSelf (i : Fin l.length) : Prop := ∃ j, AreDualInSelf l i j

instance (i : Fin l.length) : Decidable (l.HasDualInSelf i) := Fintype.decidableExistsFintype

def HasDualInOther (i : Fin l.length) : Prop :=
  ∃ (j : Fin l2.length), AreDualInOther i j

instance (i : Fin l.length) : Decidable (l.HasDualInOther l2 i) := Fintype.decidableExistsFintype

namespace HasDualInSelf

variable {l l2 : IndexList X} {i : Fin l.length}

@[simp]
lemma append_inl : (l ++ l2).HasDualInSelf (appendEquiv (Sum.inl i)) ↔
    (l.HasDualInSelf i ∨ l.HasDualInOther l2 i) := by
  apply Iff.intro
  · intro h
    obtain ⟨j, hj⟩ := h
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      apply Or.inl
      simp only [AreDualInSelf, ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq,
        idMap_append_inl] at hj
      exact ⟨k, hj⟩
    | Sum.inr k =>
      apply Or.inr
      simp only [AreDualInSelf, ne_eq, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true,
        idMap_append_inl, idMap_append_inr, true_and] at hj
      exact ⟨k, hj⟩
  · intro h
    cases h
    · rename_i h
      obtain ⟨j, hj⟩ := h
      use appendEquiv (Sum.inl j)
      simp only [AreDualInSelf, ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq,
        idMap_append_inl]
      exact hj
    · rename_i h
      obtain ⟨j, hj⟩ := h
      use appendEquiv (Sum.inr j)
      simp only [AreDualInSelf, ne_eq, EmbeddingLike.apply_eq_iff_eq, not_false_eq_true,
        idMap_append_inl, idMap_append_inr, true_and]
      exact hj

@[simp]
lemma append_inr {i : Fin l2.length} : (l ++ l2).HasDualInSelf (appendEquiv (Sum.inr i)) ↔
    (l2.HasDualInSelf i ∨ l2.HasDualInOther l i) := by
  apply Iff.intro
  · intro h
    obtain ⟨j, hj⟩ := h
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp [AreDualInSelf, ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq,
        idMap_append_inl] at hj
      exact Or.inr ⟨k, hj⟩
    | Sum.inr k =>
      simp only [AreDualInSelf, ne_eq, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq,
        idMap_append_inr] at hj
      exact Or.inl ⟨k, hj⟩
  · intro h
    cases h
    · rename_i h
      obtain ⟨j, hj⟩ := h
      use appendEquiv (Sum.inr j)
      simp [AreDualInSelf]
      exact hj
    · rename_i h
      obtain ⟨j, hj⟩ := h
      use appendEquiv (Sum.inl j)
      simp [AreDualInSelf]
      exact hj

def getFirst (h : l.HasDualInSelf i) : Fin l.length :=
  (Fin.find (l.AreDualInSelf i)).get (by simpa [Fin.isSome_find_iff] using h)

lemma some_getFirst_eq_find  (h : l.HasDualInSelf i)  :
    Fin.find (l.AreDualInSelf i) = some h.getFirst := by
  simp [getFirst]

lemma getFirst_hasDualInSelf (h : l.HasDualInSelf i) :
    l.HasDualInSelf h.getFirst := by
  have h := h.some_getFirst_eq_find
  rw [Fin.find_eq_some_iff] at h
  simp [HasDualInSelf]
  exact ⟨i, And.intro (fun a => h.1.1 a.symm) h.1.2.symm⟩

lemma areDualInSelf_getFirst (h : l.HasDualInSelf i) : l.AreDualInSelf i h.getFirst := by
  have h := h.some_getFirst_eq_find
  rw [Fin.find_eq_some_iff] at h
  simp [AreDualInSelf]
  exact h.1

@[simp]
lemma getFirst_id (h : l.HasDualInSelf i) : l.idMap h.getFirst = l.idMap i :=
  h.areDualInSelf_getFirst.2.symm

end HasDualInSelf

namespace HasDualInOther

variable {l l2 : IndexList X} {i : Fin l.length}

def getFirst {l : IndexList X} {l2 : IndexList X} (i : Fin l.length) (h : l.HasDualInOther l2 i) :
    Fin l2.length :=
  (Fin.find (l.AreDualInOther i)).get (by simpa [Fin.isSome_find_iff] using h)

lemma some_getFirst_eq_find (h : l.HasDualInOther l2 i) :
    Fin.find (l.AreDualInOther i) = some h.getFirst := by
  simp [getFirst]

lemma getFirst_hasDualInOther (h : l.HasDualInOther l2 i) :
    l2.HasDualInOther l h.getFirst := by
  have h := h.some_getFirst_eq_find
  rw [Fin.find_eq_some_iff] at h
  simp only [HasDualInOther]
  exact ⟨i, h.1.symm⟩

lemma areDualInOther_getFirst (h : l.HasDualInOther l2 i) :
    l.AreDualInOther i h.getFirst := by
  have h := h.some_getFirst_eq_find
  rw [Fin.find_eq_some_iff] at h
  simp [AreDualInOther]
  exact h.1

@[simp]
lemma getFirst_id (h : l.HasDualInOther l2 i) : l2.idMap h.getFirst = l.idMap i :=
  h.areDualInOther_getFirst.symm

end HasDualInOther

namespace HasDualInSelf


@[simp]
lemma getFirst_append_inl_of_hasDualInSelf (h : (l ++ l2).HasDualInSelf (appendEquiv (Sum.inl i)))
    (hi : l.HasDualInSelf i) : h.getFirst = appendEquiv (Sum.inl hi.getFirst) := by
  have h1 : Fin.find ((l ++ l2).AreDualInSelf (appendEquiv (Sum.inl i))) =
      some (appendEquiv (Sum.inl hi.getFirst)) := by
    rw [Fin.find_eq_some_iff]
    simp
    apply And.intro hi.areDualInSelf_getFirst
    intro j hj
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp [appendEquiv]
      rw [Fin.le_def]
      simp
      have h2 := hi.some_getFirst_eq_find
      rw [Fin.find_eq_some_iff] at h2
      simp only [AreDualInSelf.append_inl_inl] at hj
      exact h2.2 k hj
    | Sum.inr k =>
      simp [appendEquiv]
      rw [Fin.le_def]
      simp
      omega
  rw [h.some_getFirst_eq_find] at h1
  simpa only [Option.some.injEq] using h1

@[simp]
lemma getFirst_append_inl_of_not_hasDualInSelf
    (h : (l ++ l2).HasDualInSelf (appendEquiv (Sum.inl i)))
    (hi : ¬ l.HasDualInSelf i) (hn : l.HasDualInOther l2 i) :
    h.getFirst = appendEquiv (Sum.inr hn.getFirst) := by
  have h1 : Fin.find ((l ++ l2).AreDualInSelf (appendEquiv (Sum.inl i))) =
      some (appendEquiv (Sum.inr hn.getFirst)) := by
    rw [Fin.find_eq_some_iff]
    simp
    apply And.intro hn.areDualInOther_getFirst
    intro j hj
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp at hj
      exact False.elim (hi ⟨k, hj⟩)
    | Sum.inr k =>
      simp [appendEquiv]
      rw [Fin.le_def]
      simp
      have h2 := hn.some_getFirst_eq_find
      rw [Fin.find_eq_some_iff] at h2
      simp only [AreDualInSelf.append_inl_inr] at hj
      exact h2.2 k hj
  rw [h.some_getFirst_eq_find] at h1
  simpa only [Option.some.injEq] using h1

@[simp]
lemma getFirst_append_inr_of_hasDualInOther {i : Fin l2.length}
    (h : (l ++ l2).HasDualInSelf (appendEquiv (Sum.inr i))) (hi : l2.HasDualInOther l i) :
    h.getFirst = appendEquiv (Sum.inl hi.getFirst) := by
  have h1 : Fin.find ((l ++ l2).AreDualInSelf (appendEquiv (Sum.inr i))) =
      some (appendEquiv (Sum.inl hi.getFirst)) := by
    rw [Fin.find_eq_some_iff]
    simp
    apply And.intro hi.areDualInOther_getFirst
    intro j hj
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp [appendEquiv]
      rw [Fin.le_def]
      simp
      have h2 := hi.some_getFirst_eq_find
      rw [Fin.find_eq_some_iff] at h2
      simp only [AreDualInSelf.append_inr_inl] at hj
      exact h2.2 k hj
    | Sum.inr k =>
      simp [appendEquiv]
      rw [Fin.le_def]
      simp
      omega
  rw [h.some_getFirst_eq_find] at h1
  simpa only [Option.some.injEq] using h1

@[simp]
lemma getFirst_append_inr_of_not_hasDualInOther {i : Fin l2.length}
    (h : (l ++ l2).HasDualInSelf (appendEquiv (Sum.inr i))) (hi : ¬ l2.HasDualInOther l i)
    (hn : l2.HasDualInSelf i) : h.getFirst = appendEquiv (Sum.inr hn.getFirst) := by
  have h1 : Fin.find ((l ++ l2).AreDualInSelf (appendEquiv (Sum.inr i))) =
      some (appendEquiv (Sum.inr hn.getFirst)) := by
    rw [Fin.find_eq_some_iff]
    simp
    apply And.intro hn.areDualInSelf_getFirst
    intro j hj
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp at hj
      exact False.elim (hi ⟨k, hj⟩)
    | Sum.inr k =>
      simp [appendEquiv]
      rw [Fin.le_def]
      simp
      have h2 := hn.some_getFirst_eq_find
      rw [Fin.find_eq_some_iff] at h2
      simp only [AreDualInSelf.append_inr_inr] at hj
      exact h2.2 k hj
  rw [h.some_getFirst_eq_find] at h1
  simpa only [Option.some.injEq] using h1

end HasDualInSelf
/-!

## Has single dual

-/

def HasSingDualInSelf (i : Fin l.length) : Prop :=
  l.HasDualInSelf i ∧ ∀ (h : l.HasDualInSelf i) j, l.AreDualInSelf i j → j = h.getFirst

instance (i : Fin l.length) : Decidable (l.HasSingDualInSelf i) := instDecidableAnd

def HasSingDualInOther (l l2 : IndexList X) (i : Fin l.length) : Prop :=
  l.HasDualInOther l2 i ∧ ∀ (h : l.HasDualInOther l2 i) j, l.AreDualInOther i j → j = h.getFirst

instance (i : Fin l.length) : Decidable (l.HasSingDualInOther l2 i) := instDecidableAnd

namespace HasSingDualInSelf

variable {l l2 : IndexList X} {i : Fin l.length}

def toHasDualInSelf (h : l.HasSingDualInSelf i) : l.HasDualInSelf i := h.1

def get (h : l.HasSingDualInSelf i) : Fin l.length := h.1.getFirst

lemma eq_get_iff (h : l.HasSingDualInSelf i) (j : Fin l.length) :
    j = h.get ↔ l.AreDualInSelf i j := by
  apply Iff.intro
  · intro h1
    subst h1
    exact h.1.areDualInSelf_getFirst
  · intro h1
    exact h.2 h.1 j h1

@[simp]
lemma get_id (h : l.HasSingDualInSelf i) : l.idMap h.get = l.idMap i := h.1.getFirst_id

lemma get_hasSingDualInSelf (h : l.HasSingDualInSelf i) : l.HasSingDualInSelf h.get := by
  refine And.intro h.1.getFirst_hasDualInSelf (fun hj j hji => ?_)
  have h1 : i = j := by
    by_contra hn
    have h' : l.AreDualInSelf i j := by
      simp [AreDualInSelf, hn]
      simp_all [AreDualInSelf, get]
    rw [← h.eq_get_iff] at h'
    subst h'
    simp at hji
  subst h1
  have h2 : i = hj.getFirst := by
    by_contra hn
    have h' : l.AreDualInSelf i hj.getFirst := by
        simp [AreDualInSelf, hn]
    rw [← h.eq_get_iff] at h'
    have hx := hj.areDualInSelf_getFirst
    simp [AreDualInSelf, h'] at hx
  rw [← h2]

@[simp]
lemma get_get (h : l.HasSingDualInSelf i) : h.get_hasSingDualInSelf.get = i := by
  symm
  rw [h.get_hasSingDualInSelf.eq_get_iff]
  exact  h.1.areDualInSelf_getFirst.symm

/-!

### Relations regarding append for HasSingDualInSelf

-/

lemma get_append_inl (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i)))
    (hi : l.HasDualInSelf i) : h.get = appendEquiv (Sum.inl hi.getFirst)  := by
  symm
  rw [h.eq_get_iff]
  simp only [AreDualInSelf.append_inl_inl]
  exact HasDualInSelf.areDualInSelf_getFirst hi

lemma get_append_inl_other (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i)))
    (hi : l.HasDualInOther l2 i) : h.get = appendEquiv (Sum.inr hi.getFirst) := by
  symm
  rw [h.eq_get_iff]
  simp only [AreDualInSelf.append_inl_inr]
  exact HasDualInOther.areDualInOther_getFirst hi

lemma get_append_inr {i : Fin l2.length}
    (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inr i))) (hi : l2.HasDualInSelf i) :
    h.get = appendEquiv (Sum.inr hi.getFirst) := by
  symm
  rw [h.eq_get_iff]
  simp only [AreDualInSelf.append_inr_inr]
  exact HasDualInSelf.areDualInSelf_getFirst hi

lemma get_append_inr_other {i : Fin l2.length}
    (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inr i))) (hi : l2.HasDualInOther l i) :
    h.get = appendEquiv (Sum.inl hi.getFirst) := by
  symm
  rw [h.eq_get_iff]
  simp only [AreDualInSelf.append_inr_inl]
  exact HasDualInOther.areDualInOther_getFirst hi

lemma hasDualInSelf_iff_of_append_inl (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i))) :
    l.HasDualInSelf i ↔ l.HasSingDualInSelf i := by
  refine Iff.intro (fun hi => ?_) (fun hi => hi.1)
  apply And.intro hi
  intro _ j hji
  simpa [get_append_inl h hi] using
    (h.eq_get_iff (appendEquiv (Sum.inl j))).mpr (by simpa using hji)

lemma hasDualInSelf_iff_of_append_inr {i : Fin l2.length}
    (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inr i))) :
    l2.HasDualInSelf i ↔ l2.HasSingDualInSelf i := by
  refine Iff.intro (fun hi => ?_) (fun hi => hi.1)
  apply And.intro hi
  intro _ j hji
  simpa [get_append_inr h hi] using
    (h.eq_get_iff (appendEquiv (Sum.inr j))).mpr (by simpa using hji)

lemma hasDualInOther_iff_of_append_inl
    (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i))) :
    l.HasDualInOther l2 i ↔ l.HasSingDualInOther l2 i := by
  refine Iff.intro (fun hi => ?_) (fun hi => hi.1)
  apply And.intro hi
  intro _ j hji
  simpa [get_append_inl_other h hi] using
    (h.eq_get_iff (appendEquiv (Sum.inr j))).mpr (by simpa using hji)

lemma hasDualInOther_iff_of_append_inr {i : Fin l2.length}
    (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inr i))) :
    l2.HasDualInOther l i ↔ l2.HasSingDualInOther l i := by
  refine Iff.intro (fun hi => ?_) (fun hi => hi.1)
  apply And.intro hi
  intro _ j hji
  simpa [get_append_inr_other h hi] using
    (h.eq_get_iff (appendEquiv (Sum.inl j))).mpr (by simpa using hji)

lemma hasSingInSelf_iff_not_hasSingDualInOther_of_append_inl
    (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i))) :
    l.HasSingDualInSelf i ↔ ¬ l.HasSingDualInOther l2 i := by
  rw [← hasDualInOther_iff_of_append_inl h, ← hasDualInSelf_iff_of_append_inl h]
  refine Iff.intro (fun hi => ?_) (fun hi => ?_)
  · simp only [HasDualInOther, not_exists]
    intro j
    by_contra hn
    have h' := h.eq_get_iff (appendEquiv (Sum.inr j))
    rw [AreDualInSelf.append_inl_inr] at h'
    simpa [get_append_inl h hi] using h'.mpr hn
  · obtain ⟨j, hj⟩ := h.1
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp only [AreDualInSelf.append_inl_inl] at hj
      exact ⟨k, hj⟩
    | Sum.inr k =>
      simp only [AreDualInSelf.append_inl_inr] at hj
      simp only [HasDualInOther, not_exists] at hi
      exact False.elim (hi k hj)

lemma hasSingInSelf_iff_not_hasSingDualInOther_of_append_inr {i : Fin l2.length}
    (h : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inr i))) :
    l2.HasSingDualInSelf i ↔ ¬ l2.HasSingDualInOther l i := by
  rw [← hasDualInOther_iff_of_append_inr h, ← hasDualInSelf_iff_of_append_inr h]
  refine Iff.intro (fun hi => ?_) (fun hi => ?_)
  · simp only [HasDualInOther, not_exists]
    intro j
    by_contra hn
    have h' := h.eq_get_iff (appendEquiv (Sum.inl j))
    rw [AreDualInSelf.append_inr_inl] at h'
    simpa [get_append_inr h hi] using h'.mpr hn
  · obtain ⟨j, hj⟩ := h.1
    obtain ⟨k, hk⟩ := appendEquiv.surjective j
    subst hk
    match k with
    | Sum.inl k =>
      simp only [AreDualInSelf.append_inr_inl] at hj
      simp only [HasDualInOther, not_exists] at hi
      exact False.elim (hi k hj)
    | Sum.inr k =>
      simp only [AreDualInSelf.append_inr_inr] at hj
      exact ⟨k, hj⟩

lemma append_inl_of_hasSingDualInSelf (h1 : l.HasSingDualInSelf i) (h2 : ¬ l.HasDualInOther l2 i) :
    (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i)) := by
  simp only [HasSingDualInSelf, HasDualInSelf.append_inl]
  apply And.intro (Or.inl h1.toHasDualInSelf)
  intro h j hji
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  rw [HasDualInSelf.getFirst_append_inl_of_hasDualInSelf l l2 (HasDualInSelf.append_inl.mpr h)
      h1.toHasDualInSelf]
  match k with
  | Sum.inl k =>
    simp only [AreDualInSelf.append_inl_inl] at hji
    simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq]
    exact h1.2 h1.1 k hji
  | Sum.inr k =>
    simp only [AreDualInSelf.append_inl_inr] at hji
    exact False.elim (h2 ⟨k, hji⟩)

lemma append_inr_of_hasSingDualInSelf {i : Fin l2.length} (h1 : l2.HasSingDualInSelf i)
    (h2 : ¬ l2.HasDualInOther l i) : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inr i)) := by
  simp only [HasSingDualInSelf, HasDualInSelf.append_inr]
  refine And.intro (Or.inl h1.toHasDualInSelf) ?_
  intro h j hji
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  rw [HasDualInSelf.getFirst_append_inr_of_not_hasDualInOther l l2
      (HasDualInSelf.append_inr.mpr h) h2 h1.1]
  match k with
  | Sum.inl k =>
    simp only [AreDualInSelf.append_inr_inl] at hji
    exact False.elim (h2 ⟨k, hji⟩)
  | Sum.inr k =>
    simp only [EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq]
    simp only [AreDualInSelf.append_inr_inr] at hji
    exact h1.2 h1.1 k hji

lemma append_inl_of_not_hasSingDualInSelf (h1 : ¬ l.HasDualInSelf i) (h2 : l.HasSingDualInOther l2 i) :
    (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i)) := by
  simp only [HasSingDualInSelf, HasDualInSelf.append_inl]
  apply And.intro (Or.inr h2.1)
  intro h j hji
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  rw [HasDualInSelf.getFirst_append_inl_of_not_hasDualInSelf l l2
      (HasDualInSelf.append_inl.mpr h) h1 h2.1]
  match k with
  | Sum.inl k =>
    simp at hji
    exact False.elim (h1 ⟨k, hji⟩)
  | Sum.inr k =>
    simp
    simp at hji
    exact h2.2 h2.1 k hji

lemma append_inr_of_not_hasSingDualInSelf {i : Fin l2.length} (h1 : ¬ l2.HasDualInSelf i)
    (h2 : l2.HasSingDualInOther l i) : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inr i)) := by
  simp only [HasSingDualInSelf, HasDualInSelf.append_inr]
  refine And.intro (Or.inr h2.1) ?_
  intro h j hji
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  rw [HasDualInSelf.getFirst_append_inr_of_hasDualInOther l l2
      (HasDualInSelf.append_inr.mpr h) h2.1]
  match k with
  | Sum.inl k =>
    simp
    simp at hji
    exact h2.2 h2.1 k hji
  | Sum.inr k =>
    simp only [AreDualInSelf.append_inr_inr] at hji
    exact False.elim (h1 ⟨k, hji⟩)

@[simp]
lemma append_inl : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i)) ↔
    (l.HasSingDualInSelf i ∧ ¬ l.HasDualInOther l2 i) ∨
    (¬ l.HasDualInSelf i ∧ l.HasSingDualInOther l2 i) := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · by_cases hl : l.HasDualInSelf i
    · have hl2 := (hasDualInSelf_iff_of_append_inl h).mp hl
      simp_all
      exact (hasDualInOther_iff_of_append_inl h).mp.mt
        ((hasSingInSelf_iff_not_hasSingDualInOther_of_append_inl h).mp hl2)
    · have hl2 := (hasDualInSelf_iff_of_append_inl h).mpr.mt hl
      simp_all
      have h' := (hasSingInSelf_iff_not_hasSingDualInOther_of_append_inl h).mpr.mt
      simp at h'
      exact h' hl2
  · cases h <;> rename_i h
    · exact append_inl_of_hasSingDualInSelf h.1 h.2
    · exact append_inl_of_not_hasSingDualInSelf h.1 h.2

@[simp]
lemma append_inr {i : Fin l2.length} : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inr i)) ↔
    (l2.HasSingDualInSelf i ∧ ¬ l2.HasDualInOther l i) ∨
    (¬ l2.HasDualInSelf i ∧ l2.HasSingDualInOther l i) := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · by_cases hl : l2.HasDualInSelf i
    · have hl2 := (hasDualInSelf_iff_of_append_inr h).mp hl
      simp_all
      exact (hasDualInOther_iff_of_append_inr h).mp.mt
        ((hasSingInSelf_iff_not_hasSingDualInOther_of_append_inr h).mp hl2)
    · have hl2 := (hasDualInSelf_iff_of_append_inr h).mpr.mt hl
      simp_all
      have h' := (hasSingInSelf_iff_not_hasSingDualInOther_of_append_inr h).mpr.mt
      simp at h'
      exact h' hl2
  · cases h <;> rename_i h
    · exact append_inr_of_hasSingDualInSelf h.1 h.2
    · exact append_inr_of_not_hasSingDualInSelf h.1 h.2

lemma append_symm : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i)) ↔
    (l2 ++ l).HasSingDualInSelf (appendEquiv (Sum.inr i)) := by
  simp

end HasSingDualInSelf

namespace HasSingDualInOther

variable {l l2 : IndexList X} {i : Fin l.length}

def toHasDualInOther (h : l.HasSingDualInOther l2 i) : l.HasDualInOther l2 i := h.1

def get (h : l.HasSingDualInOther l2 i) : Fin l2.length := h.1.getFirst

lemma eq_get_iff (h : l.HasSingDualInOther l2 i) (j : Fin l2.length) :
    j = h.get ↔ AreDualInOther i j := by
  apply Iff.intro
  · intro h1
    subst h1
    exact h.1.areDualInOther_getFirst
  · intro h1
    exact h.2 h.1 j h1

end HasSingDualInOther


/-!

## Lists with no duals

-/

def HasNoDualsSelf : Prop := ∀ i, ¬ l.HasDualInSelf i

instance : Decidable (HasNoDualsSelf l) := Nat.decidableForallFin fun i => ¬l.HasDualInSelf i

namespace HasNoDualsSelf

variable {l : IndexList X}

lemma idMap_inje (h : l.HasNoDualsSelf) : Function.Injective l.idMap := by
  intro i j
  have h1 := h i
  simp only [HasDualInSelf, AreDualInSelf, ne_eq, not_exists, not_and] at h1
  simpa using (h1 j).mt

lemma eq_of_id_eq (h : l.HasNoDualsSelf) {i j : Fin l.length} (h' : l.idMap i = l.idMap j) :
    i = j := h.idMap_inje h'

lemma color_eq_of_id_eq (h : l.HasNoDualsSelf) (i j : Fin l.length) :
    l.idMap i = l.idMap j → l.colorMap i = l.colorMap j := by
  intro h'
  rw [h.eq_of_id_eq h']

end HasNoDualsSelf

section Color

variable {𝓒 : TensorColor}
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
variable (l l2 : IndexList 𝓒.Color)
/-!

## Has single dual of correct color

-/


def HasSingColorDualInSelf (i : Fin l.length) : Prop :=
  l.HasSingDualInSelf i ∧ ∀ (h : l.HasSingDualInSelf i), l.colorMap i = 𝓒.τ (l.colorMap h.get)

instance (i : Fin l.length) : Decidable (l.HasSingColorDualInSelf i) := instDecidableAnd

def HasSingColorDualInOther (i : Fin l.length) : Prop :=
  l.HasSingDualInOther l2 i ∧ ∀ (h : l.HasSingDualInOther l2 i), l.colorMap i =
    𝓒.τ (l2.colorMap h.get)

instance (i : Fin l.length) : Decidable (l.HasSingColorDualInOther l2 i) := instDecidableAnd

namespace HasSingColorDualInSelf

variable {l l2 : IndexList 𝓒.Color} {i : Fin l.length}

def get (h : l.HasSingColorDualInSelf i) : Fin l.length := h.1.get

@[simp]
lemma get_color (h : l.HasSingColorDualInSelf i) : l.colorMap h.get = 𝓒.τ (l.colorMap i) := by
  rw [h.2 h.1]
  exact (𝓒.τ_involutive (l.colorMap h.get)).symm

@[simp]
lemma get_id (h : l.HasSingColorDualInSelf i) : l.idMap h.get = l.idMap i := h.1.get_id

lemma get_hasSingColorDualInSelf (h : l.HasSingColorDualInSelf i) :
    l.HasSingColorDualInSelf h.get := by
  refine And.intro h.1.get_hasSingDualInSelf ?_
  intro _
  simp only [get_color, HasSingDualInSelf.get_get]

@[simp]
lemma get_get (h : l.HasSingColorDualInSelf i) : h.get_hasSingColorDualInSelf.get = i := by
  simp [get]

lemma areDualInSelf_get (h : l.HasSingColorDualInSelf i) : l.AreDualInSelf i h.get := by
  exact h.1.1.areDualInSelf_getFirst

/-!

### Append lemmas regarding HasSingColorDualInSelf

-/

@[simp]
lemma append_inl : (l ++ l2).HasSingColorDualInSelf (appendEquiv (Sum.inl i)) ↔
    (l.HasSingColorDualInSelf i ∧ ¬ l.HasDualInOther l2 i) ∨
    (¬ l.HasDualInSelf i ∧ l.HasSingColorDualInOther l2 i) := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · have h1 := h.1
    have h2 := h.2 h.1
    simp [HasSingColorDualInSelf] at h1
    simp at h2
    cases h1 <;> rename_i h1
    · refine Or.inl (And.intro ⟨h1.1, fun h' => ?_⟩ h1.2)
      rw [HasSingDualInSelf.get_append_inl h.1 h1.1.1] at h2
      simpa using h2
    · refine Or.inr (And.intro h1.1 ⟨h1.2, fun h' => ?_⟩)
      rw [HasSingDualInSelf.get_append_inl_other h.1 h1.2.1] at h2
      simpa using h2
  · have h1 : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inl i)) := by
      simp [HasSingColorDualInSelf]
      cases h <;> rename_i h
      · exact Or.inl ⟨h.1.1, h.2⟩
      · exact Or.inr ⟨h.1, h.2.1⟩
    apply And.intro h1
    intro h'
    simp
    cases h <;> rename_i h
    · simpa [HasSingDualInSelf.get_append_inl h1 h.1.1.1] using h.1.2 h.1.1
    · simpa [HasSingDualInSelf.get_append_inl_other h1 h.2.1.1] using h.2.2 h.2.1

@[simp]
lemma append_inr {i : Fin l2.length} : (l ++ l2).HasSingColorDualInSelf (appendEquiv (Sum.inr i)) ↔
    (l2.HasSingColorDualInSelf i ∧ ¬ l2.HasDualInOther l i) ∨
    (¬ l2.HasDualInSelf i ∧ l2.HasSingColorDualInOther l i) := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · have h1 := h.1
    have h2 := h.2 h.1
    simp [HasSingColorDualInSelf] at h1
    simp at h2
    cases h1 <;> rename_i h1
    · refine Or.inl (And.intro ⟨h1.1, fun h' => ?_⟩ h1.2)
      rw [HasSingDualInSelf.get_append_inr h.1 h1.1.1] at h2
      simpa using h2
    · refine Or.inr (And.intro h1.1 ⟨h1.2, fun h' => ?_⟩)
      rw [HasSingDualInSelf.get_append_inr_other h.1 h1.2.1] at h2
      simpa using h2
  · have h1 : (l ++ l2).HasSingDualInSelf (appendEquiv (Sum.inr i)) := by
      simp [HasSingColorDualInSelf]
      cases h <;> rename_i h
      · exact Or.inl ⟨h.1.1, h.2⟩
      · exact Or.inr ⟨h.1, h.2.1⟩
    apply And.intro h1
    intro h'
    simp
    cases h <;> rename_i h
    · simpa [HasSingDualInSelf.get_append_inr h1 h.1.1.1] using h.1.2 h.1.1
    · simpa [HasSingDualInSelf.get_append_inr_other h1 h.2.1.1] using h.2.2 h.2.1

lemma append_symm : (l ++ l2).HasSingColorDualInSelf (appendEquiv (Sum.inl i)) ↔
    (l2 ++ l).HasSingColorDualInSelf (appendEquiv (Sum.inr i)) := by
  simp

end HasSingColorDualInSelf

def HasSingColorDualsInSelf : Prop := ∀ i, l.HasSingColorDualInSelf i ∨ ¬ l.HasDualInSelf i

namespace HasSingColorDualsInSelf

variable {l : IndexList 𝓒.Color}

lemma not_hasDualInSelf_iff_not_hasSingColorDualInSelf (h : l.HasSingColorDualsInSelf)
    (i : Fin l.length) : ¬ l.HasDualInSelf i ↔ ¬ l.HasSingColorDualInSelf i := by
  apply Iff.intro
  · intro h'
    by_contra hn
    exact h' hn.1.1
  · intro h'
    have h1 := h i
    simp_all

lemma _root_.IndexNotation.IndexList.HasNoDualsSelf.toHasSingColorDualsInSelf
    (h : l.HasNoDualsSelf) : l.HasSingColorDualsInSelf :=
  fun i => Or.inr (h i)

end HasSingColorDualsInSelf
def HasSingColorDualsInOther : Prop := ∀ i, l.HasSingColorDualInOther l2 i ∨ ¬ l.HasDualInOther l2 i


end Color


end IndexList

end IndexNotation
