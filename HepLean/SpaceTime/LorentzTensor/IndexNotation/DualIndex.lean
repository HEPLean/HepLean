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

def AreDualInOther  (i : Fin l.length) (j : Fin l2.length) :
    Prop := l.idMap i = l2.idMap j

instance {l : IndexList X} {l2 : IndexList X}  (i : Fin l.length) (j : Fin l2.length) :
    Decidable (l.AreDualInOther l2 i j) := (l.idMap i).decEq (l2.idMap j)


namespace AreDualInSelf

variable {l l2 : IndexList X} {i j : Fin l.length}

@[symm]
lemma symm (h : l.AreDualInSelf i j) : l.AreDualInSelf j i := by
  simp only [AreDualInSelf] at h ⊢
  exact ⟨h.1.symm, h.2.symm⟩

@[simp]
lemma self_false (i : Fin l.length) : ¬ l.AreDualInSelf i i := by
  simp [AreDualInSelf]

end AreDualInSelf

namespace AreDualInOther

variable {l l2 : IndexList X} {i : Fin l.length} {j : Fin l2.length}

@[symm]
lemma symm  (h : l.AreDualInOther l2 i j) : l2.AreDualInOther l j i := by
  rw [AreDualInOther] at h ⊢
  exact h.symm

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

## With dual self.

-/

def withDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isSome) Finset.univ

lemma mem_withDual_iff_exists : i ∈ l.withDual ↔ ∃ j, l.AreDualInSelf i j := by
  simp [withDual, Finset.mem_filter, Finset.mem_univ, getDual?]
  rw [Fin.isSome_find_iff]

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


def getDual! (i : l.withDual) : Fin l.length :=
  (l.getDual? i).get (by simpa [withDual] using i.2)

lemma getDual?_eq_some_getDual! (i : l.withDual) : l.getDual? i = some (l.getDual! i) := by
  simp [getDual!]

lemma getDual?_eq_none_on_not_mem (i : Fin l.length) (h : i ∉ l.withDual) :
    l.getDual? i = none := by
  simpa [withDual, getDual?, Fin.find_eq_none_iff]  using h

lemma some_dual!_eq_gual? (i : l.withDual) : some (l.getDual! i) = l.getDual? i := by
  rw [getDual?_eq_some_getDual!]

lemma areDualInSelf_getDual! (i : l.withDual) : l.AreDualInSelf i (l.getDual! i) := by
  have h := l.getDual?_eq_some_getDual! i
  rw [getDual?, Fin.find_eq_some_iff] at h
  exact h.1

@[simp]
lemma getDual!_id (i : l.withDual) : l.idMap (l.getDual! i) = l.idMap i := by
  simpa using (l.areDualInSelf_getDual! i).2.symm

lemma getDual_mem_withDual (i : l.withDual) : l.getDual! i ∈ l.withDual := by
  simp only [withDual, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [getDual?, Fin.isSome_find_iff]
  exact ⟨i, (l.areDualInSelf_getDual! i).symm⟩

def getDual (i : l.withDual) : l.withDual := ⟨l.getDual! i, l.getDual_mem_withDual i⟩

@[simp]
lemma getDual_id (i : l.withDual) :
    l.idMap (l.getDual i) = l.idMap i := by
  simp [getDual]

/-!

## With dual other.

-/

def withDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDualInOther? l2 i).isSome) Finset.univ

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


/-!

## Has single dual in self.

-/


def withUniqueDual : Finset (Fin l.length) :=
  Finset.filter (fun i => i ∈ l.withDual ∧
    ∀ j, l.AreDualInSelf i j → j = l.getDual? i) Finset.univ

lemma mem_withDual_of_withUniqueDual (i : l.withUniqueDual) :
    i.1 ∈ l.withDual := by
  have hi := i.2
  simp [withUniqueDual, Finset.mem_filter, Finset.mem_univ] at hi
  exact hi.1

def fromWithUnique (i : l.withUniqueDual) : l.withDual :=
  ⟨i.1, l.mem_withDual_of_withUniqueDual i⟩

instance : Coe l.withUniqueDual l.withDual where
  coe i := ⟨i.1, l.mem_withDual_of_withUniqueDual i⟩

@[simp]
lemma fromWithUnique_coe (i : l.withUniqueDual) : (l.fromWithUnique i).1 = i.1 := by
  rfl

lemma all_dual_eq_getDual_of_withUniqueDual (i : l.withUniqueDual) :
    ∀ j, l.AreDualInSelf i j → j = l.getDual! i := by
  have hi := i.2
  simp [withUniqueDual] at hi
  intro j hj
  simpa [getDual!, fromWithUnique] using (Option.get_of_mem _ (hi.2 j hj ).symm).symm

lemma eq_of_areDualInSelf_withUniqueDual {j k : Fin l.length} (i : l.withUniqueDual)
    (hj : l.AreDualInSelf i j) (hk : l.AreDualInSelf i k) :
    j = k := by
  have hj' := all_dual_eq_getDual_of_withUniqueDual l i j hj
  have hk' := all_dual_eq_getDual_of_withUniqueDual l i k hk
  rw [hj', hk']

lemma eq_getDual_of_withUniqueDual_iff (i : l.withUniqueDual) (j : Fin l.length) :
    l.AreDualInSelf i j ↔ j = l.getDual! i := by
  apply Iff.intro
  intro h
  exact (l.all_dual_eq_getDual_of_withUniqueDual i) j h
  intro h
  subst h
  exact areDualInSelf_getDual! l i

@[simp]
lemma getDual!_getDual_of_withUniqueDual (i : l.withUniqueDual) :
    l.getDual! (l.getDual i) = i := by
  by_contra hn
  have h' : l.AreDualInSelf i (l.getDual! (l.getDual i)) := by
    simp [AreDualInSelf, hn]
    simp_all [AreDualInSelf, getDual, fromWithUnique]
    exact fun a => hn (id (Eq.symm a))
  rw [eq_getDual_of_withUniqueDual_iff] at h'
  have hx := l.areDualInSelf_getDual! (l.getDual i)
  simp_all [getDual]

@[simp]
lemma getDual_getDual_of_withUniqueDual (i : l.withUniqueDual) :
    l.getDual (l.getDual i) = l.fromWithUnique i :=
  SetCoe.ext (getDual!_getDual_of_withUniqueDual l i)

@[simp]
lemma getDual?_getDual!_of_withUniqueDual (i : l.withUniqueDual) :
    l.getDual? (l.getDual! i) = some i := by
  change l.getDual? (l.getDual i) = some i
  rw [getDual?_eq_some_getDual!]
  simp

@[simp]
lemma getDual?_getDual?_of_withUniqueDualInOther (i : l.withUniqueDual) :
    (l.getDual? i).bind l.getDual? = some i := by
  rw [getDual?_eq_some_getDual! l i]
  simp


lemma getDual_of_withUniqueDual_mem (i : l.withUniqueDual) :
    l.getDual! i ∈ l.withUniqueDual := by
  simp [withUniqueDual]
  apply And.intro (getDual_mem_withDual l ⟨↑i, mem_withDual_of_withUniqueDual l i⟩)
  intro j hj
  have h1 : i = j := by
    by_contra hn
    have h' : l.AreDualInSelf i j := by
      simp [AreDualInSelf, hn]
      simp_all [AreDualInSelf, getDual, fromWithUnique]
    rw [eq_getDual_of_withUniqueDual_iff] at h'
    subst h'
    simp_all [getDual]
  subst h1
  rfl

def getDualEquiv : l.withUniqueDual ≃ l.withUniqueDual where
  toFun x := ⟨l.getDual x, l.getDual_of_withUniqueDual_mem x⟩
  invFun x := ⟨l.getDual x, l.getDual_of_withUniqueDual_mem x⟩
  left_inv x := SetCoe.ext (by
    simp only [Subtype.coe_eta, getDual_getDual_of_withUniqueDual]
    rfl)
  right_inv x := SetCoe.ext (by
    simp only [Subtype.coe_eta, getDual_getDual_of_withUniqueDual]
    rfl)

@[simp]
lemma getDualEquiv_involutive : Function.Involutive l.getDualEquiv := by
  intro x
  simp [getDualEquiv, fromWithUnique]


/-!

## Has single in other.

-/

def withUniqueDualInOther : Finset (Fin l.length) :=
  Finset.filter (fun i => i ∉ l.withDual ∧ i ∈ l.withDualInOther l2
     ∧ (∀ j, l.AreDualInOther l2 i j → j = l.getDualInOther? l2 i)) Finset.univ

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

def fromWithUniqueDualInOther (i : l.withUniqueDualInOther l2) : l.withDualInOther l2 :=
  ⟨i.1, l.mem_withDualInOther_of_withUniqueDualInOther l2 i⟩

instance : Coe (l.withUniqueDualInOther l2) (l.withDualInOther l2) where
  coe i := ⟨i.1, l.mem_withDualInOther_of_withUniqueDualInOther l2 i⟩

lemma all_dual_eq_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    ∀ j, l.AreDualInOther l2 i j → j = l.getDualInOther! l2 i := by
  have hi := i.2
  simp only [withUniqueDualInOther, Finset.univ_eq_attach, Finset.mem_filter, Finset.mem_attach,
    true_and] at hi
  intro j hj
  refine (Option.get_of_mem _ (hi.2.2.2 j hj).symm).symm

lemma eq_getDualInOther_of_withUniqueDual_iff (i : l.withUniqueDualInOther l2) (j : Fin l2.length) :
    l.AreDualInOther l2 i j ↔ j = l.getDualInOther! l2 i := by
  apply Iff.intro
  intro h
  exact l.all_dual_eq_of_withUniqueDualInOther l2 i j h
  intro h
  subst h
  exact areDualInOther_getDualInOther! l l2 i

@[simp]
lemma getDualInOther!_getDualInOther_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    l2.getDualInOther! l (l.getDualInOther l2 i) = i := by
  by_contra hn
  refine (l.not_mem_withDual_of_withUniqueDualInOther l2 i)
    (l.mem_withDual_iff_exists.mpr ⟨(l2.getDualInOther! l (l.getDualInOther l2 i)), ?_⟩ )
  simp [AreDualInSelf, hn]
  exact (fun a => hn (id (Eq.symm a)))

@[simp]
lemma getDualInOther_getDualInOther_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    l2.getDualInOther l (l.getDualInOther l2 i) = i :=
  SetCoe.ext (getDualInOther!_getDualInOther_of_withUniqueDualInOther l l2 i)

@[simp]
lemma getDualInOther?_getDualInOther!_of_withUniqueDualInOther (i : l.withUniqueDualInOther l2) :
    l2.getDualInOther? l (l.getDualInOther! l2 i) = some i := by
  change l2.getDualInOther? l (l.getDualInOther l2 i) = some i
  rw [getDualInOther?_eq_some_getDualInOther!]
  simp

lemma getDualInOther_of_withUniqueDualInOther_not_mem_of_withDual (i : l.withUniqueDualInOther l2) :
    (l.getDualInOther l2 i).1 ∉ l2.withDual  := by
  rw [mem_withDual_iff_exists]
  simp
  intro j
  simp [AreDualInSelf]
  intro hj
  by_contra hn
  have hn' : l.AreDualInOther l2 i j  := by
    simp [AreDualInOther, hn, hj]
  rw [eq_getDualInOther_of_withUniqueDual_iff] at hn'
  simp_all
  simp only [getDualInOther_coe, not_true_eq_false] at hj

lemma getDualInOther_of_withUniqueDualInOther_mem (i : l.withUniqueDualInOther l2) :
    (l.getDualInOther l2 i).1 ∈ l2.withUniqueDualInOther l := by
  simp only [withUniqueDualInOther, Finset.mem_filter, Finset.mem_univ, true_and]
  apply And.intro (l.getDualInOther_of_withUniqueDualInOther_not_mem_of_withDual l2 i)
  apply And.intro
  exact Finset.coe_mem
    (l.getDualInOther l2 ⟨↑i, mem_withDualInOther_of_withUniqueDualInOther l l2 i⟩)
  intro j hj
  by_contra hn
  have h' : l.AreDualInSelf i j := by
    simp [AreDualInSelf, hn]
    simp_all [AreDualInOther, getDual]
    simp [getDualInOther_coe] at hn
    exact fun a => hn (id (Eq.symm a))
  have hi := l.not_mem_withDual_of_withUniqueDualInOther l2 i
  rw [mem_withDual_iff_exists] at hi
  simp_all

def getDualInOtherEquiv : l.withUniqueDualInOther l2 ≃ l2.withUniqueDualInOther l where
  toFun x := ⟨l.getDualInOther l2 x, l.getDualInOther_of_withUniqueDualInOther_mem l2 x⟩
  invFun x := ⟨l2.getDualInOther l x, l2.getDualInOther_of_withUniqueDualInOther_mem l x⟩
  left_inv x := SetCoe.ext (by simp)
  right_inv x := SetCoe.ext (by simp)

/-!

## Equality of withUnqiueDual and withDual

-/

lemma withUnqiueDual_eq_withDual_iff_unique_forall :
    l.withUniqueDual = l.withDual ↔
    ∀ (i : l.withDual) j, l.AreDualInSelf i j → j = l.getDual? i := by
  apply Iff.intro
  · intro h i j hj
    rw [@Finset.ext_iff] at h
    simp [withUniqueDual] at h
    exact h i i.2 j hj
  · intro h
    apply Finset.ext
    intro i
    apply Iff.intro
    · intro hi
      simp [withUniqueDual] at hi
      exact hi.1
    · intro hi
      simp [withUniqueDual]
      apply And.intro hi
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
      rw [getDual?_getDual?_of_withUniqueDualInOther l ⟨i, hii⟩]
      simp
      symm
      rw [Option.guard_eq_some]
      exact ⟨rfl, hi⟩
    · rw [getDual?_eq_none_on_not_mem l i hi]
      simp
      symm
      simpa only [Option.guard, ite_eq_right_iff, imp_false] using hi
  · intro h
    rw [withUnqiueDual_eq_withDual_iff_unique_forall]
    intro i j hj
    rcases l.getDual?_of_areDualInSelf hj with hi | hi | hi
    · have hj' := h j
      rw [hi] at hj'
      simp at hj'
      rw [hj']
      symm
      rw [Option.guard_eq_some]
      exact ⟨rfl, l.mem_withDual_iff_exists.mpr ⟨i, hj.symm⟩⟩
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



/-

def withoutDual : Finset (Fin l.length) :=
  Finset.filter (fun i => (l.getDual? i).isNone) Finset.univ


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

## Has a dual

-/

def HasDualInSelf (i : Fin l.length) : Prop := (l.getDual? i).isSome

instance (i : Fin l.length) : Decidable (l.HasDualInSelf i) := (l.getDual? i).isSome.decEq true

def HasDualInOther (i : Fin l.length) : Prop :=
  ∃ (j : Fin l2.length), AreDualInOther i j

instance (i : Fin l.length) : Decidable (l.HasDualInOther l2 i) := Fintype.decidableExistsFintype

namespace HasDualInSelf

variable {l l2 : IndexList X} {i : Fin l.length}

lemma iff_exists : l.HasDualInSelf i ↔ ∃ j, l.AreDualInSelf i j :=
  Fin.isSome_find_iff

lemma iff_mem : l.HasDualInSelf i ↔ i ∈ l.withDual := by
  simp [withDual, Finset.mem_filter, Finset.mem_univ, HasDualInSelf]

@[simp]
lemma append_inl : (l ++ l2).HasDualInSelf (appendEquiv (Sum.inl i)) ↔
    (l.HasDualInSelf i ∨ l.HasDualInOther l2 i) := by
  rw [iff_exists, iff_exists]
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
  rw [iff_exists, iff_exists]
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

### Bool condition

-/

def bool (l : IndexList X) (i : Fin l.length) : Bool :=
  if h : l.HasDualInSelf i then
    let l' := (Fin.list l.length).filterMap fun j => if l.AreDualInSelf j i ∧ j ≠ h.getFirst
      then some j else none
    List.isEmpty l'
  else false

lemma of_bool_true (h : bool l i) : l.HasSingDualInSelf i := by
  simp [bool] at h
  split at h <;> rename_i h1
  · rw [List.isEmpty_iff_eq_nil] at h
    rw [List.filterMap_eq_nil] at h
    simp at h
    apply And.intro h1
    intro h' j
    have h1 {n : ℕ} (m : Fin n) : m ∈ Fin.list n := by
      have h1' : (Fin.list n)[m] = m := by
        erw [Fin.getElem_list]
        rfl
      rw [← h1']
      apply List.getElem_mem
    intro h2
    exact h j (h1 j) h2.symm
  · exact False.elim h

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

def HasSingColorDualsInOther : Prop := ∀ i, l.HasSingColorDualInOther l2 i
  ∨ ¬ l.HasDualInOther l2 i

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



end Color

-/
end IndexList

end IndexNotation
