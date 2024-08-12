/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.Dual
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Unique Dual indices

-/

namespace IndexNotation


namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 : IndexList X)


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
lemma getDual?_getDual_of_withUniqueDual (i : l.withUniqueDual) :
    l.getDual? (l.getDual i) = some i := by
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

end IndexList

end IndexNotation