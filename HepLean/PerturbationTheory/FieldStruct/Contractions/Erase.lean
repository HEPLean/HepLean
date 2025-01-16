/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.Contractions.Uncontracted
/-!

# Erasing an element from a contraction


-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)
open HepLean.List
open HepLean.Fin

def erase (c : ContractionsNat n.succ) (i : Fin n.succ) : ContractionsNat n := by
  refine ⟨Finset.filter (fun x => Finset.map i.succAboveEmb x ∈ c.1) Finset.univ, ?_, ?_⟩
  · intro a ha
    simpa using c.2.1 (Finset.map i.succAboveEmb a) (by simpa using ha)
  · intro a ha b hb
    simp at ha hb
    rw [← Finset.disjoint_map i.succAboveEmb, ← (Finset.map_injective i.succAboveEmb).eq_iff]
    exact c.2.2 _ ha _ hb

lemma mem_erase_uncontracted_iff (c : ContractionsNat n.succ) (i : Fin n.succ) (j : Fin n) :
    j ∈ (c.erase i).uncontracted ↔
    i.succAbove j ∈ c.uncontracted ∨ c.getDual? (i.succAbove j) = some i  := by
  rw [getDual?_eq_some_iff_mem]
  simp [uncontracted,erase, getDual?]
  rw [Fin.find_eq_none_iff, Fin.find_eq_none_iff]
  apply Iff.intro
  · intro h
    by_cases hi : {i.succAbove j, i} ∈ c.1
    · simp [hi]
    · apply Or.inl
      intro k
      by_cases hi' : k = i
      · subst hi'
        exact hi
      · simp [← Fin.exists_succAbove_eq_iff] at hi'
        obtain ⟨z, hz⟩ := hi'
        subst hz
        exact h z
  · intro h
    intro k
    rcases h with h | h
    · exact h (i.succAbove k)
    · by_contra hn
      have hc := c.2.2 _ h _ hn
      simp at hc
      have hi : i ∈ ({i.succAbove j, i.succAbove k} : Finset (Fin n.succ)) := by
        simp [← hc]
      simp at hi
      rcases hi with hi | hi
      · exact False.elim (Fin.succAbove_ne _ _ hi.symm)
      · exact False.elim (Fin.succAbove_ne _ _ hi.symm)


lemma mem_not_eq_erase_of_isSome (c : ContractionsNat n.succ) (i : Fin n.succ) (h : (c.getDual? i).isSome)
    (ha : a ∈ c.1) (ha2 : a ≠ {i, (c.getDual? i).get h}) :
    ∃ a', a' ∈ (c.erase i).1  ∧ a = Finset.map i.succAboveEmb a' := by
  have h2a := c.2.1 a ha
  rw [@Finset.card_eq_two] at h2a
  obtain ⟨x, y, hx,hy⟩ := h2a
  subst hy
  have hxn : ¬ x = i := by
    by_contra hx
    subst hx
    rw [← @getDual?_eq_some_iff_mem] at ha
    rw [(Option.get_of_mem h ha)] at ha2
    simp at ha2
  have hyn : ¬ y = i := by
    by_contra hy
    subst hy
    rw [@Finset.pair_comm] at ha
    rw [← @getDual?_eq_some_iff_mem] at ha
    rw [(Option.get_of_mem h ha)] at ha2
    simp [Finset.pair_comm] at ha2
  simp [← Fin.exists_succAbove_eq_iff] at hxn hyn
  obtain ⟨x', hx'⟩ := hxn
  obtain ⟨y', hy'⟩ := hyn
  use {x', y'}
  subst hx' hy'
  simp [erase]
  exact ha

lemma mem_not_eq_erase_of_isNone (c : ContractionsNat n.succ) (i : Fin n.succ) (h : (c.getDual? i).isNone)
    (ha : a ∈ c.1)  :
    ∃ a', a' ∈ (c.erase i).1  ∧ a = Finset.map i.succAboveEmb a' := by
  have h2a := c.2.1 a ha
  rw [@Finset.card_eq_two] at h2a
  obtain ⟨x, y, hx,hy⟩ := h2a
  subst hy
  have hi : i ∈ c.uncontracted := by
    simp [uncontracted, h]
    simp_all only [Nat.succ_eq_add_one, Option.isNone_iff_eq_none, ne_eq]
  rw [@mem_uncontracted_iff_not_contracted] at hi
  have hxn : ¬ x = i := by
    by_contra hx
    subst hx
    exact hi {x, y} ha (by simp)
  have hyn : ¬ y = i := by
    by_contra hy
    subst hy
    exact hi {x, y} ha (by simp)
  simp [← Fin.exists_succAbove_eq_iff] at hxn hyn
  obtain ⟨x', hx'⟩ := hxn
  obtain ⟨y', hy'⟩ := hyn
  use {x', y'}
  subst hx' hy'
  simp [erase]
  exact ha

def getDualErase {n : ℕ} (c : ContractionsNat n.succ) (i : Fin n.succ) :
    Option ((erase c i).uncontracted) := by
  match n with
  | 0 => exact none
  | Nat.succ n =>
  refine if hj : (c.getDual? i).isSome then some ⟨(predAboveI i ((c.getDual? i).get hj)), ?_⟩
    else none
  rw [mem_erase_uncontracted_iff]
  apply Or.inr
  rw [succsAbove_predAboveI, getDual?_eq_some_iff_mem]
  · simp
  · apply c.getDual?_eq_some_neq _ _ _
    simp

@[simp]
lemma getDualErase_isSome_iff_getDual?_isSome (c : ContractionsNat n.succ) (i : Fin n.succ) :
     (c.getDualErase i).isSome ↔ (c.getDual? i).isSome := by
  match n with
  | 0 =>
    fin_cases i
    simp [getDualErase]

  | Nat.succ n =>
    simp [getDualErase]

@[simp]
lemma getDualErase_one (c : ContractionsNat 1) (i : Fin 1) :
    c.getDualErase i = none := by
  fin_cases i
  simp [getDualErase]

end ContractionsNat

end FieldStruct
