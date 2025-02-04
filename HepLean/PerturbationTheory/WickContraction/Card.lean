/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Mathematics.Fin.Involutions
import HepLean.PerturbationTheory.WickContraction.ExtractEquiv
import HepLean.PerturbationTheory.WickContraction.Involutions
/-!

# Cardinality of Wick contractions
-/

open FieldSpecification
variable {𝓕 : FieldSpecification}
namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldStatistic
open Nat

lemma wickContraction_card_eq_sum_zero_none_isSome : Fintype.card (WickContraction n.succ)
    = Fintype.card {c : WickContraction n.succ // ¬ (c.getDual? 0).isSome} +
    Fintype.card {c : WickContraction n.succ // (c.getDual? 0).isSome} := by
  let e2 : WickContraction n.succ ≃ {c : WickContraction n.succ // (c.getDual? 0).isSome} ⊕
    {c : WickContraction n.succ // ¬ (c.getDual? 0).isSome} := by
    refine (Equiv.sumCompl _).symm
  rw [Fintype.card_congr e2]
  simp [add_comm]

lemma wickContraction_zero_none_card :
    Fintype.card {c : WickContraction n.succ // ¬ (c.getDual? 0).isSome} =
    Fintype.card (WickContraction n) := by
  simp only [succ_eq_add_one, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  symm
  exact Fintype.card_of_bijective (insertAndContractNat_bijective 0)

lemma wickContraction_zero_some_eq_sum :
    Fintype.card {c : WickContraction n.succ // (c.getDual? 0).isSome} =
    ∑ i, Fintype.card {c : WickContraction n.succ // (c.getDual? 0).isSome ∧
      ∀ (h : (c.getDual? 0).isSome), (c.getDual? 0).get h = Fin.succ i} := by
  let e1 : {c : WickContraction n.succ // (c.getDual? 0).isSome} ≃
    Σ i, {c : WickContraction n.succ // (c.getDual? 0).isSome ∧
      ∀ (h : (c.getDual? 0).isSome), (c.getDual? 0).get h = Fin.succ i} := {
    toFun c := ⟨((c.1.getDual? 0).get c.2).pred (by simp),
      ⟨c.1, ⟨c.2, by simp⟩⟩⟩
    invFun c := ⟨c.2, c.2.2.1⟩
    left_inv c := rfl
    right_inv c := by
      ext
      · simp [c.2.2.2]
      · rfl}
  rw [Fintype.card_congr e1]
  simp

lemma finset_succAbove_succ_disjoint (a : Finset (Fin n)) (i : Fin n.succ) :
    Disjoint ((Finset.map (Fin.succEmb (n + 1))) ((Finset.map i.succAboveEmb) a)) {0, i.succ} := by
  simp only [succ_eq_add_one, Finset.disjoint_insert_right, Finset.mem_map, Fin.succAboveEmb_apply,
    Fin.val_succEmb, exists_exists_and_eq_and, not_exists, not_and, Finset.disjoint_singleton_right,
    Fin.succ_inj, exists_eq_right]
  apply And.intro
  · exact fun x hx => Fin.succ_ne_zero (i.succAbove x)
  · exact fun x hx => Fin.succAbove_ne i x

/-- The Wick contraction in `WickContraction n.succ.succ` formed by a Wick contraction
  `WickContraction n` by inserting at the `0` and `i.succ` and contracting these two. -/
def consAddContract (i : Fin n.succ) (c : WickContraction n) :
    WickContraction n.succ.succ :=
  ⟨(c.1.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding).map
    (Finset.mapEmbedding (Fin.succEmb n.succ)).toEmbedding ∪ {{0, i.succ}}, by
    intro a
    simp only [succ_eq_add_one, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding, exists_exists_and_eq_and, Finset.mem_singleton]
    intro h
    rcases h with h | h
    · obtain ⟨a, ha, rfl⟩ := h
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
      simp only [Finset.card_map]
      exact c.2.1 a ha
    · subst h
      rw [@Finset.card_eq_two]
      use 0, i.succ
      simp only [succ_eq_add_one, ne_eq, and_true]
      exact ne_of_beq_false rfl, by
    intro a ha b hb
    simp only [succ_eq_add_one, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding, exists_exists_and_eq_and, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      simp only [succ_eq_add_one, EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply, Finset.mapEmbedding_apply,
        Finset.mapEmbedding_apply, Finset.disjoint_map, Finset.disjoint_map]
      exact c.2.2 a ha b hb
    · obtain ⟨a, ha, rfl⟩ := ha
      subst hb
      right
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
      exact finset_succAbove_succ_disjoint a i
    · obtain ⟨b, hb, rfl⟩ := hb
      subst ha
      right
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
      exact Disjoint.symm (finset_succAbove_succ_disjoint b i)
    · subst ha hb
      simp⟩

@[simp]
lemma consAddContract_getDual?_zero (i : Fin n.succ) (c : WickContraction n) :
    (consAddContract i c).getDual? 0 = some i.succ := by
  rw [getDual?_eq_some_iff_mem]
  simp [consAddContract]

@[simp]
lemma consAddContract_getDual?_self_succ (i : Fin n.succ) (c : WickContraction n) :
    (consAddContract i c).getDual? i.succ = some 0 := by
  rw [getDual?_eq_some_iff_mem]
  simp [consAddContract, Finset.pair_comm]

lemma mem_consAddContract_of_mem_iff (i : Fin n.succ) (c : WickContraction n) (a : Finset (Fin n)) :
    a ∈ c.1 ↔ (a.map i.succAboveEmb).map (Fin.succEmb n.succ) ∈ (consAddContract i c).1 := by
  simp only [succ_eq_add_one, consAddContract, Finset.le_eq_subset, Finset.mem_union,
    Finset.mem_map, RelEmbedding.coe_toEmbedding, exists_exists_and_eq_and, Finset.mem_singleton]
  apply Iff.intro
  · intro h
    left
    use a
    simp only [h, true_and]
    rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
  · intro h
    rcases h with h | h
    · obtain ⟨b, ha⟩ := h
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply] at ha
      simp only [Finset.map_inj] at ha
      rw [← ha.2]
      exact ha.1
    · have h1 := finset_succAbove_succ_disjoint a i
      rw [h] at h1
      simp at h1

lemma consAddContract_injective (i : Fin n.succ) : Function.Injective (consAddContract i) := by
  intro c1 c2 h
  apply Subtype.ext
  ext a
  apply Iff.intro
  · intro ha
    have ha' : (a.map i.succAboveEmb).map (Fin.succEmb n.succ) ∈ (consAddContract i c1).1 :=
      (mem_consAddContract_of_mem_iff i c1 a).mp ha
    rw [h] at ha'
    rw [← mem_consAddContract_of_mem_iff] at ha'
    exact ha'
  · intro ha
    have ha' : (a.map i.succAboveEmb).map (Fin.succEmb n.succ) ∈ (consAddContract i c2).1 :=
      (mem_consAddContract_of_mem_iff i c2 a).mp ha
    rw [← h] at ha'
    rw [← mem_consAddContract_of_mem_iff] at ha'
    exact ha'

lemma consAddContract_surjective_on_zero_contract (i : Fin n.succ)
    (c : WickContraction n.succ.succ)
    (h : (c.getDual? 0).isSome) (h2 : (c.getDual? 0).get h = i.succ) :
    ∃ c', consAddContract i c' = c := by
  let c' : WickContraction n :=
      ⟨Finset.filter
      (fun x => (Finset.map i.succAboveEmb x).map (Fin.succEmb n.succ) ∈ c.1) Finset.univ, by
    intro a ha
    simp only [succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simpa using c.2.1 _ ha, by
    intro a ha b hb
    simp only [Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rw [← Finset.disjoint_map i.succAboveEmb, ← (Finset.map_injective i.succAboveEmb).eq_iff]
    rw [← Finset.disjoint_map (Fin.succEmb n.succ),
      ← (Finset.map_injective (Fin.succEmb n.succ)).eq_iff]
    exact c.2.2 _ ha _ hb⟩
  use c'
  apply Subtype.ext
  ext a
  simp [consAddContract]
  apply Iff.intro
  · intro h
    rcases h with h | h
    · obtain ⟨b, hb, rfl⟩ := h
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
      exact hb
    · subst h
      rw [← h2]
      simp
  · intro h
    by_cases ha : a = {0, i.succ}
    · simp [ha]
    · left
      have hd := c.2.2 a h {0, i.succ} (by rw [← h2]; simp)
      simp_all only [succ_eq_add_one, Finset.disjoint_insert_right, Finset.disjoint_singleton_right,
        false_or]
      have ha2 := c.2.1 a h
      rw [@Finset.card_eq_two] at ha2
      obtain ⟨x, y, hx, rfl⟩ := ha2
      simp_all only [succ_eq_add_one, ne_eq, Finset.mem_insert, Finset.mem_singleton, not_or]
      obtain ⟨x, rfl⟩ := Fin.exists_succ_eq (x := x).mpr (by omega)
      obtain ⟨y, rfl⟩ := Fin.exists_succ_eq (x := y).mpr (by omega)
      simp_all only [Fin.succ_inj]
      obtain ⟨x, rfl⟩ := (Fin.exists_succAbove_eq (x := x) (y := i)) (by omega)
      obtain ⟨y, rfl⟩ := (Fin.exists_succAbove_eq (x := y) (y := i)) (by omega)
      use {x, y}
      simp only [Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton, Fin.val_succEmb,
        h, true_and]
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
      simp

lemma consAddContract_bijection (i : Fin n.succ) :
    Function.Bijective (fun c => (⟨(consAddContract i c), by simp⟩ :
    {c : WickContraction n.succ.succ // (c.getDual? 0).isSome ∧
      ∀ (h : (c.getDual? 0).isSome), (c.getDual? 0).get h = Fin.succ i})) := by
  apply And.intro
  · intro c1 c2 h
    simp only [succ_eq_add_one, Subtype.mk.injEq] at h
    exact consAddContract_injective i h
  · intro c
    obtain ⟨c', hc⟩ := consAddContract_surjective_on_zero_contract i c.1 c.2.1 (c.2.2 c.2.1)
    use c'
    simp [hc]

lemma wickContraction_zero_some_eq_mul :
    Fintype.card {c : WickContraction n.succ.succ // (c.getDual? 0).isSome} =
    (n + 1) * Fintype.card (WickContraction n) := by
  rw [wickContraction_zero_some_eq_sum]
  conv_lhs =>
    enter [2, i]
    rw [← Fintype.card_of_bijective (consAddContract_bijection i)]
  simp

/-- The cardinality of Wick's contractions as a recursive formula.
  This corresponds to OEIS:A000085. -/
def cardFun : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | Nat.succ (Nat.succ n) => cardFun (Nat.succ n) + (n + 1) * cardFun n

/-- The number of Wick contractions for `n : ℕ` fields, i.e. the cardinality of
  `WickContraction n`, is equal to the terms in
  Online Encyclopedia of Integer Sequences (OEIS) A000085. -/
theorem card_eq_cardFun : (n : ℕ) → Fintype.card (WickContraction n) = cardFun n
  | 0 => by decide
  | 1 => by decide
  | Nat.succ (Nat.succ n) => by
    rw [wickContraction_card_eq_sum_zero_none_isSome, wickContraction_zero_none_card,
      wickContraction_zero_some_eq_mul]
    simp only [cardFun, succ_eq_add_one]
    rw [← card_eq_cardFun n, ← card_eq_cardFun (n + 1)]

end WickContraction
