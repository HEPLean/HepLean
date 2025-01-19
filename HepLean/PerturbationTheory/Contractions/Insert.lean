/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.Erase
/-!

# Inserting an element into a contraction

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)
open HepLean.List
open HepLean.Fin

/-!

## Inserting an element into a contraction

-/

def insert (c : ContractionsNat n) (i : Fin n.succ) (j : Option (c.uncontracted)) :
    ContractionsNat n.succ := by
  let f := Finset.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding c.1
  let f' := match j with | none => f | some j => Insert.insert {i, i.succAbove j} f
  refine ⟨f', ?_, ?_⟩
  · simp only [Nat.succ_eq_add_one, f']
    match j with
    | none =>
      simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, f]
      intro a ha
      rw [Finset.mapEmbedding_apply]
      simp only [Finset.card_map]
      exact c.2.1 a ha
    | some j =>
      simp only [Finset.mem_insert, forall_eq_or_imp]
      apply And.intro
      · rw [@Finset.card_eq_two]
        use i
        use (i.succAbove j)
        simp only [ne_eq, and_true]
        exact Fin.ne_succAbove i j
      · simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, f]
        intro a ha
        rw [Finset.mapEmbedding_apply]
        simp only [Finset.card_map]
        exact c.2.1 a ha
  · intro a ha b hb
    simp only [Nat.succ_eq_add_one, f'] at ha hb
    match j with
    | none =>
      simp_all only [f, Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding,
        Nat.succ_eq_add_one]
      obtain ⟨a', ha', ha''⟩ := ha
      obtain ⟨b', hb', hb''⟩ := hb
      subst ha''
      subst hb''
      simp only [EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply, Finset.disjoint_map]
      exact c.2.2 a' ha' b' hb'
    | some j =>
      simp_all only [Finset.mem_insert, Nat.succ_eq_add_one]
      match ha, hb with
      | Or.inl ha, Or.inl hb =>
        rw [ha, hb]
        simp
      | Or.inl ha, Or.inr hb =>
        apply Or.inr
        subst ha
        simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left]
        simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding, f] at hb
        obtain ⟨a', hb', hb''⟩ := hb
        subst hb''
        rw [Finset.mapEmbedding_apply]
        apply And.intro
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          exact fun x _ => Fin.succAbove_ne i x
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          have hj := j.2
          rw [mem_uncontracted_iff_not_contracted] at hj
          intro a ha hja
          rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hja
          subst hja
          exact False.elim (hj a' hb' ha)
      | Or.inr ha, Or.inl hb =>
        apply Or.inr
        subst hb
        simp only [Finset.disjoint_insert_right, Nat.succ_eq_add_one,
          Finset.disjoint_singleton_right]
        simp only [Finset.le_eq_subset, Finset.mem_map, RelEmbedding.coe_toEmbedding, f] at ha
        obtain ⟨a', ha', ha''⟩ := ha
        subst ha''
        rw [Finset.mapEmbedding_apply]
        apply And.intro
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          exact fun x _ => Fin.succAbove_ne i x
        · simp only [Finset.mem_map, Fin.succAboveEmb_apply, not_exists, not_and]
          have hj := j.2
          rw [mem_uncontracted_iff_not_contracted] at hj
          intro a ha hja
          rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hja
          subst hja
          exact False.elim (hj a' ha' ha)
      | Or.inr ha, Or.inr hb =>
        simp_all only [f, Finset.le_eq_subset,
          or_true, Finset.mem_map, RelEmbedding.coe_toEmbedding]
        obtain ⟨a', ha', ha''⟩ := ha
        obtain ⟨b', hb', hb''⟩ := hb
        subst ha''
        subst hb''
        simp only [EmbeddingLike.apply_eq_iff_eq]
        rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply, Finset.disjoint_map]
        exact c.2.2 a' ha' b' hb'

lemma insert_of_isSome (c : ContractionsNat n) (i : Fin n.succ) (j : Option c.uncontracted)
    (hj : j.isSome) : (insert c i j).1 = Insert.insert {i, i.succAbove (j.get hj)}
    (Finset.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding c.1) := by
  simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset]
  rw [@Option.isSome_iff_exists] at hj
  obtain ⟨j, hj⟩ := hj
  subst hj
  simp

@[simp]
lemma self_mem_uncontracted_of_insert_none (c : ContractionsNat n) (i : Fin n.succ) :
    i ∈ (insert c i none).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at hp
  obtain ⟨a, ha, ha'⟩ := hp
  have hc := c.2.1 a ha
  rw [@Finset.card_eq_two] at hc
  obtain ⟨x, y, hxy, ha⟩ := hc
  subst ha
  subst ha'
  rw [Finset.mapEmbedding_apply]
  simp only [Nat.succ_eq_add_one, Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  apply And.intro
  · exact Fin.ne_succAbove i x
  · exact Fin.ne_succAbove i y

@[simp]
lemma self_not_mem_uncontracted_of_insert_some (c : ContractionsNat n) (i : Fin n.succ)
    (j : c.uncontracted) : i ∉ (insert c i (some j)).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  simp [insert]

@[simp]
lemma insert_succAbove_mem_uncontracted_iff (c : ContractionsNat n) (i : Fin n.succ) (j : Fin n) :
    (i.succAbove j) ∈ (insert c i none).uncontracted ↔ j ∈ c.uncontracted := by
  rw [mem_uncontracted_iff_not_contracted, mem_uncontracted_iff_not_contracted]
  simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset, Finset.mem_map,
    RelEmbedding.coe_toEmbedding, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  apply Iff.intro
  · intro h p hp
    have hp' := h p hp
    have hc := c.2.1 p hp
    rw [Finset.card_eq_two] at hc
    obtain ⟨x, y, hxy, hp⟩ := hc
    subst hp
    rw [Finset.mapEmbedding_apply] at hp'
    simp only [Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hp'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact And.intro (fun a => hp'.1 (congrArg i.succAbove a))
      (fun a => hp'.2 (congrArg i.succAbove a))
  · intro h p hp
    have hc := c.2.1 p hp
    rw [Finset.card_eq_two] at hc
    obtain ⟨x, y, hxy, hp⟩ := hc
    subst hp
    rw [Finset.mapEmbedding_apply]
    simp only [Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton, Finset.mem_insert,
      Finset.mem_singleton, not_or]
    have hp' := h {x, y} hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp'
    apply And.intro
      (fun a => hp'.1 (i.succAbove_right_injective a))
      (fun a => hp'.2 (i.succAbove_right_injective a))

@[simp]
lemma mem_uncontracted_insert_none_iff (c : ContractionsNat n) (i : Fin n.succ) (k : Fin n.succ) :
    k ∈ (insert c i none).uncontracted ↔
    k = i ∨ ∃ j, k = i.succAbove j ∧ j ∈ c.uncontracted := by
  by_cases hi : k = i
  · subst hi
    simp
  · simp only [Nat.succ_eq_add_one, ← Fin.exists_succAbove_eq_iff] at hi
    obtain ⟨z, hk⟩ := hi
    subst hk
    have hn : ¬ i.succAbove z = i := by exact Fin.succAbove_ne i z
    simp only [Nat.succ_eq_add_one, insert_succAbove_mem_uncontracted_iff, hn, false_or]
    apply Iff.intro
    · intro h
      exact ⟨z, rfl, h⟩
    · intro h
      obtain ⟨j, hk⟩ := h
      have hjk : z = j := Fin.succAbove_right_inj.mp hk.1
      subst hjk
      exact hk.2

lemma insert_none_uncontracted (c : ContractionsNat n) (i : Fin n.succ) :
    (insert c i none).uncontracted = Insert.insert i (c.uncontracted.map i.succAboveEmb) := by
  ext a
  simp only [Nat.succ_eq_add_one, mem_uncontracted_insert_none_iff, Finset.mem_insert,
    Finset.mem_map, Fin.succAboveEmb_apply]
  apply Iff.intro
  · intro a_1
    cases a_1 with
    | inl h =>
      subst h
      simp_all only [true_or]
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      obtain ⟨left, right⟩ := h
      subst left
      apply Or.inr
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only
  · intro a_1
    cases a_1 with
    | inl h =>
      subst h
      simp_all only [true_or]
    | inr h_1 =>
      obtain ⟨w, h⟩ := h_1
      obtain ⟨left, right⟩ := h
      subst right
      apply Or.inr
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {exact left
        }
        · simp_all only

@[simp]
lemma mem_uncontracted_insert_some_iff (c : ContractionsNat n) (i : Fin n.succ)
    (k : Fin n.succ) (j : c.uncontracted) :
    k ∈ (insert c i (some j)).uncontracted ↔
    ∃ z, k = i.succAbove z ∧ z ∈ c.uncontracted ∧ z ≠ j := by
  by_cases hki : k = i
  · subst hki
    simp only [Nat.succ_eq_add_one, self_not_mem_uncontracted_of_insert_some, ne_eq, false_iff,
      not_exists, not_and, Decidable.not_not]
    exact fun x hx => False.elim (Fin.ne_succAbove k x hx)
  · simp only [Nat.succ_eq_add_one, ← Fin.exists_succAbove_eq_iff] at hki
    obtain ⟨z, hk⟩ := hki
    subst hk
    by_cases hjz : j = z
    · subst hjz
      rw [mem_uncontracted_iff_not_contracted]
      simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset, Finset.mem_insert,
        Finset.mem_map, RelEmbedding.coe_toEmbedding, forall_eq_or_imp, Finset.mem_singleton,
        or_true, not_true_eq_false, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        false_and, ne_eq, false_iff, not_exists, not_and, Decidable.not_not]
      intro x
      rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)]
      exact fun a _a => a.symm
    · apply Iff.intro
      · intro h
        use z
        simp only [Nat.succ_eq_add_one, ne_eq, true_and]
        refine And.intro ?_ (fun a => hjz a.symm)
        rw [mem_uncontracted_iff_not_contracted]
        intro p hp
        rw [mem_uncontracted_iff_not_contracted] at h
        simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset, Finset.mem_insert,
          Finset.mem_map, RelEmbedding.coe_toEmbedding, forall_eq_or_imp, Finset.mem_singleton,
          not_or, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
        have hc := h.2 p hp
        rw [Finset.mapEmbedding_apply] at hc
        exact (Finset.mem_map' (i.succAboveEmb)).mpr.mt hc
      · intro h
        obtain ⟨z', hz'1, hz'⟩ := h
        rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hz'1
        subst hz'1
        rw [mem_uncontracted_iff_not_contracted]
        simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset, Finset.mem_insert,
          Finset.mem_map, RelEmbedding.coe_toEmbedding, forall_eq_or_imp, Finset.mem_singleton,
          not_or, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        apply And.intro
        · rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)]
          exact And.intro (Fin.succAbove_ne i z) (fun a => hjz a.symm)
        · rw [mem_uncontracted_iff_not_contracted] at hz'
          exact fun a ha hc => hz'.1 a ha ((Finset.mem_map' (i.succAboveEmb)).mp hc)

lemma insert_some_uncontracted (c : ContractionsNat n) (i : Fin n.succ) (j : c.uncontracted) :
    (insert c i (some j)).uncontracted = (c.uncontracted.erase j).map i.succAboveEmb := by
  ext a
  simp only [Nat.succ_eq_add_one, mem_uncontracted_insert_some_iff, ne_eq, Finset.map_erase,
    Fin.succAboveEmb_apply, Finset.mem_erase, Finset.mem_map]
  apply Iff.intro
  · intro h
    obtain ⟨z, h1, h2, h3⟩ := h
    subst h1
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)]
    simp only [h3, not_false_eq_true, true_and]
    use z
  · intro h
    obtain ⟨z, h1, h2⟩ := h.2
    use z
    subst h2
    simp only [true_and]
    obtain ⟨a, ha1, ha2⟩ := h.2
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at ha2
    subst ha2
    simp_all only [true_and]
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at h
    exact h.1

/-!

## Insert and getDual?

-/

lemma insert_none_getDual?_isNone (c : ContractionsNat n) (i : Fin n.succ) :
    ((insert c i none).getDual? i).isNone := by
  have hi : i ∈ (insert c i none).uncontracted := by
    simp
  simp only [Nat.succ_eq_add_one, uncontracted, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rw [hi]
  simp

@[simp]
lemma insert_succAbove_getDual?_eq_none_iff (c : ContractionsNat n) (i : Fin n.succ) (j : Fin n) :
    (insert c i none).getDual? (i.succAbove j) = none ↔ c.getDual? j = none := by
  have h1 := insert_succAbove_mem_uncontracted_iff c i j
  simpa [uncontracted] using h1

@[simp]
lemma insert_succAbove_getDual?_isSome_iff (c : ContractionsNat n) (i : Fin n.succ) (j : Fin n) :
    ((insert c i none).getDual? (i.succAbove j)).isSome ↔ (c.getDual? j).isSome := by
  rw [← not_iff_not]
  simp

@[simp]
lemma insert_succAbove_getDual?_get (c : ContractionsNat n) (i : Fin n.succ) (j : Fin n)
    (h : ((insert c i none).getDual? (i.succAbove j)).isSome) :
    ((insert c i none).getDual? (i.succAbove j)).get h =
    i.succAbove ((c.getDual? j).get (by simpa using h)) := by
  have h1 : (insert c i none).getDual? (i.succAbove j) = some
      (i.succAbove ((c.getDual? j).get (by simpa using h))) := by
    rw [getDual?_eq_some_iff_mem]
    simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    use {j, ((c.getDual? j).get (by simpa using h))}
    simp only [self_getDual?_get_mem, true_and]
    rw [Finset.mapEmbedding_apply]
    simp
  exact Option.get_of_mem h h1

@[simp]
lemma insert_some_getDual?_eq (c : ContractionsNat n) (i : Fin n.succ) (j : c.uncontracted) :
    (insert c i (some j)).getDual? i = some (i.succAbove j) := by
  rw [getDual?_eq_some_iff_mem]
  simp [insert]

@[simp]
lemma insert_some_getDual?_neq_none (c : ContractionsNat n) (i : Fin n.succ) (j : c.uncontracted)
    (k : Fin n) (hkj : k ≠ j.1) :
    (insert c i (some j)).getDual? (i.succAbove k) = none ↔ c.getDual? k = none := by
  apply Iff.intro
  · intro h
    have hk : (i.succAbove k) ∈ (insert c i (some j)).uncontracted := by
      simp only [Nat.succ_eq_add_one, uncontracted, Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    simp only [Nat.succ_eq_add_one, mem_uncontracted_insert_some_iff, ne_eq] at hk
    obtain ⟨z, hz1, hz2, hz3⟩ := hk
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hz1
    subst hz1
    simpa [uncontracted] using hz2
  · intro h
    have hk : (i.succAbove k) ∈ (insert c i (some j)).uncontracted := by
      simp only [Nat.succ_eq_add_one, mem_uncontracted_insert_some_iff, ne_eq]
      use k
      simp only [hkj, not_false_eq_true, and_true, true_and]
      simpa [uncontracted] using h
    simpa [uncontracted, -mem_uncontracted_insert_some_iff, ne_eq] using hk

@[simp]
lemma insert_some_getDual?_neq_isSome (c : ContractionsNat n) (i : Fin n.succ) (j : c.uncontracted)
    (k : Fin n) (hkj : k ≠ j.1) :
    ((insert c i (some j)).getDual? (i.succAbove k)).isSome ↔ (c.getDual? k).isSome := by
  rw [← not_iff_not]
  simp [hkj]

@[simp]
lemma insert_some_getDual?_neq_isSome_get (c : ContractionsNat n) (i : Fin n.succ)
    (j : c.uncontracted) (k : Fin n) (hkj : k ≠ j.1)
    (h : ((insert c i (some j)).getDual? (i.succAbove k)).isSome) :
    ((insert c i (some j)).getDual? (i.succAbove k)).get h =
    i.succAbove ((c.getDual? k).get (by simpa [hkj] using h)) := by
  have h1 : ((insert c i (some j)).getDual? (i.succAbove k))
    = some (i.succAbove ((c.getDual? k).get (by simpa [hkj] using h))) := by
    rw [getDual?_eq_some_iff_mem]
    simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset, Finset.mem_insert, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    apply Or.inr
    use { k, ((c.getDual? k).get (by simpa [hkj] using h))}
    simp only [self_getDual?_get_mem, true_and]
    rw [Finset.mapEmbedding_apply]
    simp
  exact Option.get_of_mem h h1

@[simp]
lemma insert_some_getDual?_of_neq (c : ContractionsNat n) (i : Fin n.succ) (j : c.uncontracted)
    (k : Fin n) (hkj : k ≠ j.1) :
    (insert c i (some j)).getDual? (i.succAbove k) =
    Option.map i.succAbove (c.getDual? k) := by
  by_cases h : (c.getDual? k).isSome
  · have h1 : (c.insert i (some j)).getDual? (i.succAbove k) =
        some (i.succAbove ((c.getDual? k).get h)) := by
      rw [← insert_some_getDual?_neq_isSome_get c i j k hkj]
      refine Eq.symm (Option.some_get ?_)
      simpa [hkj] using h
    rw [h1]
    have h2 :(c.getDual? k) = some ((c.getDual? k).get h) := by simp
    conv_rhs => rw [h2]
    rw [@Option.map_coe']
  · simp only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none] at h
    simp only [Nat.succ_eq_add_one, h, Option.map_none']
    simp only [ne_eq, hkj, not_false_eq_true, insert_some_getDual?_neq_none]
    exact h

/-!

## Interaction with erase.

-/
@[simp]
lemma insert_erase (c : ContractionsNat n) (i : Fin n.succ) (j : Option (c.uncontracted)) :
    erase (insert c i j) i = c := by
  refine Subtype.eq ?_
  simp only [erase, Nat.succ_eq_add_one, insert, Finset.le_eq_subset]
  conv_rhs => rw [c.eq_filter_mem_self]
  refine Finset.filter_inj'.mpr ?_
  intro a _
  match j with
  | none =>
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
    apply Iff.intro
    · intro ha
      obtain ⟨a', ha', ha''⟩ := ha
      rw [Finset.mapEmbedding_apply] at ha''
      simp only [Finset.map_inj] at ha''
      subst ha''
      exact ha'
    · intro ha
      use a
      simp only [ha, true_and]
      rw [Finset.mapEmbedding_apply]
  | some j =>
    simp only [Finset.mem_insert, Finset.mem_map, RelEmbedding.coe_toEmbedding]
    apply Iff.intro
    · intro ha
      rcases ha with ha | ha
      · have hin : ¬ i ∈ Finset.map i.succAboveEmb a := by
          simp only [Nat.succ_eq_add_one, Finset.mem_map, Fin.succAboveEmb_apply, not_exists,
            not_and]
          intro x
          exact fun a => Fin.succAbove_ne i x
        refine False.elim (hin ?_)
        rw [ha]
        simp
      · obtain ⟨a', ha', ha''⟩ := ha
        rw [Finset.mapEmbedding_apply] at ha''
        simp only [Finset.map_inj] at ha''
        subst ha''
        exact ha'
    · intro ha
      apply Or.inr
      use a
      simp only [ha, true_and]
      rw [Finset.mapEmbedding_apply]

lemma insert_getDualErase (c : ContractionsNat n) (i : Fin n.succ) (j : Option c.uncontracted) :
    (insert c i j).getDualErase i =
    uncontractedCongr (c := c) (c' := (c.insert i j).erase i) (by simp) j := by
  match n with
  | 0 =>
    simp only [insert, Nat.succ_eq_add_one, Nat.reduceAdd, Finset.le_eq_subset, getDualErase]
    fin_cases j
    simp
  | Nat.succ n =>
  match j with
  | none =>
    have hi := insert_none_getDual?_isNone c i
    simp [getDualErase, hi]
  | some j =>
    simp only [Nat.succ_eq_add_one, getDualErase, insert_some_getDual?_eq, Option.isSome_some,
      ↓reduceDIte, Option.get_some, predAboveI_succAbove, uncontractedCongr_some, Option.some.injEq]
    rfl

@[simp]
lemma erase_insert (c : ContractionsNat n.succ) (i : Fin n.succ) :
    insert (erase c i) i (getDualErase c i) = c := by
  match n with
  | 0 =>
    apply Subtype.eq
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, insert, getDualErase, Finset.le_eq_subset]
    ext a
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
    apply Iff.intro
    · intro h
      simp only [erase, Nat.reduceAdd, Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      obtain ⟨a', ha', ha''⟩ := h
      subst ha''
      exact ha'
    · intro ha
      obtain ⟨a, ha⟩ := c.mem_not_eq_erase_of_isNone (a := a) i (by simp) ha
      simp_all only [Nat.succ_eq_add_one]
      obtain ⟨left, right⟩ := ha
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only
  | Nat.succ n =>
  apply Subtype.eq
  by_cases hi : (c.getDual? i).isSome
  · rw [insert_of_isSome]
    simp only [Nat.succ_eq_add_one, getDualErase, hi, ↓reduceDIte, Option.get_some,
      Finset.le_eq_subset]
    rw [succsAbove_predAboveI]
    ext a
    apply Iff.intro
    · simp only [Finset.mem_insert, Finset.mem_map, RelEmbedding.coe_toEmbedding]
      intro ha
      rcases ha with ha | ha
      · subst ha
        simp
      · obtain ⟨a', ha', ha''⟩ := ha
        subst ha''
        simpa [erase] using ha'
    · intro ha
      simp only [Finset.mem_insert, Finset.mem_map, RelEmbedding.coe_toEmbedding]
      by_cases hia : a = {i, (c.getDual? i).get hi}
      · subst hia
        simp
      · apply Or.inr
        simp only [erase, Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, true_and]
        obtain ⟨a', ha'⟩ := c.mem_not_eq_erase_of_isSome (a := a) i hi ha hia
        use a'
        simp_all only [Nat.succ_eq_add_one, true_and]
        obtain ⟨left, right⟩ := ha'
        subst right
        rfl
    simp only [Nat.succ_eq_add_one, ne_eq, self_neq_getDual?_get, not_false_eq_true]
    exact (getDualErase_isSome_iff_getDual?_isSome c i).mpr hi
  · simp only [Nat.succ_eq_add_one, insert, getDualErase, hi, Bool.false_eq_true, ↓reduceDIte,
    Finset.le_eq_subset]
    ext a
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
    apply Iff.intro
    · intro h
      simp only [erase, Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, true_and] at h
      obtain ⟨a', ha', ha''⟩ := h
      subst ha''
      exact ha'
    · intro ha
      obtain ⟨a, ha⟩ := c.mem_not_eq_erase_of_isNone (a := a) i (by simpa using hi) ha
      simp_all only [Nat.succ_eq_add_one, Bool.not_eq_true, Option.not_isSome,
        Option.isNone_iff_eq_none]
      obtain ⟨left, right⟩ := ha
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only

/-- Lifts a contraction in `c` to a contraction in `(c.insert i j)`. -/
def insertLift {c : ContractionsNat n} (i : Fin n.succ) (j : Option (c.uncontracted))
    (a : c.1) : (c.insert i j).1 := ⟨a.1.map (Fin.succAboveEmb i), by
  simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset]
  match j with
  | none =>
    simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding]
    use a
    simp only [a.2, true_and]
    rfl
  | some j =>
    simp only [Finset.mem_insert, Finset.mem_map, RelEmbedding.coe_toEmbedding]
    apply Or.inr
    use a
    simp only [a.2, true_and]
    rfl⟩

lemma insertLift_injective {c : ContractionsNat n} (i : Fin n.succ) (j : Option (c.uncontracted)) :
    Function.Injective (insertLift i j) := by
  intro a b hab
  simp only [Nat.succ_eq_add_one, insertLift, Subtype.mk.injEq, Finset.map_inj] at hab
  exact Subtype.eq hab

lemma insertLift_none_surjective {c : ContractionsNat n} (i : Fin n.succ) :
    Function.Surjective (c.insertLift i none) := by
  intro a
  have ha := a.2
  simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha
  obtain ⟨a', ha', ha''⟩ := ha
  use ⟨a', ha'⟩
  exact Subtype.eq ha''

lemma insertLift_none_bijective {c : ContractionsNat n} (i : Fin n.succ) :
    Function.Bijective (c.insertLift i none) := by
  exact ⟨insertLift_injective i none, insertLift_none_surjective i⟩

@[simp]
lemma insert_fstFieldOfContract (c : ContractionsNat n) (i : Fin n.succ)
    (j : Option (c.uncontracted)) (a : c.1) : (c.insert i j).fstFieldOfContract (insertLift i j a) =
      i.succAbove (c.fstFieldOfContract a) := by
  refine (c.insert i j).eq_fstFieldOfContract_of_mem (a := (insertLift i j a))
    (i := i.succAbove (c.fstFieldOfContract a)) (j := i.succAbove (c.sndFieldOfContract a)) ?_ ?_ ?_
  · simp only [Nat.succ_eq_add_one, insertLift, Finset.mem_map, Fin.succAboveEmb_apply]
    use (c.fstFieldOfContract a)
    simp
  · simp only [Nat.succ_eq_add_one, insertLift, Finset.mem_map, Fin.succAboveEmb_apply]
    use (c.sndFieldOfContract a)
    simp
  · refine Fin.succAbove_lt_succAbove_iff.mpr ?_
    exact fstFieldOfContract_lt_sndFieldOfContract c a

@[simp]
lemma insert_sndFieldOfContract (c : ContractionsNat n) (i : Fin n.succ)
    (j : Option (c.uncontracted)) (a : c.1) : (c.insert i j).sndFieldOfContract (insertLift i j a) =
    i.succAbove (c.sndFieldOfContract a) := by
  refine (c.insert i j).eq_sndFieldOfContract_of_mem (a := (insertLift i j a))
    (i := i.succAbove (c.fstFieldOfContract a)) (j := i.succAbove (c.sndFieldOfContract a)) ?_ ?_ ?_
  · simp only [Nat.succ_eq_add_one, insertLift, Finset.mem_map, Fin.succAboveEmb_apply]
    use (c.fstFieldOfContract a)
    simp
  · simp only [Nat.succ_eq_add_one, insertLift, Finset.mem_map, Fin.succAboveEmb_apply]
    use (c.sndFieldOfContract a)
    simp
  · refine Fin.succAbove_lt_succAbove_iff.mpr ?_
    exact fstFieldOfContract_lt_sndFieldOfContract c a

def insertLiftSome {c : ContractionsNat n} (i : Fin n.succ) (j : c.uncontracted)
    (a : Unit ⊕ c.1) : (c.insert i (some j)).1 :=
  match a with
  | Sum.inl () => ⟨{i, i.succAbove j}, by
    simp [insert]⟩
  | Sum.inr a => c.insertLift i j a

lemma insertLiftSome_injective {c : ContractionsNat n} (i : Fin n.succ) (j : c.uncontracted) :
    Function.Injective (insertLiftSome i j) := by
  intro a b hab
  match a, b with
  | Sum.inl (), Sum.inl () => rfl
  | Sum.inl (), Sum.inr a =>
    simp only [Nat.succ_eq_add_one, insertLiftSome, insertLift, Subtype.mk.injEq] at hab
    rw [finset_eq_fstFieldOfContract_sndFieldOfContract] at hab
    simp only [Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton] at hab
    have hi : i ∈ ({i.succAbove (c.fstFieldOfContract a),
        i.succAbove (c.sndFieldOfContract a)} : Finset (Fin (n + 1))) := by
      rw [← hab]
      simp
    simp only [Nat.succ_eq_add_one, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · exact False.elim (Fin.ne_succAbove _ _ hi)
    · exact False.elim (Fin.ne_succAbove _ _ hi)
  | Sum.inr a, Sum.inl () =>
    simp only [Nat.succ_eq_add_one, insertLiftSome, insertLift, Subtype.mk.injEq] at hab
    rw [finset_eq_fstFieldOfContract_sndFieldOfContract] at hab
    simp only [Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton] at hab
    have hi : i ∈ ({i.succAbove (c.fstFieldOfContract a),
        i.succAbove (c.sndFieldOfContract a)} : Finset (Fin (n + 1))) := by
      rw [hab]
      simp
    simp only [Nat.succ_eq_add_one, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with hi | hi
    · exact False.elim (Fin.ne_succAbove _ _ hi)
    · exact False.elim (Fin.ne_succAbove _ _ hi)
  | Sum.inr a, Sum.inr b =>
    simp only [Nat.succ_eq_add_one, insertLiftSome] at hab
    simpa using insertLift_injective i (some j) hab

lemma insertLiftSome_surjective {c : ContractionsNat n} (i : Fin n.succ) (j : c.uncontracted) :
    Function.Surjective (insertLiftSome i j) := by
  intro a
  have ha := a.2
  simp only [Nat.succ_eq_add_one, insert, Finset.le_eq_subset, Finset.mem_insert, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha
  rcases ha with ha | ha
  · use Sum.inl ()
    exact Subtype.eq ha.symm
  · obtain ⟨a', ha', ha''⟩ := ha
    use Sum.inr ⟨a', ha'⟩
    simp only [Nat.succ_eq_add_one, insertLiftSome, insertLift]
    exact Subtype.eq ha''

lemma insertLiftSome_bijective {c : ContractionsNat n} (i : Fin n.succ) (j : c.uncontracted) :
    Function.Bijective (insertLiftSome i j) :=
  ⟨insertLiftSome_injective i j, insertLiftSome_surjective i j⟩

end ContractionsNat

end FieldStruct
