/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.NormalOrder
import HepLean.PerturbationTheory.Wick.Signs.KoszulSign
import HepLean.Mathematics.List.InsertIdx
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image
/-!

# Contractions


-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

def ContractionsNat (n : ℕ) : Type :=
  {f : Finset ((Finset (Fin n))) // (∀ a ∈ f, a.card = 2) ∧
    (∀ a ∈ f, ∀ b ∈ f, a = b ∨ Disjoint a b)}

namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)
open HepLean.List

local instance : IsTotal (Fin n × Fin n) (fun a b => a.1 ≤ b.1) where
  total := by
    intro a b
    exact le_total a.1 b.1

local instance : IsTrans (Fin n × Fin n) (fun a b => a.1 ≤ b.1) where
  trans := by
    intro a b c ha hb
    exact Fin.le_trans ha hb

def congr : {n m : ℕ} → (h : n = m) → ContractionsNat n ≃ ContractionsNat m
  | n, .(n), rfl => Equiv.refl _

@[simp]
lemma congr_refl : c.congr rfl = c := by
  cases c
  rfl

def getDual? (i : Fin n) : Option (Fin n) := Fin.find (fun j => {i, j} ∈ c.1)

lemma getDual?_eq_some_iff_mem (i j : Fin n) :
    c.getDual? i = some j ↔ {i, j} ∈ c.1 := by
  simp [getDual?]
  rw [Fin.find_eq_some_iff]
  apply Iff.intro
  · intro h
    exact h.1
  · intro h
    simp [h]
    intro k hk
    have hc := c.2.2 _ h _ hk
    simp at hc
    have hj : k ∈ ({i, j} : Finset (Fin n)):= by
      simp [hc]
    simp at hj
    rcases hj with hj | hj
    · subst hj
      simp at hk
      have hc := c.2.1 _ hk
      simp at hc
    · subst hj
      simp

@[simp]
lemma getDual?_one_eq_none (c : ContractionsNat 1) (i : Fin 1) : c.getDual? i = none := by
  by_contra h
  have hn : (c.getDual? i).isSome := by
    rw [← Option.not_isSome_iff_eq_none] at h
    simpa  [- Option.not_isSome, -Option.isNone_iff_eq_none] using h
  rw [@Option.isSome_iff_exists] at hn
  obtain ⟨a, hn⟩ := hn
  rw [getDual?_eq_some_iff_mem] at hn
  have hc := c.2.1 {i, a} hn
  fin_cases i
  fin_cases a
  simp at hc

@[simp]
lemma getDual?_get_self_mem (i : Fin n) (h : (c.getDual? i).isSome) :
    {(c.getDual? i).get h, i} ∈ c.1 := by
  rw [@Finset.pair_comm]
  rw [← getDual?_eq_some_iff_mem]
  simp

@[simp]
lemma self_getDual?_get_mem (i : Fin n) (h : (c.getDual? i).isSome) :
    {i, (c.getDual? i).get h} ∈ c.1 := by
  rw [← getDual?_eq_some_iff_mem]
  simp

lemma getDual?_eq_some_neq (i j : Fin n) (h : c.getDual? i = some j) :
     ¬ i = j := by
  rw [getDual?_eq_some_iff_mem] at h
  by_contra hn
  subst hn
  have hc := c.2.1 _ h
  simp at hc

@[simp]
lemma self_neq_getDual?_get (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ i = (c.getDual? i).get h := by
  by_contra hn
  have hx : {i, (c.getDual? i).get h} ∈ c.1 := by simp
  have hc := c.2.1 _ hx
  nth_rewrite 1 [hn] at hc
  simp at hc

@[simp]
lemma getDual?_get_self_neq (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ (c.getDual? i).get h  = i := by
  by_contra hn
  have hx : {i, (c.getDual? i).get h} ∈ c.1 := by simp
  have hc := c.2.1 _ hx
  nth_rewrite 1 [hn] at hc
  simp at hc

def uncontracted : Finset (Fin n) := Finset.filter (fun i => c.getDual? i = none) (Finset.univ)

lemma congr_uncontracted {n m : ℕ} (c : ContractionsNat n) (h : n = m) :
    (c.congr h).uncontracted = Finset.map (finCongr h).toEmbedding c.uncontracted := by
  subst h
  simp

def uncontractedCongr {c c': ContractionsNat n} (h : c = c') :
    Option c.uncontracted ≃ Option c'.uncontracted :=
    Equiv.optionCongr (Equiv.subtypeEquivRight (by rw [h]; simp))

@[simp]
lemma uncontractedCongr_none {c c': ContractionsNat n} (h : c = c') :
    (uncontractedCongr h) none = none := by
  simp [uncontractedCongr]

@[simp]
lemma uncontractedCongr_some {c c': ContractionsNat n} (h : c = c') (i : c.uncontracted) :
    (uncontractedCongr h) (some i) = some (Equiv.subtypeEquivRight (by rw [h]; simp) i) := by
  simp [uncontractedCongr]


lemma mem_uncontracted_iff_not_contracted (i : Fin n)  :
    i ∈ c.uncontracted ↔ ∀ p ∈ c.1, i ∉ p := by
  simp [uncontracted, getDual?]
  apply Iff.intro
  · intro h p hp
    have hp := c.2.1 p hp
    rw [Finset.card_eq_two] at hp
    obtain ⟨a, b, ha, hb, hab⟩ := hp
    rw [Fin.find_eq_none_iff] at h
    by_contra hn
    simp at hn
    rcases hn with hn | hn
    · subst hn
      exact h b hp
    · subst hn
      rw [Finset.pair_comm] at hp
      exact h a hp
  · intro h
    rw [Fin.find_eq_none_iff]
    by_contra hn
    simp at hn
    obtain ⟨j, hj⟩ := hn
    apply h {i, j} hj
    simp

lemma eq_filter_mem_self : c.1 = Finset.filter (fun x => x ∈ c.1) Finset.univ := by
  exact Eq.symm (Finset.filter_univ_mem c.1)

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

def insert (c : ContractionsNat n) (i : Fin n.succ) (j : Option (c.uncontracted)) :
    ContractionsNat n.succ := by
  let f := Finset.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding c.1
  let f' := match j with | none => f | some j => Insert.insert {i, i.succAbove j} f
  refine ⟨f', ?_, ?_⟩
  · simp [f']
    match j with
    | none =>
      simp [f', f]
      intro a ha
      rw [Finset.mapEmbedding_apply]
      simp [Finset.mapEmbedding_apply]
      exact c.2.1  a ha
    | some j =>
      simp
      apply And.intro
      · rw [@Finset.card_eq_two]
        use i
        use (i.succAbove j)
        simp
        exact Fin.ne_succAbove i j
      · simp [f]
        intro a ha
        rw [Finset.mapEmbedding_apply]
        simp
        exact c.2.1 a ha
  · intro a ha b hb
    simp [f'] at ha hb
    match j with
    | none =>
      simp_all [f]
      obtain ⟨a', ha', ha''⟩ := ha
      obtain ⟨b', hb', hb''⟩ := hb
      subst ha''
      subst hb''
      simp
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply, Finset.disjoint_map]
      exact c.2.2 a' ha' b' hb'
    | some j =>
      simp_all
      match ha, hb with
      | Or.inl ha, Or.inl hb =>
        rw [ha, hb]
        simp
      | Or.inl ha, Or.inr hb =>
        apply Or.inr
        subst ha
        simp
        simp [f] at hb
        obtain ⟨a', hb', hb''⟩ := hb
        subst hb''
        rw [Finset.mapEmbedding_apply]
        apply And.intro
        · simp
          exact fun x _  => Fin.succAbove_ne i x
        · simp
          have hj := j.2
          rw [mem_uncontracted_iff_not_contracted] at hj
          intro a ha hja
          rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hja
          subst hja
          exact False.elim (hj a' hb' ha)
      | Or.inr ha, Or.inl hb =>
        apply Or.inr
        subst hb
        simp
        simp [f] at ha
        obtain ⟨a', ha', ha''⟩ := ha
        subst ha''
        rw [Finset.mapEmbedding_apply]
        apply And.intro
        · simp
          exact fun x _ => Fin.succAbove_ne i x
        · simp
          have hj := j.2
          rw [mem_uncontracted_iff_not_contracted] at hj
          intro a ha hja
          rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hja
          subst hja
          exact False.elim (hj a' ha' ha)
      | Or.inr ha, Or.inr hb =>
        simp_all [f]
        obtain ⟨a', ha', ha''⟩ := ha
        obtain ⟨b', hb', hb''⟩ := hb
        subst ha''
        subst hb''
        simp
        rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply, Finset.disjoint_map]
        exact c.2.2 a' ha' b' hb'

lemma insert_of_isSome (c : ContractionsNat n) (i : Fin n.succ) (j : Option c.uncontracted) (hj : j.isSome) :
    (insert c i j).1 = Insert.insert {i, i.succAbove (j.get hj)}
    (Finset.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding c.1) := by
  simp [insert]
  rw [@Option.isSome_iff_exists] at hj
  obtain ⟨j, hj⟩ := hj
  subst hj
  simp

@[simp]
lemma self_mem_uncontracted_of_insert_none (c : ContractionsNat n) (i : Fin n.succ) :
    i ∈ (insert c i none).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  simp [insert] at hp
  obtain ⟨a, ha, ha'⟩ := hp
  have hc := c.2.1 a ha
  rw [@Finset.card_eq_two] at hc
  obtain ⟨x, y, hxy, ha⟩ := hc
  subst ha
  subst ha'
  rw [Finset.mapEmbedding_apply]
  simp
  apply And.intro
  · exact Fin.ne_succAbove i x
  · exact Fin.ne_succAbove i y


lemma insert_none_getDual?_isNone (c : ContractionsNat n) (i : Fin n.succ) :
    ((insert c i none).getDual? i).isNone := by
  have hi : i ∈ (insert c i none).uncontracted := by
    simp
  simp [uncontracted] at hi
  rw [hi]
  simp

@[simp]
lemma self_not_mem_uncontracted_of_insert_some (c : ContractionsNat n) (i : Fin n.succ) (j : c.uncontracted) :
    i ∉ (insert c i (some j)).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  simp [insert]

@[simp]
lemma insert_succAbove_mem_uncontracted_iff (c : ContractionsNat n) (i : Fin n.succ) (j : Fin n) :
    (i.succAbove j) ∈ (insert c i none).uncontracted ↔ j ∈ c.uncontracted := by
  rw [mem_uncontracted_iff_not_contracted, mem_uncontracted_iff_not_contracted]
  simp [insert]
  apply Iff.intro
  · intro h p hp
    have hp' := h p hp
    have hc := c.2.1 p hp
    rw [Finset.card_eq_two] at hc
    obtain ⟨x, y, hxy, hp⟩ := hc
    subst hp
    rw [Finset.mapEmbedding_apply] at hp'
    simp at hp'
    simp
    exact And.intro (fun a => hp'.1 (congrArg i.succAbove a))
      (fun a => hp'.2 (congrArg i.succAbove a))
  · intro h p hp
    have hc := c.2.1 p hp
    rw [Finset.card_eq_two] at hc
    obtain ⟨x, y, hxy, hp⟩ := hc
    subst hp
    rw [Finset.mapEmbedding_apply]
    simp
    have hp' := h {x, y} hp
    simp at hp'
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
  · simp [← Fin.exists_succAbove_eq_iff] at hi
    obtain ⟨z, hk⟩ := hi
    subst hk
    have hn :  ¬ i.succAbove z = i := by exact Fin.succAbove_ne i z
    simp [hn]
    apply Iff.intro
    · intro h
      exact  ⟨z, rfl, h⟩
    · intro h
      obtain ⟨j, hk⟩ := h
      have hjk : z = j := Fin.succAbove_right_inj.mp hk.1
      subst hjk
      exact hk.2

lemma insert_none_uncontracted (c : ContractionsNat n) (i : Fin n.succ) :
    (insert c i none).uncontracted = Insert.insert i (c.uncontracted.map i.succAboveEmb) := by
  ext a
  simp
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
    simp
    exact fun x hx => False.elim (Fin.ne_succAbove k x hx)
  · simp [← Fin.exists_succAbove_eq_iff] at hki
    obtain ⟨z, hk⟩ := hki
    subst hk
    by_cases hjz : j = z
    · subst hjz
      rw [mem_uncontracted_iff_not_contracted]
      simp [insert]
      intro x
      rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)]
      exact fun a _a => a.symm
    · apply Iff.intro
      · intro h
        use z
        simp
        refine And.intro ?_ (fun a => hjz a.symm)
        rw [mem_uncontracted_iff_not_contracted]
        intro p hp
        rw [mem_uncontracted_iff_not_contracted] at h
        simp [insert] at h
        have hc := h.2 p hp
        rw [Finset.mapEmbedding_apply] at hc
        exact (Finset.mem_map' (i.succAboveEmb)).mpr.mt hc
      · intro h
        obtain ⟨z', hz'1, hz'⟩ := h
        rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at hz'1
        subst hz'1
        rw [mem_uncontracted_iff_not_contracted]
        simp [insert]
        apply And.intro
        · rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)]
          exact And.intro (Fin.succAbove_ne i z) (fun a => hjz a.symm)
        · rw [mem_uncontracted_iff_not_contracted] at hz'
          exact fun a ha hc => hz'.1 a ha ((Finset.mem_map' (i.succAboveEmb)).mp hc)

lemma insert_some_uncontracted  (c : ContractionsNat n) (i : Fin n.succ) (j : c.uncontracted) :
    (insert c i (some j)).uncontracted = (c.uncontracted.erase j).map i.succAboveEmb := by
  ext a
  simp
  apply Iff.intro
  · intro h
    obtain ⟨z, h1, h2, h3⟩ := h
    subst h1
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)]
    simp [h3]
    use z
  · intro h
    obtain ⟨z, h1, h2⟩ := h.2
    use z
    subst h2
    simp
    obtain ⟨a, ha1 , ha2⟩ := h.2
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at ha2
    subst ha2
    simp_all
    rw [Function.Injective.eq_iff (Fin.succAbove_right_injective)] at h
    exact h.1

@[simp]
lemma insert_some_getDual?_eq (c : ContractionsNat n) (i : Fin n.succ) (j : c.uncontracted) :
    (insert c i (some j)).getDual? i = some (i.succAbove j) := by
  rw [getDual?_eq_some_iff_mem]
  simp [insert]

@[simp]
lemma insert_erase (c : ContractionsNat n) (i : Fin n.succ) (j : Option (c.uncontracted)) :
    erase (insert c i j) i = c := by
  refine Subtype.eq ?_
  simp [insert, erase]
  conv_rhs => rw [c.eq_filter_mem_self]
  refine Finset.filter_inj'.mpr ?_
  intro a _
  match j with
  | none =>
    simp
    apply Iff.intro
    · intro ha
      obtain ⟨a', ha', ha''⟩ := ha
      rw [Finset.mapEmbedding_apply] at ha''
      simp at ha''
      subst ha''
      exact ha'
    · intro ha
      use a
      simp [ha]
      rw [Finset.mapEmbedding_apply]
  | some j =>
    simp
    apply Iff.intro
    · intro ha
      rcases ha with ha | ha
      · have hin : ¬ i ∈ Finset.map i.succAboveEmb a := by
          simp
          intro x
          exact fun a => Fin.succAbove_ne i x
        refine False.elim (hin ?_)
        rw [ha]
        simp
      · obtain ⟨a', ha', ha''⟩ := ha
        rw [Finset.mapEmbedding_apply] at ha''
        simp at ha''
        subst ha''
        exact ha'
    · intro ha
      apply Or.inr
      use a
      simp [ha]
      rw [Finset.mapEmbedding_apply]

open HepLean.Fin

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

lemma insert_getDualErase (c : ContractionsNat n) (i : Fin n.succ) (j : Option c.uncontracted) :
    (insert c i j).getDualErase i = uncontractedCongr (c := c) (c' := (c.insert i j).erase i) (by simp) j := by
  match n with
  | 0 =>
    simp [getDualErase, insert]
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
    simp [getDualErase,  insert]
    ext a
    simp
    apply Iff.intro
    · intro h
      simp only [erase, Nat.reduceAdd, Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ,
        true_and] at h
      obtain ⟨a', ha', ha''⟩ := h
      subst ha''
      exact ha'
    · intro ha
      obtain ⟨a, ha⟩ := c.mem_not_eq_erase_of_isNone (a := a) i (by simp) ha
      simp_all only [Nat.succ_eq_add_one, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
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
    simp [getDualErase, hi]
    rw [succsAbove_predAboveI]
    ext a
    apply Iff.intro
    · simp
      intro ha
      rcases ha with ha | ha
      · subst ha
        simp
      · obtain ⟨a', ha', ha''⟩ := ha
        subst ha''
        simpa [erase] using ha'
    · intro ha
      simp
      by_cases hia :  a = {i, (c.getDual? i).get hi}
      · subst hia
        simp
      · apply Or.inr
        simp [erase]
        obtain ⟨a', ha'⟩ := c.mem_not_eq_erase_of_isSome (a := a) i hi ha hia
        use a'
        simp_all only [Nat.succ_eq_add_one, true_and]
        obtain ⟨left, right⟩ := ha'
        subst right
        rfl
    simp
    exact (getDualErase_isSome_iff_getDual?_isSome c i).mpr hi
  · simp [getDualErase, hi, insert]
    ext a
    simp
    apply Iff.intro
    · intro h
      simp [erase] at h
      obtain ⟨a', ha', ha''⟩ := h
      subst ha''
      exact ha'
    · intro ha
      obtain ⟨a, ha⟩ := c.mem_not_eq_erase_of_isNone (a := a) i (by simpa using hi) ha
      simp_all only [Nat.succ_eq_add_one, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
      obtain ⟨left, right⟩ := ha
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only

/-!

## extractEquiv

-/

lemma extractEquiv_equiv {c1 c2 : (c : ContractionsNat n) × Option c.uncontracted}
    (h : c1.1 = c2.1) (ho : c1.2 = uncontractedCongr (by rw [h]) c2.2) : c1 = c2 := by
  cases c1
  cases c2
  simp_all
  simp at h
  subst h
  simp [uncontractedCongr]
  rename_i a
  match a with
  | none => simp
  | some a =>
    simp
    ext
    simp


def extractEquiv (i : Fin n.succ) : ContractionsNat n.succ ≃
    (c : ContractionsNat n) × Option c.uncontracted  where
  toFun := fun c => ⟨erase c i, getDualErase c i⟩
  invFun := fun ⟨c, j⟩ => insert c i j
  left_inv f := by
    simp
  right_inv f := by
    refine extractEquiv_equiv ?_ ?_
    simp
    simp
    have h1 := insert_getDualErase f.fst i f.snd
    exact insert_getDualErase _ i _

lemma extractEquiv_symm_none_uncontracted (i : Fin n.succ)  (c : ContractionsNat n) :
    ((extractEquiv i).symm ⟨c, none⟩).uncontracted =
    (Insert.insert i (c.uncontracted.map i.succAboveEmb)) := by
  exact insert_none_uncontracted c i

def nil : ContractionsNat n := ⟨∅, by simp, by simp⟩

instance fintype_zero : Fintype (ContractionsNat 0) where
  elems := {nil}
  complete := by
    intro c
    simp
    apply Subtype.eq
    simp [nil]
    ext a
    apply Iff.intro
    · intro h
      have hc := c.2.1 a h
      rw [Finset.card_eq_two] at hc
      obtain ⟨x, y, hxy, ha⟩ := hc
      exact Fin.elim0 x
    · simp

instance fintype_succ : (n : ℕ) → Fintype (ContractionsNat n)
  | 0 => fintype_zero
  | Nat.succ n => by
    letI := fintype_succ n
    exact Fintype.ofEquiv _ (extractEquiv 0).symm

/-!

## Uncontracted List

-/
def uncontractedList : List (Fin n) := List.filter (fun x => x ∈ c.uncontracted) (List.finRange n)

lemma uncontractedList_mem_iff (i : Fin n) :
    i ∈ c.uncontractedList ↔  i ∈ c.uncontracted := by
  simp [uncontractedList]

lemma congr_uncontractedList {n m : ℕ} (h : n = m) (c : ContractionsNat n) :
    ((congr h) c).uncontractedList = List.map (finCongr h) c.uncontractedList := by
  subst h
  simp [congr]

lemma uncontractedList_get_mem_uncontracted (i : Fin c.uncontractedList.length) :
    c.uncontractedList.get i ∈ c.uncontracted := by
  rw [← uncontractedList_mem_iff]
  simp

lemma uncontractedList_sorted : List.Sorted (· ≤ ·) c.uncontractedList := by
  rw [uncontractedList]
  apply List.Sorted.filter
  rw [← List.ofFn_id]
  exact Monotone.ofFn_sorted fun ⦃a b⦄ a => a

lemma uncontractedList_nodup : c.uncontractedList.Nodup := by
  rw [uncontractedList]
  refine List.Nodup.filter (fun x => decide (x ∈ c.uncontracted)) ?_
  exact List.nodup_finRange n

lemma uncontractedList_toFinset (c : ContractionsNat n) :
    c.uncontractedList.toFinset = c.uncontracted := by
  simp [uncontractedList]

lemma uncontractedList_eq_sort (c : ContractionsNat n) :
    c.uncontractedList = c.uncontracted.sort (· ≤ ·) := by
  symm
  rw [← uncontractedList_toFinset]
  refine (List.toFinset_sort (α := Fin n) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_nodup c
  · exact uncontractedList_sorted c

lemma uncontractedList_length_eq_card (c : ContractionsNat n) :
    c.uncontractedList.length = c.uncontracted.card := by
  rw [uncontractedList_eq_sort]
  exact Finset.length_sort fun x1 x2 => x1 ≤ x2



lemma fin_list_sorted_monotone_sorted {n m : ℕ} (l: List (Fin n)) (hl : l.Sorted (· ≤ ·))
   (f : Fin n → Fin m) (hf : StrictMono f) :
    ((List.map f l)).Sorted (· ≤ ·) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp
    apply And.intro
    · simp at hl
      intro b hb
      have hl1 := hl.1 b hb
      exact (StrictMono.le_iff_le hf).mpr hl1
    · simp at hl
      exact ih hl.2

lemma fin_list_sorted_succAboveEmb_sorted (l: List (Fin n)) (hl : l.Sorted (· ≤ ·)) (i : Fin n.succ)  :
    ((List.map i.succAboveEmb l)).Sorted (· ≤ ·) := by
  apply fin_list_sorted_monotone_sorted
  exact hl
  simp
  exact Fin.strictMono_succAbove i

lemma uncontractedList_succAboveEmb_sorted (c : ContractionsNat n) (i : Fin n.succ) :
    ((List.map i.succAboveEmb c.uncontractedList)).Sorted (· ≤ ·) := by
  apply fin_list_sorted_succAboveEmb_sorted
  exact uncontractedList_sorted c

lemma uncontractedList_succAboveEmb_nodup (c : ContractionsNat n) (i : Fin n.succ) :
    ((List.map i.succAboveEmb c.uncontractedList)).Nodup := by
  refine List.Nodup.map ?_ ?_
  · exact Function.Embedding.injective i.succAboveEmb
  · exact uncontractedList_nodup c

lemma uncontractedList_succAboveEmb_toFinset (c : ContractionsNat n) (i : Fin n.succ) :
    (List.map i.succAboveEmb c.uncontractedList).toFinset = (Finset.map i.succAboveEmb c.uncontracted) := by
  ext a
  simp
  rw [← c.uncontractedList_toFinset]
  simp

lemma uncontractedList_succAboveEmb_eq_sort(c : ContractionsNat n) (i : Fin n.succ) :
    (List.map i.succAboveEmb c.uncontractedList) =
    (c.uncontracted.map i.succAboveEmb).sort (· ≤ ·)  := by
  rw [← uncontractedList_succAboveEmb_toFinset]
  symm
  refine (List.toFinset_sort (α := Fin n.succ) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_succAboveEmb_nodup c i
  · exact uncontractedList_succAboveEmb_sorted c i

lemma uncontractedList_succAboveEmb_eraseIdx_sorted (c : ContractionsNat n) (i : Fin n.succ) (k: ℕ) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).Sorted (· ≤ ·) := by
  apply HepLean.List.eraseIdx_sorted
  exact uncontractedList_succAboveEmb_sorted c i

lemma uncontractedList_succAboveEmb_eraseIdx_nodup (c : ContractionsNat n) (i : Fin n.succ) (k: ℕ) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).Nodup := by
  refine List.Nodup.eraseIdx k ?_
  exact uncontractedList_succAboveEmb_nodup c i

lemma uncontractedList_succAboveEmb_eraseIdx_toFinset (c : ContractionsNat n) (i : Fin n.succ) (k : ℕ)
      (hk : k < c.uncontractedList.length) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k).toFinset =
    (c.uncontracted.map i.succAboveEmb).erase (i.succAboveEmb c.uncontractedList[k]) := by
  ext a
  simp
  rw [mem_eraseIdx_nodup _ _ _ (by simpa using hk)]
  simp_all only [List.mem_map, List.getElem_map, ne_eq]
  apply Iff.intro
  · intro a_1
    simp_all only [not_false_eq_true, true_and]
    obtain ⟨left, right⟩ := a_1
    obtain ⟨w, h⟩ := left
    obtain ⟨left, right_1⟩ := h
    subst right_1
    use w
    simp_all [uncontractedList]
  · intro a_1
    simp_all only [not_false_eq_true, and_true]
    obtain ⟨left, right⟩ := a_1
    obtain ⟨w, h⟩ := right
    obtain ⟨left_1, right⟩ := h
    subst right
    use w
    simp_all [uncontractedList]
  exact uncontractedList_succAboveEmb_nodup c i

lemma uncontractedList_succAboveEmb_eraseIdx_eq_sort (c : ContractionsNat n) (i : Fin n.succ) (k : ℕ)
      (hk : k < c.uncontractedList.length) :
    ((List.map i.succAboveEmb c.uncontractedList).eraseIdx k) =
    ((c.uncontracted.map i.succAboveEmb).erase (i.succAboveEmb c.uncontractedList[k])).sort (· ≤ ·) := by
  rw [← uncontractedList_succAboveEmb_eraseIdx_toFinset]
  symm
  refine (List.toFinset_sort (α := Fin n.succ) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_succAboveEmb_eraseIdx_nodup c i k
  · exact uncontractedList_succAboveEmb_eraseIdx_sorted c i k

lemma uncontractedList_succAbove_orderedInsert_sorted (c : ContractionsNat n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).Sorted (· ≤ ·) := by
  refine List.Sorted.orderedInsert i (List.map (⇑i.succAboveEmb) c.uncontractedList) ?_
  exact uncontractedList_succAboveEmb_sorted c i

lemma uncontractedList_succAbove_orderedInsert_nodup (c : ContractionsNat n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).Nodup := by
  have h1 : (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).Perm
    (i :: List.map i.succAboveEmb c.uncontractedList) := by
    exact List.perm_orderedInsert (fun x1 x2 => x1 ≤ x2) i _
  apply List.Perm.nodup h1.symm
  simp only [Nat.succ_eq_add_one, List.nodup_cons, List.mem_map, not_exists,
    not_and]
  apply And.intro
  · intro x _
    exact Fin.succAbove_ne i x
  · exact uncontractedList_succAboveEmb_nodup c i

lemma uncontractedList_succAbove_orderedInsert_toFinset (c : ContractionsNat n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)).toFinset =
    (Insert.insert i (Finset.map i.succAboveEmb c.uncontracted)) := by
  ext a
  simp
  rw [← uncontractedList_toFinset]
  simp

lemma uncontractedList_succAbove_orderedInsert_eq_sort (c : ContractionsNat n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)) =
    (Insert.insert i (Finset.map i.succAboveEmb c.uncontracted)).sort (· ≤ ·) := by
  rw [← uncontractedList_succAbove_orderedInsert_toFinset]
  symm
  refine (List.toFinset_sort (α := Fin n.succ) (· ≤ ·) ?_).mpr ?_
  · exact uncontractedList_succAbove_orderedInsert_nodup c i
  · exact uncontractedList_succAbove_orderedInsert_sorted c i

lemma uncontractedList_extractEquiv_symm_none (c : ContractionsNat n) (i : Fin n.succ) :
    ((extractEquiv i).symm ⟨c, none⟩).uncontractedList =
    List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList) := by
  rw [uncontractedList_eq_sort, extractEquiv_symm_none_uncontracted]
  rw [uncontractedList_succAbove_orderedInsert_eq_sort]




lemma fin_list_sorted_split  :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·))  →  (i : ℕ) →
    l = l.filter (fun x => x.1 < i) ++ l.filter (fun x => i ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp at hl
    by_cases ha : a < i
    · conv_lhs => rw [fin_list_sorted_split l hl.2 i]
      rw [← List.cons_append]
      rw [List.filter_cons_of_pos, List.filter_cons_of_neg]
      simp [ha]
      simp [ha]
    · have hx :  List.filter (fun x => decide (x.1 < i)) (a :: l) = [] := by
        simp [ha]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp [hx]
      rw [List.filter_cons_of_pos]
      simp
      have hl' := fin_list_sorted_split l hl.2 i
      have hx :  List.filter (fun x => decide (x.1 < i)) (l) = [] := by
        simp [ha]
        intro b hb
        have hb' := hl.1 b hb
        omega
      simp [hx] at hl'
      conv_lhs => rw [hl']
      simp [ha]
      omega

lemma orderedInsert_of_fin_list_sorted  :
    (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·))  →  (i : Fin n) →
    List.orderedInsert (· ≤ ·) i l = l.filter (fun x => x.1 < i.1) ++ i :: l.filter (fun x => i.1 ≤ x.1)
  | [], _, _ => by simp
  | a :: l, hl, i => by
    simp at hl
    by_cases ha : i ≤ a
    · simp [ha]
      have h1 : List.filter (fun x => decide (↑x < ↑i)) l  = [] := by
        simp
        intro a ha
        have ha' := hl.1 a ha
        omega
      have hl : l = List.filter (fun x => decide (i ≤ x)) l := by
        conv_lhs => rw [fin_list_sorted_split l hl.2 i]
        simp [h1]
      simp [← hl, h1]
    · simp [ha]
      rw [List.filter_cons_of_pos]
      rw [orderedInsert_of_fin_list_sorted l hl.2 i]
      simp
      simp
      omega

lemma orderedInsert_eq_insertIdx_of_fin_list_sorted  :  (l : List (Fin n)) → (hl : l.Sorted (· ≤ ·))  →  (i : Fin n) →
    List.orderedInsert (· ≤ ·) i l = l.insertIdx (l.filter (fun x => x.1 < i.1)).length i := by
  intro l hl i
  let n : Fin l.length.succ := ⟨(List.filter (fun x => decide (x < i)) l).length, by
    have h1 := l.length_filter_le (fun x => x.1 < i.1)
    simp at h1
    omega⟩
  simp
  conv_rhs => rw [insertIdx_eq_take_drop _ _ n]
  rw [orderedInsert_of_fin_list_sorted]
  congr
  · conv_rhs =>
      rhs
      rw [fin_list_sorted_split l  hl i]
    simp [n]
  · conv_rhs =>
      rhs
      rw [fin_list_sorted_split l  hl i]
    simp [n]
  exact hl


def uncontractedListOrderPos (c : ContractionsNat n)  (i : Fin n.succ) : ℕ :=
  (List.filter (fun x => x.1 < i.1) c.uncontractedList).length

@[simp]
lemma uncontractedListOrderPos_lt_length_add_one (c : ContractionsNat n) (i : Fin n.succ) :
    c.uncontractedListOrderPos i < c.uncontractedList.length + 1 := by
  simp [uncontractedListOrderPos]
  have h1 := c.uncontractedList.length_filter_le (fun x => x.1 < i.1)
  omega

lemma take_uncontractedListOrderPos_eq_filter (c : ContractionsNat n) (i : Fin n.succ) :
    (c.uncontractedList.take (c.uncontractedListOrderPos i)) =
    c.uncontractedList.filter (fun x => x.1 < i.1) := by
  nth_rewrite 1 [fin_list_sorted_split c.uncontractedList _ i]
  simp [uncontractedListOrderPos]
  exact uncontractedList_sorted c


lemma take_uncontractedListOrderPos_eq_filter_sort (c : ContractionsNat n) (i : Fin n.succ) :
    (c.uncontractedList.take (c.uncontractedListOrderPos i)) =
    (c.uncontracted.filter (fun x => x.1 < i.1)).sort (· ≤ ·) := by
  rw [take_uncontractedListOrderPos_eq_filter]
  have h1 : (c.uncontractedList.filter (fun x => x.1 < i.1)).Sorted (· ≤ ·) := by
    apply List.Sorted.filter
    exact uncontractedList_sorted c
  have h2 : (c.uncontractedList.filter (fun x => x.1 < i.1)).Nodup := by
    refine List.Nodup.filter _ ?_
    exact uncontractedList_nodup c
  have h3 : (c.uncontractedList.filter (fun x => x.1 < i.1)).toFinset =
    (c.uncontracted.filter (fun x => x.1 < i.1)) := by
    rw [uncontractedList_eq_sort]
    simp
  rw [← h3]
  exact ((List.toFinset_sort (α := Fin n) (· ≤ ·) h2).mpr h1).symm

lemma orderedInsert_succAboveEmb_uncontractedList_eq_insertIdx (c : ContractionsNat n) (i : Fin n.succ) :
    (List.orderedInsert (· ≤ ·) i (List.map i.succAboveEmb c.uncontractedList)) =
    (List.map i.succAboveEmb c.uncontractedList).insertIdx (uncontractedListOrderPos c i) i := by
  rw [orderedInsert_eq_insertIdx_of_fin_list_sorted]
  swap
  exact uncontractedList_succAboveEmb_sorted c i
  congr 1
  simp [uncontractedListOrderPos]
  rw [List.filter_map]
  simp
  congr
  funext x
  simp [Fin.succAbove]
  split
  simp [Fin.lt_def]
  rename_i h
  simp_all [Fin.lt_def]
  omega

def uncontractedFinEquiv (c : ContractionsNat n) :
    Fin (c.uncontractedList).length ≃ c.uncontracted where
  toFun i := ⟨c.uncontractedList.get i, c.uncontractedList_get_mem_uncontracted i⟩
  invFun i := ⟨List.indexOf i.1 c.uncontractedList,
    List.indexOf_lt_length.mpr ((c.uncontractedList_mem_iff i.1).mpr i.2)⟩
  left_inv i := by
    ext
    exact List.get_indexOf (uncontractedList_nodup c) _
  right_inv i := by
    ext
    simp

@[simp]
lemma uncontractedList_getElem_uncontractedFinEquiv_symm (k : c.uncontracted) :
    c.uncontractedList[(c.uncontractedFinEquiv.symm k).val] = k := by
  simp [uncontractedFinEquiv]

def uncontractedStatesEquiv (φs : List 𝓕.States) (c : ContractionsNat φs.length) :
   Option c.uncontracted ≃ Option (Fin (c.uncontractedList.map φs.get).length):=
  Equiv.optionCongr (c.uncontractedFinEquiv.symm.trans (finCongr (by simp)))

@[simp]
lemma uncontractedStatesEquiv_none (φs : List 𝓕.States) (c : ContractionsNat φs.length) :
    (uncontractedStatesEquiv φs c).toFun none = none := by
  simp [uncontractedStatesEquiv]

lemma uncontractedStatesEquiv_list_sum [AddCommMonoid α] (φs : List 𝓕.States)
  (c : ContractionsNat φs.length) (f : Option (Fin (c.uncontractedList.map φs.get).length) → α) :
    ∑ (i : Option (Fin (c.uncontractedList.map φs.get).length)), f i =
    ∑ (i : Option c.uncontracted), f (c.uncontractedStatesEquiv φs i) := by
  rw [(c.uncontractedStatesEquiv φs).sum_comp]

lemma uncontractedStatesEquiv_take (φs : List 𝓕.States) (c : ContractionsNat φs.length) (i : ℕ) :
    (c.uncontractedList.map φs.val) (c.uncontractedStatesEquiv φs ) =
    some (Fin.cast (List.length_map φs.get) (c.uncontractedList.take i).length) := by
  sorry

lemma uncontractedList_extractEquiv_symm_some (c : ContractionsNat n) (i : Fin n.succ)
  (k : c.uncontracted) :
    ((extractEquiv i).symm ⟨c, some k⟩).uncontractedList =
   ((c.uncontractedList).map i.succAboveEmb).eraseIdx (c.uncontractedFinEquiv.symm k) := by
  rw [uncontractedList_eq_sort]
  rw [uncontractedList_succAboveEmb_eraseIdx_eq_sort]
  swap
  simp
  congr
  simp [extractEquiv]
  rw [insert_some_uncontracted]
  ext a
  simp


end ContractionsNat

end FieldStruct
