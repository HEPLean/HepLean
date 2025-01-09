/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.OperatorAlgebra
import HepLean.PerturbationTheory.Wick.Signs.KoszulSign
import Mathlib.Data.Fintype.Basic
/-!

# Contractions


-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

def ContractionsNat (n : ℕ) : Type :=
  {f : Finset ((Finset (Fin n))) // (∀ a ∈ f, a.card = 2) ∧
    (∀ a ∈ f, ∀ b ∈ f, ∀ x (_ : x ∈ a) (_ : x ∈ b), a = b)}

namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)

local instance : IsTotal (Fin n × Fin n) (fun a b => a.1 ≤ b.1) where
  total := by
    intro a b
    exact le_total a.1 b.1

local instance : IsTrans (Fin n × Fin n) (fun a b => a.1 ≤ b.1) where
  trans := by
    intro a b c ha hb
    exact Fin.le_trans ha hb

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
    have hc := c.2.2 _ h _ hk i (by simp) (by simp)
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
  · intro a ha b hb x hxa hxb
    simp at ha hb
    apply (Finset.map_injective i.succAboveEmb)
    refine c.2.2 _ ha _ hb (i.succAbove x) ?_ ?_
    · simp
      use x
    · simp
      use x

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
      have hc := c.2.2 _ h _ hn (i.succAbove j) (by simp) (by simp)
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
  · intro a ha b hb x hxa hxb
    simp [f'] at ha hb
    match j with
    | none =>
      simp_all [f]
      obtain ⟨a', ha', ha''⟩ := ha
      obtain ⟨b', hb', hb''⟩ := hb
      subst ha''
      subst hb''
      simp
      rw [Finset.mapEmbedding_apply] at hxa hxb
      simp at hxa hxb
      obtain ⟨x', hxa', hxa''⟩ := hxa
      obtain ⟨x'', hxb', hxb''⟩ := hxb
      have hx : x' = x'' := by
        subst hxa''
        exact Fin.succAbove_right_inj.mp (id (Eq.symm hxb''))
      subst hx
      exact c.2.2 a' ha' b' hb' x' hxa' hxb'
    | some j =>
      simp_all
      rcases ha with ha | ha <;>
        rcases hb with hb | hb
      · rw [ha, hb]
      · subst ha
        simp at hxa
        rcases hxa with hxa | hxa
        · subst hxa
          simp [f] at hb
          obtain ⟨a', hb', hb''⟩ := hb
          rw [Finset.mapEmbedding_apply] at hb''
          subst hb''
          simp at hxb
          obtain ⟨a, _, ha⟩ := hxb
          exact False.elim (Fin.succAbove_ne x a ha)
        · subst hxa
          simp [f] at hb
          obtain ⟨a', hb', hb''⟩ := hb
          rw [Finset.mapEmbedding_apply] at hb''
          subst hb''
          simp at hxb
          obtain ⟨a, ha2, ha⟩ := hxb
          have hx : a = j := by exact Fin.succAbove_right_inj.mp ha
          subst hx
          exact False.elim (((c.mem_uncontracted_iff_not_contracted j.1).mp j.2) a' hb' ha2)
      · subst hb
        simp at hxb
        rcases hxb with hxb | hxb
        · subst hxb
          simp [f] at ha
          obtain ⟨a', ha', ha''⟩ := ha
          rw [Finset.mapEmbedding_apply] at ha''
          subst ha''
          simp at hxa
          obtain ⟨a, _, ha⟩ := hxa
          exact False.elim (Fin.succAbove_ne x a ha)
        · subst hxb
          simp [f] at ha
          obtain ⟨a', ha', ha''⟩ := ha
          rw [Finset.mapEmbedding_apply] at ha''
          subst ha''
          simp at hxa
          obtain ⟨a, ha2, ha⟩ := hxa
          have hx : a = j := by exact Fin.succAbove_right_inj.mp ha
          subst hx
          exact False.elim (((c.mem_uncontracted_iff_not_contracted j.1).mp j.2) a' ha' ha2)
      · /- Same as the proof in the none case. -/
        simp_all [f]
        obtain ⟨a', ha', ha''⟩ := ha
        obtain ⟨b', hb', hb''⟩ := hb
        subst ha''
        subst hb''
        simp
        rw [Finset.mapEmbedding_apply] at hxa hxb
        simp at hxa hxb
        obtain ⟨x', hxa', hxa''⟩ := hxa
        obtain ⟨x'', hxb', hxb''⟩ := hxb
        have hx : x' = x'' := by
          subst hxa''
          exact Fin.succAbove_right_inj.mp (id (Eq.symm hxb''))
        subst hx
        exact c.2.2 a' ha' b' hb' x' hxa' hxb'

lemma insert_of_isSome (c : ContractionsNat n) (i : Fin n.succ) (j : Option c.uncontracted) (hj : j.isSome) :
    (insert c i j).1 = Insert.insert {i, i.succAbove (j.get hj)}
    (Finset.map (Finset.mapEmbedding i.succAboveEmb).toEmbedding c.1) := by
  simp [insert]
  rw [@Option.isSome_iff_exists] at hj
  obtain ⟨j, hj⟩ := hj
  subst hj
  simp

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

def getDualErase (c : ContractionsNat n.succ.succ) (i : Fin n.succ.succ) :
    Option ((erase c i).uncontracted) := by
  refine if hj : (c.getDual? i).isSome then some ⟨(predAboveI i ((c.getDual? i).get hj)), ?_⟩
    else none
  rw [mem_erase_uncontracted_iff]
  apply Or.inr
  rw [succsAbove_predAboveI, getDual?_eq_some_iff_mem]
  · simp
  · apply c.getDual?_eq_some_neq _ _ _
    simp


@[simp]
lemma getDualErase_isSome_iff_getDual?_isSome (c : ContractionsNat n.succ.succ) (i : Fin n.succ.succ) :
     (c.getDualErase i).isSome ↔ (c.getDual? i).isSome := by
  simp [getDualErase]


@[simp]
lemma erase_insert (c : ContractionsNat n.succ.succ) (i : Fin n.succ.succ) :
    insert (erase c i) i (getDualErase c i) = c := by
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


def length (l : ContractionsNat n) : ℕ := l.val.length

def fstPart : List (Fin n) := (List.unzip c.1).1

lemma fstPart_nodup : c.fstPart.Nodup := by
  have h1 := c.2.2.2
  rw [List.nodup_append] at h1
  exact h1.1

lemma fstPart_length : c.fstPart.length = c.1.length := by
  simp [fstPart]

lemma fstPart_length_le : c.fstPart.length ≤ n := by
  rw [fstPart_length]
  have h1 := List.Nodup.length_le_card c.fstPart_nodup
  simpa [fstPart] using h1

def sndPart : List (Fin n) := (List.unzip c.1).2

lemma sndPart_nodup : c.sndPart.Nodup := by
  have h1 := c.2.2.2
  rw [List.nodup_append] at h1
  exact h1.2.1

lemma fstPart_disjoint_sndPart : c.fstPart.Disjoint c.sndPart := by
  have h1 := c.2.2.2
  rw [List.nodup_append] at h1
  exact h1.2.2

def flatten : List (Fin n) := c.fstPart ++ c.sndPart

lemma eq_zip_fstPart_sndPart : c.1 = (c.fstPart.zip c.sndPart) := by
  simp only [fstPart,  sndPart]
  rw [List.zip_unzip]

lemma fstPart_sorted : c.fstPart.Sorted (· ≤ ·) := by
  have h1 := c.2.2.1
  have hl (l : List (Fin n × Fin n)) (h : l.Sorted (fun a b => a.1 ≤ b.1)) :
    (List.unzip l).1.Sorted (· ≤ ·) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp [List.unzip]
      simp at h
      apply And.intro
      · intro b x
        exact h.1 b x
      · simpa using ih h.2
  exact hl c.1 h1


lemma length_lt (l : ContractionsNat n) : l.val.length ≤ n := by
  rw [← fstPart_length]
  exact fstPart_length_le l

def unconstrainedList : List (Fin n) :=
  (List.finRange n).filter (fun i => i ∉ c.flatten)

lemma mem_unconstrainedList_not_fst {i : Fin n} (hi : i ∈ c.unconstrainedList) :
    ∀ x, (i, x) ∉ c.1:= by
  simp [unconstrainedList, flatten] at hi
  by_contra hx
  simp at hx
  obtain ⟨x, hx⟩ := hx
  simp [fstPart] at hi
  exact hi.1 x hx

lemma mem_unconstrainedList_not_snd {i : Fin n} (hi : i ∈ c.unconstrainedList) :
    ∀ x, (x, i) ∉ c.1:= by
  simp [unconstrainedList, flatten] at hi
  by_contra hx
  simp at hx
  obtain ⟨x, hx⟩ := hx
  simp [sndPart] at hi
  exact hi.2 x hx

def unconstrainedMap : Fin c.unconstrainedList.length → Fin n :=
  c.unconstrainedList.get


lemma eq_of_mem_fst_eq {x y : Fin n × Fin n} (hi : x.1 = y.1) (hx : x ∈ c.1) (hy : y ∈ c.1) :
    x = y := by
  sorry

lemma eq_of_mem_snd_eq {x y : Fin n × Fin n} (hi : x.2 = y.2) (hx : x ∈ c.1) (hy : y ∈ c.1) :
    x = y := by
  sorry
/-!

## getContrPartner

-/

def getContrPartner (i : Fin n) : Option (Fin n) :=
  let x1 := Option.map Prod.snd (c.1.find? (fun x => x.1 = i))
  let x2 := Option.map Prod.fst (c.1.find? (fun x => x.2 = i))
  Option.or x1 x2

lemma getContrPartner_eq_some_of_fst_mem (i j : Fin n) (h : (i, j) ∈ c.1) :
    c.getContrPartner i = some j := by
  simp [getContrPartner]
  apply Or.inl
  use i
  have hx : (List.find? (fun x => decide (x.1 = i)) c.1).isSome := by
    rw [List.find?_isSome]
    use (i , j)
    simp
    exact h
  have hx1 : ∃ x, (List.find? (fun x => decide (x.1 = i)) c.1) = some x := by
    exact Option.isSome_iff_exists.mp hx
  obtain ⟨x, hx1⟩ := hx1
  have hx2 : x.1 = i := by
    rw [@List.find?_eq_some_iff_getElem] at hx1
    simpa using hx1.1
  rw [hx1]
  simp
  apply eq_of_mem_fst_eq c
  simp [hx2]
  exact List.mem_of_find?_eq_some hx1
  exact h

lemma getContrPartner_eq_some_of_snd_mem (i j : Fin n) (h : (i, j) ∈ c.1) :
    c.getContrPartner j = some i := by
  simp [getContrPartner]
  sorry


/-!

## inserting and erasing contractions

-/

def insertContrList (i j : Fin n) : List (Fin n × Fin n) :=
  if i < j then
  List.orderedInsert (fun a b => a.1 ≤ b.1) (i, j) c.1
  else
  List.orderedInsert (fun a b => a.1 ≤ b.1) (j, i) c.1

lemma insertContrList_pairwise_ordered {i j : Fin n} {k : Fin n × Fin n} (hij : i ≠ j)
    (hk : k ∈ c.insertContrList i j) : k.1 < k.2 := by
  simp [insertContrList] at hk
  split at hk
  · simp at hk
    rcases hk with hk | hk
    · subst hk
      simp_all
    · apply c.2.1
      exact hk
  · simp at hk
    rcases hk with hk | hk
    · subst hk
      simp_all
      rename_i hn
      exact lt_of_le_of_ne hn fun a => hij (id (Eq.symm a))
    · apply c.2.1
      exact hk

lemma insertContrList_sorted (i j : Fin n) :
    (c.insertContrList i j).Sorted (fun a b => a.1 ≤ b.1) := by
  rw [insertContrList]
  split
  · apply List.Sorted.orderedInsert
    exact c.2.2.1
  · apply List.Sorted.orderedInsert
    exact c.2.2.1

lemma insertContrList_nodup_fst {i j : Fin n} (hi : i ∈ c.unconstrainedList)
    (hj : j ∈ c.unconstrainedList) : ((List.unzip (c.insertContrList i j)).1).Nodup := by
  simp [insertContrList]
  split
  · have h1 :  (List.map Prod.fst (List.orderedInsert (fun a b => a.1 ≤ b.1) (i, j) c.1)).Perm
      (List.map Prod.fst ((i,j)::c.1)) := by
      refine List.Perm.map Prod.fst ?p
      exact List.perm_orderedInsert (fun a b => a.1 ≤ b.1) (i, j) c.1
    apply List.Perm.nodup h1.symm
    simp
    apply And.intro
    · intro x
      exact mem_unconstrainedList_not_fst c hi x
    · simpa [fstPart] using c.fstPart_nodup
  · have h1 :  (List.map Prod.fst (List.orderedInsert (fun a b => a.1 ≤ b.1) (j, i) c.1)).Perm
      (List.map Prod.fst ((j,i)::c.1)) := by
      refine List.Perm.map Prod.fst ?_
      exact List.perm_orderedInsert (fun a b => a.1 ≤ b.1) (j, i) c.1
    apply List.Perm.nodup h1.symm
    simp
    apply And.intro
    · intro x
      exact mem_unconstrainedList_not_fst c hj x
    · simpa [fstPart] using c.fstPart_nodup

lemma insertContrList_nodup_snd {i j : Fin n} (hi : i ∈ c.unconstrainedList)
    (hj : j ∈ c.unconstrainedList) : ((List.unzip (c.insertContrList i j)).2).Nodup := by
  simp [insertContrList]
  split
  · have h1 :  (List.map Prod.snd (List.orderedInsert (fun a b => a.1 ≤ b.1) (i, j) c.1)).Perm
      (List.map Prod.snd ((i,j)::c.1)) := by
      refine List.Perm.map Prod.snd ?p
      exact List.perm_orderedInsert (fun a b => a.1 ≤ b.1) (i, j) c.1
    apply List.Perm.nodup h1.symm
    simp
    apply And.intro
    · intro x
      exact mem_unconstrainedList_not_snd c hj x
    · simpa [sndPart] using c.sndPart_nodup
  · have h1 :  (List.map Prod.snd (List.orderedInsert (fun a b => a.1 ≤ b.1) (j, i) c.1)).Perm
      (List.map Prod.snd ((j,i)::c.1)) := by
      refine List.Perm.map Prod.snd ?_
      exact List.perm_orderedInsert (fun a b => a.1 ≤ b.1) (j, i) c.1
    apply List.Perm.nodup h1.symm
    simp
    apply And.intro
    · intro x
      exact mem_unconstrainedList_not_snd c hi x
    · simpa [sndPart] using c.sndPart_nodup

lemma insertContrList_fst_disjoint_snd {i j : Fin n} (hij : i ≠ j) (hi : i ∈ c.unconstrainedList)
    (hj : j ∈ c.unconstrainedList) : ((List.unzip (c.insertContrList i j)).1).Disjoint
    ((List.unzip (c.insertContrList i j)).2) := by
  simp [insertContrList]
  have h1 {i j : Fin n}:  (List.map Prod.fst (List.orderedInsert (fun a b => a.1 ≤ b.1) (i, j) c.1)).Perm
      (List.map Prod.fst ((i,j)::c.1)) := by
      refine List.Perm.map Prod.fst ?_
      exact List.perm_orderedInsert (fun a b => a.1 ≤ b.1) (i, j) c.1
  have h2 {i j : Fin n} :  (List.map Prod.snd (List.orderedInsert (fun a b => a.1 ≤ b.1) (i, j) c.1)).Perm
      (List.map Prod.snd ((i,j)::c.1)) := by
      refine List.Perm.map Prod.snd ?_
      exact List.perm_orderedInsert (fun a b => a.1 ≤ b.1) (i, j) c.1
  split
  · apply (List.Perm.disjoint_left h1.symm).mp
    apply (List.Perm.disjoint_right h2.symm).mp
    simp
    apply And.intro
    · apply And.intro (id (Ne.symm hij))
      exact fun x => mem_unconstrainedList_not_fst c hj x
    · apply And.intro
      · exact fun x => mem_unconstrainedList_not_snd c hi x
      · simpa [fstPart, sndPart] using c.fstPart_disjoint_sndPart
  · apply (List.Perm.disjoint_left h1.symm).mp
    apply (List.Perm.disjoint_right h2.symm).mp
    simp
    apply And.intro
    · apply And.intro hij
      exact fun x => mem_unconstrainedList_not_fst c hi x
    · apply And.intro
      · exact fun x => mem_unconstrainedList_not_snd c hj x
      · simpa [fstPart, sndPart] using c.fstPart_disjoint_sndPart

lemma insertContrList_nodup {i j : Fin n} (hij : i ≠ j) (hi : i ∈ c.unconstrainedList)
    (hj : j ∈ c.unconstrainedList) :
    ((List.unzip (c.insertContrList i j)).1 ++ (List.unzip (c.insertContrList i j)).2).Nodup := by
  rw [List.nodup_append]
  apply And.intro
  · exact insertContrList_nodup_fst c hi hj
  · apply And.intro
    · exact insertContrList_nodup_snd c hi hj
    · exact insertContrList_fst_disjoint_snd c hij hi hj

def insertContr (i j : Fin n) (hij : i ≠ j) (hi : i ∈ c.unconstrainedList)
    (hj : j ∈ c.unconstrainedList) : ContractionsNat n :=
  ⟨c.insertContrList i j, fun _ => c.insertContrList_pairwise_ordered hij,
    c.insertContrList_sorted i j, c.insertContrList_nodup hij hi hj⟩

lemma insertContr_symm (i j : Fin n) (hij : i ≠ j) (hi : i ∈ c.unconstrainedList)
    (hj : j ∈ c.unconstrainedList) :
    (c.insertContr i j hij hi hj) = (c.insertContr j i (Ne.symm hij) hj hi) := by
  simp [insertContr]
  apply Subtype.eq
  simp [insertContrList]
  split_ifs
  · omega
  · rfl
  · rfl
  · omega

lemma insertContr_mem {i j : Fin n} (hij : i ≠ j) (hi : i ∈ c.unconstrainedList)
    (hj : j ∈ c.unconstrainedList) :
    (i, j) ∈ (c.insertContr i j hij hi hj).1 ∨ (j, i) ∈ (c.insertContr i j hij hi hj).1 := by
  simp [insertContr, insertContrList]
  split
  simp
  simp

/-!

## Erasing a contraction

-/
def eraseContrList (i : Fin n) : List (Fin n × Fin n) :=
  c.1.filter (fun x => x.1 ≠ i ∧ x.2 ≠ i)

lemma eraseContrList_pairwise_ordered {i : Fin n} {j : Fin n × Fin n}
    (hj : j ∈ c.eraseContrList i) : j.1 < j.2 := by
  simp [eraseContrList] at hj
  exact c.2.1 j hj.1

lemma eraseContrList_sorted (i : Fin n) :
    (c.eraseContrList i).Sorted (fun a b => a.1 ≤ b.1) := by
  simp [eraseContrList]
  apply List.Sorted.filter
  exact c.2.2.1

lemma filter_map_nodup (l : List α) (f : α → β) (h : (List.map f l).Nodup) (p : α → Bool) :
    ((List.map f (l.filter p)).Nodup) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    by_cases hp : p i
    · rw [List.filter_cons_of_pos hp]
      simp
      apply And.intro
      · intro x hx hf
        simp at h
        exact h.1 x hx
      · simp at h
        exact ih h.2
    · rw [List.filter_cons_of_neg hp]
      simp at h
      exact ih h.2


lemma filter_map_disjoint (l1 l2 : List α) (f1 f2 : α → β) (h : (List.map f1 l1).Disjoint (List.map f2 l2)) (p : α → Bool) :
    ((List.map f1 (l1.filter p)).Disjoint (List.map f2 (l2.filter p))) := by
  induction l1 with
  | nil => simp
  | cons i l ih =>
    by_cases hp : p i
    · rw [List.filter_cons_of_pos hp]
      simp
      apply And.intro
      · intro x hx hf
        simp at h
        exact h.1 x hx
      · simp at h
        exact ih h.2
    · rw [List.filter_cons_of_neg hp]
      simp at h
      exact ih h.2

lemma eraseContrList_nodup (i : Fin n) :
    ((List.unzip (c.eraseContrList i)).1 ++ (List.unzip (c.eraseContrList i)).2).Nodup := by
  rw [List.nodup_append]
  apply And.intro
  · simp [eraseContrList]
    have h1 := c.fstPart_nodup
    simp [fstPart] at h1
    apply filter_map_nodup
    exact h1
  · apply And.intro
    · simp [eraseContrList]
      have h1 := c.sndPart_nodup
      simp [sndPart] at h1
      apply filter_map_nodup
      exact h1
    · simp [eraseContrList]
      apply filter_map_disjoint
      simpa [fstPart, sndPart] using c.fstPart_disjoint_sndPart

def eraseContr (i : Fin n) : ContractionsNat n :=
  ⟨c.eraseContrList i, fun _ => c.eraseContrList_pairwise_ordered,
    c.eraseContrList_sorted i, c.eraseContrList_nodup i⟩

/-!

## succAbove
-/
def succAboveList (m : Fin n.succ) : List (Fin n.succ × Fin n.succ) :=
  List.map (fun (a, b) => (m.succAbove a, m.succAbove b)) c.1

lemma succAboveList_pairwise_ordered {i : Fin n.succ × Fin n.succ}
    {m : Fin n.succ} (hi : i ∈ c.succAboveList m) :
    i.1 < i.2 := by
  simp [succAboveList] at hi
  obtain ⟨a, b, hab1, hab2⟩ := hi
  subst hab2
  simp
  refine Fin.succAbove_lt_succAbove_iff.mpr ?_
  exact c.2.1 ⟨a, b⟩ hab1

lemma succAboveList_sorted {m : Fin n.succ} :
    (c.succAboveList m).Sorted (fun a b => a.1 ≤ b.1) := by
  have hl (l : List (Fin n × Fin n)) (hl : l.Sorted (fun a b => a.1 ≤ b.1)) :
    (List.map (fun (a, b) => (m.succAbove a, m.succAbove b)) l).Sorted (fun a b => a.1 ≤ b.1) := by
    induction l with
    | nil => simp
    | cons a l ih =>
      simp
      simp at hl
      apply And.intro
      · intro x b c d h1 h2 h3
        subst h2
        apply Fin.succAbove_le_succAbove_iff.mpr (hl.1 c d h1)
      · exact ih hl.2
  exact hl c.1 c.2.2.1

lemma succAboveList_nodup {m : Fin n.succ} :
    ((List.unzip (c.succAboveList m)).1 ++ (List.unzip (c.succAboveList m)).2).Nodup := by
  rw [@List.nodup_append]
  simp [succAboveList]
  have h1 : (List.map (Prod.fst ∘ fun x => (m.succAbove x.1, m.succAbove x.2)) c.1)
        = List.map m.succAbove c.fstPart := by
      simp [fstPart]
  rw [h1]
  have h2 : (List.map (Prod.snd ∘ fun x => (m.succAbove x.1, m.succAbove x.2)) c.1)
        = List.map m.succAbove c.sndPart := by
      simp [sndPart]
  rw [h2]
  apply And.intro
  · apply List.Nodup.map
    exact Fin.succAbove_right_injective
    exact fstPart_nodup c
  · apply And.intro
    · apply List.Nodup.map
      exact Fin.succAbove_right_injective
      exact sndPart_nodup c
    · apply List.disjoint_map
      exact Fin.succAbove_right_injective
      exact fstPart_disjoint_sndPart c

/-- Adds `m` with no contractions. -/
def succAbove (m : Fin n.succ) : ContractionsNat n.succ :=
  ⟨c.succAboveList m, fun _ => c.succAboveList_pairwise_ordered,
    c.succAboveList_sorted, c.succAboveList_nodup⟩

def succAboveContrList (m : Fin n.succ) (i : Fin c.unconstrainedList.length) :
    List (Fin n.succ × Fin n.succ) :=
  if  m.succAbove (c.unconstrainedMap i) < m then
    List.orderedInsert (fun a b => a.1 ≤ b.1) (m.succAbove (c.unconstrainedMap i), m)
      (succAboveList c m)
  else
    List.orderedInsert (fun a b => a.1 ≤ b.1) (m, m.succAbove (c.unconstrainedMap i))
      (succAboveList c m)

lemma succAboveContrList_pairwise_ordered {m : Fin n.succ} {i : Fin c.unconstrainedList.length}
    {j : Fin n.succ × Fin n.succ} (hj : j ∈ c.succAboveContrList m i) :
    j.1 < j.2 := by
  simp [succAboveContrList] at hj
  split at hj
  · rename_i hi
    simp at hj
    rcases hj with hj | hj
    · subst hj
      exact hi
    · exact c.succAboveList_pairwise_ordered hj
  · rename_i hi
    simp at hj
    rcases hj with hj | hj
    · subst hj
      simp
      simp at hi
      exact lt_of_le_of_ne hi (Fin.ne_succAbove m (c.unconstrainedMap i))
    · exact c.succAboveList_pairwise_ordered hj

lemma succAboveContrList_sorted {m : Fin n.succ} {i : Fin c.unconstrainedList.length} :
    (c.succAboveContrList m i).Sorted (fun a b => a.1 ≤ b.1) := by
  rw [succAboveContrList]
  split
  · apply List.Sorted.orderedInsert
    exact succAboveList_sorted c
  · apply List.Sorted.orderedInsert
    exact succAboveList_sorted c

lemma succAboveContrList_nodup_fst {m : Fin n.succ} {i : Fin c.unconstrainedList.length} :
    ((List.unzip (c.succAboveContrList m i)).1).Nodup := by
  rw [succAboveContrList]
  split
  simp
  have h1 : ((List.map Prod.fst
    (List.orderedInsert (fun a b => a.1 ≤ b.1) (m.succAbove (c.unconstrainedMap i), m) (c.succAboveList m)))).Perm
    (List.map Prod.fst ((m.succAbove (c.unconstrainedMap i), m) :: c.succAboveList m)) := by
    refine List.Perm.map Prod.fst ?p
    exact List.perm_orderedInsert _ _ _
  apply List.Perm.nodup h1.symm
  simp
  apply And.intro
  · intro x
    sorry
  · have hi := c.succAboveList_nodup (m := m)
    simp [List.nodup_append] at hi
    exact hi.1

section predAboveI

open HepLean.Fin
variable {n : ℕ} (c : ContractionsNat n.succ.succ)

def predAboveIList (m : Fin n.succ.succ) : List (Fin n.succ × Fin n.succ) :=
  List.map (fun (a, b) => (predAboveI m a, predAboveI m b))
  (List.filter (fun (a, b) => a.1 ≠ m ∧ b.1 ≠ m) c.1)


end predAboveI
end ContractionsNat

end FieldStruct
