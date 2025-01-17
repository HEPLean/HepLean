/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.NormalOrder
import HepLean.Mathematics.List.InsertIdx
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

/-- The contraction consisting of no contracted pairs. -/
def nil : ContractionsNat n := ⟨∅, by simp, by simp⟩

def congr : {n m : ℕ} → (h : n = m) → ContractionsNat n ≃ ContractionsNat m
  | n, .(n), rfl => Equiv.refl _

@[simp]
lemma congr_refl : c.congr rfl = c := by
  cases c
  rfl


lemma congr_contractions {n m : ℕ} (h : n = m) (c : ContractionsNat n) :
    ((congr h) c).1 = Finset.map (Finset.mapEmbedding (finCongr h)).toEmbedding c.1 := by
  subst h
  simp
  ext a
  apply Iff.intro
  · intro ha
    simp
    use a
    simp [ha]
    rw [Finset.mapEmbedding_apply]
    simp
  · intro ha
    simp at ha
    obtain ⟨b, hb, hab⟩ := ha
    rw [Finset.mapEmbedding_apply] at hab
    simp at hab
    subst hab
    exact hb



@[simp]
lemma congr_trans {n m o : ℕ} (h1 : n = m) (h2 : m = o) :
    (congr h1).trans (congr h2) = congr (h1.trans h2) := by
  subst h1 h2
  simp [congr]

@[simp]
lemma congr_trans_apply {n m o : ℕ} (h1 : n = m) (h2 : m = o) (c : ContractionsNat n) :
    (congr h2) ((congr h1) c) = congr (h1.trans h2) c := by
  subst h1 h2
  simp

def congrLift {n m : ℕ} (h : n = m) {c : ContractionsNat n} (a : c.1) :
    (congr h c).1 := ⟨a.1.map (finCongr h).toEmbedding, by
    subst h
    simp⟩

@[simp]
lemma congrLift_rfl {n : ℕ} {c : ContractionsNat n} :
    c.congrLift rfl  = id := by
  funext a
  simp [congrLift]

lemma congrLift_injective {n m : ℕ} {c : ContractionsNat n}  (h : n = m) :
    Function.Injective (c.congrLift h) := by
  subst h
  simp
  exact fun ⦃a₁ a₂⦄ a => a

lemma congrLift_surjective {n m : ℕ} {c : ContractionsNat n}  (h : n = m) :
    Function.Surjective (c.congrLift h) := by
  subst h
  simp
  exact Function.surjective_id

lemma congrLift_bijective {n m : ℕ} {c : ContractionsNat n}  (h : n = m) :
    Function.Bijective (c.congrLift h) := by
  exact ⟨c.congrLift_injective h, c.congrLift_surjective h⟩

lemma eq_filter_mem_self : c.1 = Finset.filter (fun x => x ∈ c.1) Finset.univ := by
  exact Eq.symm (Finset.filter_univ_mem c.1)

def getDual? (i : Fin n) : Option (Fin n) := Fin.find (fun j => {i, j} ∈ c.1)

lemma getDual?_congr {n m : ℕ} (h : n = m) (c : ContractionsNat n) (i : Fin m) :
    (congr h c).getDual? i = Option.map (finCongr h) (c.getDual? (finCongr h.symm i)) := by
  subst h
  simp


lemma getDual?_congr_get {n m : ℕ} (h : n = m) (c : ContractionsNat n) (i : Fin m)
    (hg : ( (congr h c).getDual? i).isSome) :
    ((congr h c).getDual? i).get hg =
     (finCongr h ((c.getDual? (finCongr h.symm i)).get (by simpa [getDual?_congr] using hg)) ) := by
  simp [getDual?_congr]
  exact Option.get_map

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

lemma getDual?_isSome_iff  (i : Fin n) : (c.getDual? i).isSome ↔ ∃ (a : c.1), i ∈ a.1 := by
  apply Iff.intro
  · intro h
    simp [getDual?] at h
    rw [Fin.isSome_find_iff] at h
    obtain ⟨a, ha⟩ := h
    use ⟨{i, a}, ha⟩
    simp
  · intro h
    obtain ⟨a, ha⟩ := h
    have ha := c.2.1 a a.2
    rw [@Finset.card_eq_two] at ha
    obtain ⟨x, y, hx, hy⟩ := ha
    rw [hy] at ha
    simp at ha
    match ha with
    | Or.inl ha =>
      subst ha
      simp [getDual?]
      rw [Fin.isSome_find_iff]
      use y
      rw [← hy]
      exact a.2
    | Or.inr ha =>
      subst ha
      simp [getDual?]
      rw [Fin.isSome_find_iff]
      use x
      rw [Finset.pair_comm]
      rw [← hy]
      exact a.2

lemma getDual?_isSome_of_mem (a : c.1) (i : a.1) : (c.getDual? i).isSome := by
  rw [getDual?_isSome_iff]
  use ⟨a.1, a.2⟩
  simp

@[simp]
lemma getDual?_getDual?_get_get (i : Fin n) (h : (c.getDual? i).isSome) :
    c.getDual? ((c.getDual? i).get h) = some i := by
  rw [getDual?_eq_some_iff_mem]
  simp

lemma getDual?_getDual?_get_isSome (i : Fin n) (h : (c.getDual? i).isSome) :
    (c.getDual? ((c.getDual? i).get h)).isSome := by
  simp

lemma getDual?_getDual?_get_not_none (i : Fin n) (h : (c.getDual? i).isSome) :
    ¬ (c.getDual? ((c.getDual? i).get h)) = none := by
  simp



/-!

## Extracting parts from a contraction.

-/

def fstFieldOfContract (c : ContractionsNat n) (a : c.1) : Fin n :=
  (a.1.sort (· ≤ ·)).head (by
    have hx : (Finset.sort (fun x1 x2 => x1 ≤ x2) a.1).length =  a.1.card := by
      exact Finset.length_sort fun x1 x2 => x1 ≤ x2
    by_contra hn
    rw [hn, c.2.1 a.1 a.2] at hx
    simp at hx)

@[simp]
lemma fstFieldOfContract_congr {n m : ℕ} (h : n = m) (c : ContractionsNat n) (a : c.1) :
    (congr h c).fstFieldOfContract (c.congrLift h a) = (finCongr h) (c.fstFieldOfContract a) := by
  subst h
  simp [congr]

def sndFieldOfContract (c : ContractionsNat n) (a : c.1) : Fin n :=
  (a.1.sort (· ≤ ·)).tail.head (by
    have hx : (Finset.sort (fun x1 x2 => x1 ≤ x2) a.1).length =  a.1.card := by
      exact Finset.length_sort fun x1 x2 => x1 ≤ x2
    by_contra hn
    have hn := congrArg List.length hn
    simp at hn
    rw [c.2.1 a.1 a.2] at hn
    omega)

@[simp]
lemma sndFieldOfContract_congr {n m : ℕ} (h : n = m) (c : ContractionsNat n) (a : c.1) :
    (congr h c).sndFieldOfContract (c.congrLift h a) = (finCongr h) (c.sndFieldOfContract a) := by
  subst h
  simp [congr]

lemma finset_eq_fstFieldOfContract_sndFieldOfContract (c : ContractionsNat n) (a : c.1) :
    a.1 = {c.fstFieldOfContract a, c.sndFieldOfContract a} := by
  have h1 := c.2.1 a.1 a.2
  rw [Finset.card_eq_two] at h1
  obtain ⟨x, y, hxy, ha⟩ := h1
  rw [ha]
  by_cases hxyle : x ≤ y
  · have ha : a.1.sort (· ≤ ·) = [x, y] := by
      rw [ha]
      trans Finset.sort (· ≤ ·) (Finset.cons x {y} (by simp [hxy]))
      · congr
        simp
      rw [Finset.sort_cons]
      simp
      intro b hb
      simp at hb
      subst hb
      omega
    simp [fstFieldOfContract, ha, sndFieldOfContract]
  · have ha : a.1.sort (· ≤ ·) = [y, x] := by
      rw [ha]
      trans Finset.sort (· ≤ ·) (Finset.cons y {x} (by simp [hxy]; omega))
      · congr
        simp
        rw [@Finset.pair_comm]
      rw [Finset.sort_cons]
      simp
      intro b hb
      simp at hb
      subst hb
      omega
    simp [fstFieldOfContract, ha, sndFieldOfContract]
    rw [Finset.pair_comm]

lemma fstFieldOfContract_neq_sndFieldOfContract (c : ContractionsNat n) (a : c.1) :
    c.fstFieldOfContract a ≠ c.sndFieldOfContract a := by
  have h1 := c.2.1 a.1 a.2
  have h2 := c.finset_eq_fstFieldOfContract_sndFieldOfContract a
  by_contra hn
  rw [h2, hn] at h1
  simp at h1

lemma fstFieldOfContract_le_sndFieldOfContract (c : ContractionsNat n) (a : c.1) :
    c.fstFieldOfContract a ≤ c.sndFieldOfContract a := by
  simp [fstFieldOfContract, sndFieldOfContract]
  have h1 (n : ℕ) (l : List (Fin n))  (h : l ≠ []) (hl : l.Sorted (· ≤ ·)) :
      ∀ a ∈ l, l.head h ≤ a := by
    induction l with
    | nil => simp at h
    | cons i l ih =>
      simp at hl
      simpa using hl.1
  apply h1
  · exact Finset.sort_sorted (fun x1 x2 => x1 ≤ x2) _
  · exact List.getElem_mem _

lemma fstFieldOfContract_lt_sndFieldOfContract (c : ContractionsNat n) (a : c.1) :
    c.fstFieldOfContract a < c.sndFieldOfContract a :=
  lt_of_le_of_ne (c.fstFieldOfContract_le_sndFieldOfContract a)
    (c.fstFieldOfContract_neq_sndFieldOfContract a)

@[simp]
lemma fstFieldOfContract_mem (c : ContractionsNat n) (a : c.1) :
    c.fstFieldOfContract a ∈ a.1 := by
  rw [finset_eq_fstFieldOfContract_sndFieldOfContract]
  simp

@[simp]
lemma fstFieldOfContract_getDual?_isSome (c : ContractionsNat n) (a : c.1) :
    (c.getDual? (c.fstFieldOfContract a)).isSome := by
  rw [getDual?_isSome_iff]
  use a
  simp

@[simp]
lemma fstFieldOfContract_getDual? (c : ContractionsNat n) (a : c.1) :
    c.getDual? (c.fstFieldOfContract a) = some (c.sndFieldOfContract a) := by
  rw [getDual?_eq_some_iff_mem]
  erw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
  exact a.2

@[simp]
lemma sndFieldOfContract_mem (c : ContractionsNat n) (a : c.1) :
    c.sndFieldOfContract a ∈ a.1 := by
  rw [finset_eq_fstFieldOfContract_sndFieldOfContract]
  simp

@[simp]
lemma sndFieldOfContract_getDual?_isSome (c : ContractionsNat n) (a : c.1) :
    (c.getDual? (c.sndFieldOfContract a)).isSome := by
  rw [getDual?_isSome_iff]
  use a
  simp

@[simp]
lemma sndFieldOfContract_getDual? (c : ContractionsNat n) (a : c.1) :
    c.getDual? (c.sndFieldOfContract a) = some (c.fstFieldOfContract a) := by
  rw [getDual?_eq_some_iff_mem]
  rw [Finset.pair_comm]
  erw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
  exact a.2

lemma eq_fstFieldOfContract_of_mem (c : ContractionsNat n) (a : c.1) (i j : Fin n)
    (hi : i ∈ a.1) (hj : j ∈ a.1) (hij : i < j) :
    c.fstFieldOfContract a = i := by
  rw [finset_eq_fstFieldOfContract_sndFieldOfContract] at hi hj
  simp_all
  match hi, hj with
  | Or.inl hi, Or.inl hj =>
    subst hi hj
    simp at hij
  | Or.inl hi, Or.inr hj =>
    subst hi
    rfl
  | Or.inr hi, Or.inl hj =>
    subst hi hj
    have hn := fstFieldOfContract_lt_sndFieldOfContract c a
    omega
  | Or.inr hi, Or.inr hj =>
    subst hi hj
    simp at hij


lemma eq_sndFieldOfContract_of_mem (c : ContractionsNat n) (a : c.1) (i j : Fin n)
    (hi : i ∈ a.1) (hj : j ∈ a.1) (hij : i < j) :
    c.sndFieldOfContract a = j := by
  rw [finset_eq_fstFieldOfContract_sndFieldOfContract] at hi hj
  simp_all
  match hi, hj with
  | Or.inl hi, Or.inl hj =>
    subst hi hj
    simp at hij
  | Or.inl hi, Or.inr hj =>
    subst hi hj
    have hn := fstFieldOfContract_lt_sndFieldOfContract c a
    omega
  | Or.inr hi, Or.inl hj =>
    subst hi hj
    have hn := fstFieldOfContract_lt_sndFieldOfContract c a
    omega
  | Or.inr hi, Or.inr hj =>
    subst hi hj
    simp at hij

def contractEquivFinTwo (c : ContractionsNat n) (a : c.1) :
    a ≃ Fin 2 where
  toFun i := if i = c.fstFieldOfContract a then 0 else 1
  invFun i :=
    match i with
    | 0 => ⟨c.fstFieldOfContract a, fstFieldOfContract_mem c a⟩
    | 1 => ⟨c.sndFieldOfContract a, sndFieldOfContract_mem c a⟩
  left_inv i := by
    simp
    have hi := i.2
    have ha := c.finset_eq_fstFieldOfContract_sndFieldOfContract a
    simp [ha] at hi
    rcases hi with hi | hi
    · rw [hi]
      simp
      exact Subtype.eq (id (Eq.symm hi))
    · rw [hi]
      rw [if_neg]
      simp
      exact Subtype.eq (id (Eq.symm hi))
      have h := fstFieldOfContract_neq_sndFieldOfContract c a
      exact (Ne.symm h)
  right_inv i := by
    fin_cases i
    · simp
    · simp
      have h := fstFieldOfContract_neq_sndFieldOfContract c a
      exact (Ne.symm h)


lemma prod_finset_eq_mul_fst_snd (c : ContractionsNat n) (a : c.1)
  (f : a.1 → M) [CommMonoid M] :
    ∏ (x : a), f x = f (⟨c.fstFieldOfContract a, fstFieldOfContract_mem c a⟩)
    * f (⟨c.sndFieldOfContract a, sndFieldOfContract_mem c a⟩) := by
  rw [← (c.contractEquivFinTwo a).symm.prod_comp]
  simp [contractEquivFinTwo]


def IsGradedObeying (φs : List 𝓕.States) (c : ContractionsNat φs.length) :=
  ∀ (a : c.1), (𝓕 |>ₛ φs[c.fstFieldOfContract a]) = (𝓕 |>ₛ φs[c.sndFieldOfContract a])


def sigmaConstrainedEquiv : (a : c.1) × a ≃ {x : Fin n // (c.getDual? x).isSome} where
    toFun := fun x => ⟨x.2, getDual?_isSome_of_mem c x.fst x.snd⟩
    invFun := fun x => ⟨
      ⟨{x.1, (c.getDual? x.1).get x.2}, self_getDual?_get_mem c (↑x) x.prop⟩,
      ⟨x.1, by simp⟩⟩
    left_inv x := by
      have hxa (x1 x2 : (a : c.1) × a) (h1 : x1.1 = x2.1)
        (h2 : x1.2.val = x2.2.val) : x1 = x2 := by
        cases x1
        cases x2
        simp_all
        subst h1
        rename_i fst snd snd_1
        simp_all only [heq_eq_eq]
        obtain ⟨val, property⟩ := fst
        obtain ⟨val_2, property_2⟩ := snd
        subst h2
        simp_all only
      match x with
      | ⟨a, i⟩ =>
      apply hxa
      · have hc := c.2.2 a.1 a.2 {i.1, (c.getDual? ↑i).get (getDual?_isSome_of_mem c a i)}
          (self_getDual?_get_mem c (↑i) (getDual?_isSome_of_mem c a i))
        have hn : ¬ Disjoint a.1 {i.1, (c.getDual? ↑i).get (getDual?_isSome_of_mem c a i)} := by
          rw [Finset.disjoint_iff_inter_eq_empty]
          rw [@Finset.eq_empty_iff_forall_not_mem]
          simp
          use i
          simp
        simp_all
        exact Subtype.eq (id (Eq.symm hc))
      · simp
    right_inv := by
      intro x
      cases x
      rfl
end ContractionsNat
end FieldStruct
