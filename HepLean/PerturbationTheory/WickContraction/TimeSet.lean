/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.WickContraction.Join
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.TimeContraction
/-!

# Time contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra

def EqTimeOnlyCond {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) : Prop :=
  ∀ (i j), {i, j} ∈ φsΛ.1 → timeOrderRel φs[i] φs[j]
noncomputable section

noncomputable instance  {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
    Decidable (EqTimeOnlyCond φsΛ) :=
    inferInstanceAs (Decidable (∀ (i j), {i, j} ∈ φsΛ.1 → timeOrderRel φs[i] φs[j]))

noncomputable def EqTimeOnly (φs : List 𝓕.States) :
    Finset (WickContraction φs.length) := {φsΛ | EqTimeOnlyCond φsΛ}


namespace EqTimeOnly
variable {φs : List 𝓕.States} (φsΛ : EqTimeOnly φs)

lemma timeOrderRel_of_mem {i j : Fin φs.length} (h : {i, j} ∈ φsΛ.1.1) :
    timeOrderRel φs[i] φs[j] := by
  have h' := φsΛ.2
  simp only [EqTimeOnly, EqTimeOnlyCond, ne_eq, Fin.getElem_fin, Finset.mem_filter, Finset.mem_univ,
    true_and] at h'
  exact h' i j h

lemma timeOrderRel_both_of_mem {i j : Fin φs.length} (h : {i, j} ∈ φsΛ.1.1) :
    timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i]  := by
  apply And.intro
  · exact timeOrderRel_of_mem φsΛ h
  · apply timeOrderRel_of_mem φsΛ
    rw [@Finset.pair_comm]
    exact h

lemma mem_iff_forall_finset {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
    φsΛ ∈ EqTimeOnly φs ↔ ∀ (a  : φsΛ.1),
      timeOrderRel (φs[φsΛ.fstFieldOfContract a]) (φs[φsΛ.sndFieldOfContract a])
      ∧ timeOrderRel (φs[φsΛ.sndFieldOfContract a]) (φs[φsΛ.fstFieldOfContract a])  := by
  apply Iff.intro
  · intro h a
    apply timeOrderRel_both_of_mem ⟨φsΛ, h⟩
    simp
    rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
    simp
  · intro h
    simp [EqTimeOnly, EqTimeOnlyCond]
    intro i j h1
    have h' := h ⟨{i, j}, h1⟩
    by_cases hij: i < j
    · have hi : φsΛ.fstFieldOfContract ⟨{i, j}, h1⟩ = i := by
        apply eq_fstFieldOfContract_of_mem _ _ i j
        · simp
        · simp
        · exact hij
      have hj : φsΛ.sndFieldOfContract ⟨{i, j}, h1⟩ = j := by
        apply eq_sndFieldOfContract_of_mem _ _ i j
        · simp
        · simp
        · exact hij
      simp_all
    · have hij : i ≠ j := by
        by_contra hij
        subst hij
        have h2 := φsΛ.2.1 {i, i} h1
        simp at h2
      have hj : φsΛ.fstFieldOfContract ⟨{i, j}, h1⟩ = j := by
        apply eq_fstFieldOfContract_of_mem _ _ j i
        · simp
        · simp
        · omega
      have hi : φsΛ.sndFieldOfContract ⟨{i, j}, h1⟩ = i := by
        apply eq_sndFieldOfContract_of_mem _ _ j i
        · simp
        · simp
        · omega
      simp_all

@[simp]
lemma empty_mem {φs : List 𝓕.States} : empty ∈ EqTimeOnly φs := by
  rw [mem_iff_forall_finset]
  simp [empty]

lemma staticContract_eq_timeContract : φsΛ.1.staticContract = φsΛ.1.timeContract := by
  simp only [staticContract,  timeContract]
  apply congrArg
  funext a
  ext
  simp only [List.get_eq_getElem]
  rw [timeContract_of_timeOrderRel]
  apply timeOrderRel_of_mem φsΛ
  rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
  exact a.2

lemma mem_congr {φs φs' : List 𝓕.States} (h : φs = φs') (φsΛ : WickContraction φs.length):
    congr (by simp [h]) φsΛ ∈ EqTimeOnly φs' ↔ φsΛ ∈ EqTimeOnly φs := by
  subst h
  simp

lemma quotContraction_mem {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    (h : φsΛ ∈ EqTimeOnly φs)  (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    φsΛ.quotContraction S ha ∈ EqTimeOnly [φsΛ.subContraction S ha]ᵘᶜ := by
  rw [mem_iff_forall_finset]
  intro a
  simp
  erw [subContraction_uncontractedList_get]
  erw [subContraction_uncontractedList_get]
  simp
  rw [mem_iff_forall_finset] at h
  apply h

lemma exists_join_singleton_of_card_ge_zero {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (h : 0 < φsΛ.1.card) (h1 :  φsΛ ∈ EqTimeOnly φs) :
    ∃ (i j : Fin φs.length) (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length),
    φsΛ = join (singleton h) φsucΛ ∧ (timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i])
    ∧ φsucΛ ∈ EqTimeOnly [singleton h]ᵘᶜ ∧ φsucΛ.1.card + 1 = φsΛ.1.card := by
  obtain ⟨a, ha⟩ := exists_contraction_pair_of_card_ge_zero φsΛ h
  use φsΛ.fstFieldOfContract ⟨a, ha⟩
  use φsΛ.sndFieldOfContract ⟨a, ha⟩
  use φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩
  let φsucΛ :
     WickContraction [singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩)]ᵘᶜ.length :=
     congr (by simp [← subContraction_singleton_eq_singleton]) (φsΛ.quotContraction {a} (by simpa using ha))
  use φsucΛ
  simp [← subContraction_singleton_eq_singleton]
  apply And.intro
  · have h1 := join_congr (subContraction_singleton_eq_singleton _ ⟨a, ha⟩).symm (φsucΛ := φsucΛ)
    simp [h1, φsucΛ]
    rw [join_sub_quot]
  · apply And.intro
    · apply timeOrderRel_both_of_mem ⟨φsΛ, h1⟩
      simp
      rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
      simp [ha]
    apply And.intro
    · simp [φsucΛ]
      rw [mem_congr (φs := [(φsΛ.subContraction {a} (by simpa using ha))]ᵘᶜ)]
      simp
      exact quotContraction_mem h1 _ _
      rw [← subContraction_singleton_eq_singleton]
    · simp [φsucΛ]
      have h1 := subContraction_card_plus_quotContraction_card_eq _ {a} (by simpa using ha)
      simp [subContraction] at h1
      omega

lemma timeOrder_timeContract_mul_of_mem_mid_induction  {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (hl : φsΛ ∈ EqTimeOnly φs) (a b: 𝓕.FieldOpAlgebra) : (n : ℕ) → (hn : φsΛ.1.card = n) →
    𝓣(a * φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(a * b)
  | 0, hn => by
    rw [@card_zero_iff_empty] at hn
    subst hn
    simp
  | Nat.succ n, hn => by
    obtain ⟨i, j, hij, φsucΛ, rfl, h2, h3, h4⟩ := exists_join_singleton_of_card_ge_zero φsΛ (by simp [hn]) hl
    rw [join_timeContract]
    rw [singleton_timeContract]
    simp
    trans timeOrder (a * FieldOpAlgebra.timeContract φs[↑i] φs[↑j] * (φsucΛ.timeContract.1 * b))
    simp [mul_assoc]
    rw [timeOrder_timeContract_eq_time_mid]
    have ih := timeOrder_timeContract_mul_of_mem_mid_induction φsucΛ h3 a b n (by omega)
    rw [← mul_assoc, ih]
    simp [mul_assoc]
    simp_all
    simp_all

lemma timeOrder_timeContract_mul_of_mem_mid {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (hl : φsΛ ∈ EqTimeOnly φs) (a b : 𝓕.FieldOpAlgebra) :
    𝓣(a * φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣(a * b) := by
  exact timeOrder_timeContract_mul_of_mem_mid_induction φsΛ hl a b φsΛ.1.card rfl

lemma timeOrder_timeContract_mul_of_mem_left {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (hl : φsΛ ∈ EqTimeOnly φs) ( b : 𝓕.FieldOpAlgebra) :
    𝓣( φsΛ.timeContract.1 * b) = φsΛ.timeContract.1 * 𝓣( b) := by
  trans 𝓣(1 * φsΛ.timeContract.1 * b)
  simp
  rw [timeOrder_timeContract_mul_of_mem_mid φsΛ hl]
  simp

lemma exists_join_singleton_of_ne_mem {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (h1 : ¬ φsΛ ∈ EqTimeOnly φs) :
    ∃ (i j : Fin φs.length) (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length),
    φsΛ = join (singleton h) φsucΛ ∧ (¬ timeOrderRel φs[i] φs[j] ∨ ¬ timeOrderRel φs[j] φs[i]) := by
  rw [mem_iff_forall_finset] at h1
  simp at h1
  obtain ⟨a, ha, hr⟩ := h1
  use φsΛ.fstFieldOfContract ⟨a, ha⟩
  use φsΛ.sndFieldOfContract ⟨a, ha⟩
  use φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩
  let φsucΛ :
     WickContraction [singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩)]ᵘᶜ.length :=
     congr (by simp [← subContraction_singleton_eq_singleton]) (φsΛ.quotContraction {a} (by simpa using ha))
  use φsucΛ
  simp [← subContraction_singleton_eq_singleton]
  apply And.intro
  · have h1 := join_congr (subContraction_singleton_eq_singleton _ ⟨a, ha⟩).symm (φsucΛ := φsucΛ)
    simp [h1, φsucΛ]
    rw [join_sub_quot]
  · by_cases h1 : timeOrderRel φs[↑(φsΛ.fstFieldOfContract ⟨a, ha⟩)]
      φs[↑(φsΛ.sndFieldOfContract ⟨a, ha⟩)]
    · simp_all [h1]
    · simp_all [h1]

lemma timeOrder_timeContract_of_not_mem {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (hl : ¬ φsΛ ∈ EqTimeOnly φs) : 𝓣(φsΛ.timeContract.1) = 0 := by
  obtain ⟨i, j, hij, φsucΛ, rfl, hr⟩ := exists_join_singleton_of_ne_mem φsΛ hl
  rw [join_timeContract]
  rw [singleton_timeContract]
  simp
  rw [timeOrder_timeOrder_left]
  rw [timeOrder_timeContract_neq_time]
  simp
  simp_all
  intro h
  simp_all

lemma timeOrder_staticContract_of_not_mem {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (hl : ¬ φsΛ ∈ EqTimeOnly φs) : 𝓣(φsΛ.staticContract.1) = 0 := by
  obtain ⟨i, j, hij, φsucΛ, rfl, hr⟩ := exists_join_singleton_of_ne_mem φsΛ hl
  rw [join_staticContract]
  simp
  rw [singleton_staticContract]
  rw [timeOrder_timeOrder_left]
  rw [timeOrder_superCommute_anPart_ofFieldOp_neq_time]
  simp
  intro h
  simp_all

end EqTimeOnly


def HaveEqTime {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) : Prop :=
  ∃ (i j : Fin φs.length) (h : {i, j} ∈ φsΛ.1),
  timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i]


noncomputable instance  {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
    Decidable (HaveEqTime φsΛ) :=
    inferInstanceAs (Decidable (∃ (i j : Fin φs.length) (h : ({i, j} : Finset (Fin φs.length)) ∈ φsΛ.1),
      timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i]))

lemma haveEqTime_iff_finset {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
    HaveEqTime φsΛ ↔ ∃ (a : Finset (Fin φs.length)) (h : a ∈ φsΛ.1), timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩]
    ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩] := by
  simp [HaveEqTime]
  apply Iff.intro
  · intro h
    obtain ⟨i, j, hij, h1, h2⟩ := h
    use {i, j}, h1
    by_cases hij : i < j
    · have h1n := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ i j (by simp) (by simp) hij
      have h2n := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ i j (by simp) (by simp) hij
      simp [h1n, h2n]
      simp_all only [forall_true_left, true_and]
    · have hineqj : i ≠ j := by
        by_contra hineqj
        subst hineqj
        have h2 := φsΛ.2.1 {i, i} h1
        simp_all
      have hji : j < i := by omega
      have h1n := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ j i (by simp) (by simp) hji
      have h2n := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h1⟩ j i (by simp) (by simp) hji
      simp [h1n, h2n]
      simp_all
  · intro h
    obtain ⟨a, h1, h2, h3⟩ := h
    use φsΛ.fstFieldOfContract ⟨a, h1⟩
    use φsΛ.sndFieldOfContract ⟨a, h1⟩
    simp_all
    rw [← finset_eq_fstFieldOfContract_sndFieldOfContract]
    exact h1

@[simp]
lemma empty_not_haveEqTime {φs : List 𝓕.States} : ¬ HaveEqTime (empty : WickContraction φs.length) := by
  rw [haveEqTime_iff_finset]
  simp [empty]

def eqTimeContractSet {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
    Finset (Finset (Fin φs.length)) :=
  Finset.univ.filter (fun a =>
    a ∈ φsΛ.1 ∧ ∀ (h : a ∈ φsΛ.1),
     timeOrderRel φs[φsΛ.fstFieldOfContract ⟨a, h⟩] φs[φsΛ.sndFieldOfContract ⟨a, h⟩]
     ∧ timeOrderRel φs[φsΛ.sndFieldOfContract ⟨a, h⟩] φs[φsΛ.fstFieldOfContract ⟨a, h⟩])

lemma eqTimeContractSet_subset {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
    eqTimeContractSet φsΛ ⊆ φsΛ.1 := by
  simp [eqTimeContractSet]
  intro a
  simp
  intro h _
  exact h

lemma mem_of_mem_eqTimeContractSet{φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {a : Finset (Fin φs.length)} (h : a ∈ eqTimeContractSet φsΛ) : a ∈ φsΛ.1 := by
  simp [eqTimeContractSet] at h
  exact h.1

lemma join_eqTimeContractSet {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    eqTimeContractSet (join φsΛ φsucΛ) = φsΛ.eqTimeContractSet ∪
    φsucΛ.eqTimeContractSet.map (Finset.mapEmbedding uncontractedListEmd).toEmbedding := by
  ext a
  apply Iff.intro
  · intro h
    have hmem := mem_of_mem_eqTimeContractSet h
    have ht := joinLiftLeft_or_joinLiftRight_of_mem_join (φsucΛ := φsucΛ) _ hmem
    rcases ht with ht | ht
    · obtain ⟨b, rfl⟩ := ht
      simp
      left
      simp [eqTimeContractSet]
      apply And.intro (by simp [joinLiftLeft])
      intro h'
      simp [eqTimeContractSet] at h
      exact h
    · obtain ⟨b, rfl⟩ := ht
      simp
      right
      use b
      rw [Finset.mapEmbedding_apply]
      simp [joinLiftRight]
      simpa [eqTimeContractSet] using h
  · intro h
    simp at h
    rcases h with h | h
    · simp [eqTimeContractSet]
      simp [eqTimeContractSet] at h
      apply And.intro
      · simp [join, h.1]
      · intro h'
        have h2 := h.2 h.1
        exact h2
    · simp [eqTimeContractSet]
      simp [eqTimeContractSet] at h
      obtain ⟨b, h1, h2, rfl⟩ := h
      apply And.intro
      · simp [join, h1]
      · intro h'
        have h2 := h1.2 h1.1
        have hj : ⟨(Finset.mapEmbedding uncontractedListEmd) b, h'⟩ = joinLiftRight ⟨b, h1.1⟩ := by rfl
        simp [hj]
        simpa using h2


lemma eqTimeContractSet_of_not_haveEqTime {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    (h : ¬ HaveEqTime φsΛ) : eqTimeContractSet φsΛ = ∅  := by
  ext a
  simp
  by_contra hn
  rw [haveEqTime_iff_finset] at h
  simp at h
  simp [eqTimeContractSet] at hn
  have h2 := hn.2 hn.1
  have h3 := h a hn.1
  simp_all

lemma eqTimeContractSet_of_mem_eqTimeOnly {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    (h : φsΛ ∈ EqTimeOnly φs) : eqTimeContractSet φsΛ = φsΛ.1 := by
  ext a
  simp [eqTimeContractSet]
  rw [@EqTimeOnly.mem_iff_forall_finset] at h
  exact fun h_1 => h ⟨a, h_1⟩

lemma subContraction_eqTimeContractSet_eqTimeOnly {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
    φsΛ.subContraction (eqTimeContractSet φsΛ) (eqTimeContractSet_subset φsΛ) ∈
    EqTimeOnly φs := by
  rw [EqTimeOnly.mem_iff_forall_finset]
  intro a
  have ha2  := a.2
  simp [subContraction, -Finset.coe_mem, eqTimeContractSet] at ha2
  simp
  exact ha2.2 ha2.1

lemma pair_mem_eqTimeContractSet_iff  {φs : List 𝓕.States} {i j : Fin φs.length} (φsΛ : WickContraction φs.length) (h : {i, j} ∈ φsΛ.1) :
    {i, j} ∈  φsΛ.eqTimeContractSet ↔ timeOrderRel φs[i] φs[j] ∧ timeOrderRel φs[j] φs[i] := by
  simp [eqTimeContractSet]
  by_cases hij : i < j
  · have h1 := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h⟩ i j (by simp) (by simp) hij
    have h2 := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h⟩ i j (by simp) (by simp) hij
    simp [h1, h2]
    simp_all only [forall_true_left, true_and]
  · have hineqj : i ≠ j := by
      by_contra hineqj
      subst hineqj
      have h2 := φsΛ.2.1 {i, i} h
      simp_all
    have hji : j < i := by omega
    have h1 := eq_fstFieldOfContract_of_mem φsΛ ⟨{i,j}, h⟩ j i (by simp) (by simp) hji
    have h2 := eq_sndFieldOfContract_of_mem φsΛ ⟨{i,j}, h⟩ j i (by simp) (by simp) hji
    simp [h1, h2]
    simp_all only [not_lt, ne_eq, forall_true_left, true_and]
    apply Iff.intro
    · intro a
      simp_all only [and_self]
    · intro a
      simp_all only [and_self]

lemma subContraction_eqTimeContractSet_not_empty_of_haveEqTime
    {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) (h : HaveEqTime φsΛ) :
    φsΛ.subContraction (eqTimeContractSet φsΛ) (eqTimeContractSet_subset φsΛ) ≠ empty := by
  simp
  erw [Subtype.eq_iff]
  simp [empty, subContraction]
  rw [@Finset.eq_empty_iff_forall_not_mem]
  simp [HaveEqTime] at h
  obtain ⟨i, j, hij, h1, h2⟩ := h
  simp
  use {i, j}
  rw [pair_mem_eqTimeContractSet_iff]
  simp_all
  exact h1

lemma quotContraction_eqTimeContractSet_not_haveEqTime {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
   ¬ HaveEqTime (φsΛ.quotContraction (eqTimeContractSet φsΛ) (eqTimeContractSet_subset φsΛ)) := by
  rw [haveEqTime_iff_finset]
  simp
  intro a ha
  erw [subContraction_uncontractedList_get]
  erw [subContraction_uncontractedList_get]
  simp
  simp [quotContraction] at ha
  have hn' :  Finset.map uncontractedListEmd a ∉
      (φsΛ.subContraction (eqTimeContractSet φsΛ) (eqTimeContractSet_subset φsΛ) ).1 := by
    exact uncontractedListEmd_finset_not_mem a
  simp [subContraction, eqTimeContractSet] at hn'
  have hn'' := hn' ha
  obtain ⟨h, h1⟩ := hn''
  simp_all

lemma join_haveEqTime_of_eqTimeOnly_nonEmpty {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (h1 : φsΛ ∈ EqTimeOnly φs) (h2 : φsΛ ≠ empty)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    HaveEqTime (join φsΛ φsucΛ) := by
  simp [join, HaveEqTime]
  simp [EqTimeOnly, EqTimeOnlyCond] at h1
  obtain ⟨i, j, h⟩ := exists_pair_of_not_eq_empty _ h2
  use i, j
  have h1 := h1 i j h
  simp_all
  apply h1 j i
  rw [Finset.pair_comm]
  exact h

lemma hasEqTimeEquiv_ext_sigma {φs : List 𝓕.States} {x1 x2 :  Σ (φsΛ : {φsΛ : WickContraction φs.length // φsΛ ∈ EqTimeOnly φs ∧ φsΛ ≠ empty}),
    {φssucΛ : WickContraction [φsΛ.1]ᵘᶜ.length // ¬ HaveEqTime φssucΛ}}
    (h1 : x1.1.1 = x2.1.1) (h2 : x1.2.1 = congr (by simp [h1]) x2.2.1) : x1 = x2 := by
  match x1, x2 with
  | ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩, ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩ =>
    simp at h1
    subst h1
    simp at h2
    simp [h2]

def hasEqTimeEquiv (φs : List 𝓕.States) :
    {φsΛ : WickContraction φs.length // HaveEqTime φsΛ} ≃
    Σ (φsΛ : {φsΛ : WickContraction φs.length // φsΛ ∈ EqTimeOnly φs ∧ φsΛ ≠ empty}),
    {φssucΛ : WickContraction [φsΛ.1]ᵘᶜ.length // ¬ HaveEqTime φssucΛ}  where
  toFun φsΛ := ⟨⟨φsΛ.1.subContraction (eqTimeContractSet φsΛ.1) (eqTimeContractSet_subset φsΛ.1),
    subContraction_eqTimeContractSet_eqTimeOnly φsΛ.1,
    subContraction_eqTimeContractSet_not_empty_of_haveEqTime φsΛ.1 φsΛ.2⟩,
    ⟨φsΛ.1.quotContraction (eqTimeContractSet φsΛ.1) (eqTimeContractSet_subset φsΛ.1),
    quotContraction_eqTimeContractSet_not_haveEqTime φsΛ.1⟩⟩
  invFun φsΛ := ⟨join φsΛ.1.1 φsΛ.2.1 , join_haveEqTime_of_eqTimeOnly_nonEmpty φsΛ.1.1 φsΛ.1.2.1 φsΛ.1.2.2 φsΛ.2⟩
  left_inv φsΛ := by
    match φsΛ with
    | ⟨φsΛ, h1, h2⟩ =>
      simp
      exact join_sub_quot φsΛ φsΛ.eqTimeContractSet (eqTimeContractSet_subset φsΛ)
  right_inv φsΛ' := by
    match φsΛ' with
    | ⟨⟨φsΛ, h1⟩, ⟨φsucΛ, h2⟩⟩ =>
      have hs : subContraction (φsΛ.join φsucΛ).eqTimeContractSet (
        eqTimeContractSet_subset (φsΛ.join φsucΛ)) = φsΛ  := by
        apply Subtype.ext
        ext a
        simp [subContraction]
        rw [join_eqTimeContractSet]
        rw [eqTimeContractSet_of_not_haveEqTime h2]
        simp
        rw [eqTimeContractSet_of_mem_eqTimeOnly h1.1]
      refine hasEqTimeEquiv_ext_sigma ?_ ?_
      · simp
        exact hs
      · simp
        apply Subtype.ext
        ext a
        simp [quotContraction]
        rw [mem_congr_iff]
        rw [mem_join_right_iff]
        simp
        rw [uncontractedListEmd_congr hs]
        rw [Finset.map_map]


lemma sum_haveEqTime (φs : List 𝓕.States)
    (f : WickContraction φs.length → M) [AddCommMonoid M]:
  ∑ (φsΛ : {φsΛ : WickContraction φs.length // HaveEqTime φsΛ}), f φsΛ =
  ∑ (φsΛ : {φsΛ : WickContraction φs.length // φsΛ ∈ EqTimeOnly φs ∧ φsΛ ≠ empty}),
  ∑ (φssucΛ : {φssucΛ : WickContraction [φsΛ.1]ᵘᶜ.length // ¬ HaveEqTime φssucΛ}),
    f (join φsΛ.1 φssucΛ.1) := by
  rw [← (hasEqTimeEquiv φs).symm.sum_comp]
  erw [Finset.sum_sigma]
  rfl

end
end WickContraction
