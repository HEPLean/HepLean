/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.WickContraction.StaticContract
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.TimeContraction
import HepLean.PerturbationTheory.WickContraction.SubContraction
import HepLean.PerturbationTheory.WickContraction.Singleton

/-!

# Join of contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra

/-- Given a Wick contraction `φsΛ` on `φs` and a Wick contraction `φsucΛ` on the uncontracted fields
within `φsΛ`, a Wick contraction on `φs`consisting of the contractins in `φsΛ` and
the contractions in `φsucΛ`. -/
def join {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) : WickContraction φs.length :=
  ⟨φsΛ.1 ∪ φsucΛ.1.map (Finset.mapEmbedding uncontractedListEmd).toEmbedding, by
    intro a ha
    simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding] at ha
    rcases ha with ha | ha
    · exact φsΛ.2.1 a ha
    · obtain ⟨a, ha, rfl⟩ := ha
      rw [Finset.mapEmbedding_apply]
      simp only [Finset.card_map]
      exact φsucΛ.2.1 a ha, by
    intro a ha b hb
    simp only [Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact φsΛ.2.2 a ha b hb
    · obtain ⟨b, hb, rfl⟩ := hb
      right
      symm
      rw [Finset.mapEmbedding_apply]
      apply uncontractedListEmd_finset_disjoint_left
      exact ha
    · obtain ⟨a, ha, rfl⟩ := ha
      right
      rw [Finset.mapEmbedding_apply]
      apply uncontractedListEmd_finset_disjoint_left
      exact hb
    · obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      simp only [EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
      rw [Finset.disjoint_map]
      exact φsucΛ.2.2 a ha b hb⟩

lemma join_congr {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} {φsΛ' : WickContraction φs.length}
    (h1 : φsΛ = φsΛ') :
    join φsΛ φsucΛ = join φsΛ' (congr (by simp [h1]) φsucΛ) := by
  subst h1
  rfl

/-- Given a contracting pair within `φsΛ` the corresponding contracting pair within
  `(join φsΛ φsucΛ)`. -/
def joinLiftLeft {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsΛ.1 → (join φsΛ φsucΛ).1 :=
  fun a => ⟨a, by simp [join]⟩

lemma jointLiftLeft_injective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    Function.Injective (@joinLiftLeft _ _ φsΛ φsucΛ) := by
  intro a b h
  simp only [joinLiftLeft] at h
  rw [Subtype.mk_eq_mk] at h
  refine Subtype.eq h

/-- Given a contracting pair within `φsucΛ` the corresponding contracting pair within
  `(join φsΛ φsucΛ)`. -/
def joinLiftRight {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsucΛ.1 → (join φsΛ φsucΛ).1 :=
  fun a => ⟨a.1.map uncontractedListEmd, by
    simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    right
    use a.1
    simp only [Finset.coe_mem, true_and]
    rfl⟩

lemma joinLiftRight_injective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    Function.Injective (@joinLiftRight _ _ φsΛ φsucΛ) := by
  intro a b h
  simp only [joinLiftRight] at h
  rw [Subtype.mk_eq_mk] at h
  simp only [Finset.map_inj] at h
  refine Subtype.eq h

lemma jointLiftLeft_disjoint_joinLiftRight {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} (a : φsΛ.1) (b : φsucΛ.1) :
    Disjoint (@joinLiftLeft _ _ _ φsucΛ a).1 (joinLiftRight b).1 := by
  simp only [joinLiftLeft, joinLiftRight]
  symm
  apply uncontractedListEmd_finset_disjoint_left
  exact a.2

lemma jointLiftLeft_neq_joinLiftRight {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} (a : φsΛ.1) (b : φsucΛ.1) :
    joinLiftLeft a ≠ joinLiftRight b := by
  by_contra hn
  have h1 := jointLiftLeft_disjoint_joinLiftRight a b
  rw [hn] at h1
  simp only [disjoint_self, Finset.bot_eq_empty] at h1
  have hj := (join φsΛ φsucΛ).2.1 (joinLiftRight b).1 (joinLiftRight b).2
  rw [h1] at hj
  simp at hj

/-- The map from contracted pairs of `φsΛ` and `φsucΛ` to contracted pairs in
  `(join φsΛ φsucΛ)`. -/
def joinLift {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsΛ.1 ⊕ φsucΛ.1 → (join φsΛ φsucΛ).1 := fun a =>
  match a with
  | Sum.inl a => joinLiftLeft a
  | Sum.inr a => joinLiftRight a

lemma joinLift_injective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Injective (@joinLift _ _ φsΛ φsucΛ) := by
  intro a b h
  match a, b with
  | Sum.inl a, Sum.inl b =>
    simp only [Sum.inl.injEq]
    exact jointLiftLeft_injective h
  | Sum.inr a, Sum.inr b =>
    simp only [Sum.inr.injEq]
    exact joinLiftRight_injective h
  | Sum.inl a, Sum.inr b =>
    simp only [joinLift] at h
    have h1 := jointLiftLeft_neq_joinLiftRight a b
    simp_all
  | Sum.inr a, Sum.inl b =>
    simp only [joinLift] at h
    have h1 := jointLiftLeft_neq_joinLiftRight b a
    simp_all

lemma joinLift_surjective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Surjective (@joinLift _ _ φsΛ φsucΛ) := by
  intro a
  have ha2 := a.2
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha2
  rcases ha2 with ha2 | ⟨a2, ha3⟩
  · use Sum.inl ⟨a, ha2⟩
    simp [joinLift, joinLiftLeft]
  · rw [Finset.mapEmbedding_apply] at ha3
    use Sum.inr ⟨a2, ha3.1⟩
    simp only [joinLift, joinLiftRight]
    refine Subtype.eq ?_
    exact ha3.2

lemma joinLift_bijective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Bijective (@joinLift _ _ φsΛ φsucΛ) := by
  apply And.intro
  · exact joinLift_injective
  · exact joinLift_surjective

lemma prod_join {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (f : (join φsΛ φsucΛ).1 → M) [CommMonoid M]:
      ∏ (a : (join φsΛ φsucΛ).1), f a = (∏ (a : φsΛ.1), f (joinLiftLeft a)) *
      ∏ (a : φsucΛ.1), f (joinLiftRight a) := by
  let e1 := Equiv.ofBijective (@joinLift _ _ φsΛ φsucΛ) joinLift_bijective
  rw [← e1.prod_comp]
  simp only [Fintype.prod_sum_type, Finset.univ_eq_attach]
  rfl

lemma joinLiftLeft_or_joinLiftRight_of_mem_join {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) {a : Finset (Fin φs.length)}
    (ha : a ∈ (join φsΛ φsucΛ).1) :
    (∃ b, a = (joinLiftLeft (φsucΛ := φsucΛ) b).1) ∨
    (∃ b, a = (joinLiftRight (φsucΛ := φsucΛ) b).1) := by
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha
  rcases ha with ha | ⟨a, ha, rfl⟩
  · left
    use ⟨a, ha⟩
    rfl
  · right
    use ⟨a, ha⟩
    rfl

@[simp]
lemma join_fstFieldOfContract_joinLiftRight {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsucΛ.1) :
    (join φsΛ φsucΛ).fstFieldOfContract (joinLiftRight a) =
    uncontractedListEmd (φsucΛ.fstFieldOfContract a) := by
  apply eq_fstFieldOfContract_of_mem _ _ _ (uncontractedListEmd (φsucΛ.sndFieldOfContract a))
  · simp [joinLiftRight]
  · simp [joinLiftRight]
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a

@[simp]
lemma join_sndFieldOfContract_joinLiftRight {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsucΛ.1) :
    (join φsΛ φsucΛ).sndFieldOfContract (joinLiftRight a) =
    uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by
  apply eq_sndFieldOfContract_of_mem _ _ (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
  · simp [joinLiftRight]
  · simp [joinLiftRight]
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a

@[simp]
lemma join_fstFieldOfContract_joinLiftLeft {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsΛ.1) :
    (join φsΛ φsucΛ).fstFieldOfContract (joinLiftLeft a) =
    (φsΛ.fstFieldOfContract a) := by
  apply eq_fstFieldOfContract_of_mem _ _ _ (φsΛ.sndFieldOfContract a)
  · simp [joinLiftLeft]
  · simp [joinLiftLeft]
  · exact fstFieldOfContract_lt_sndFieldOfContract φsΛ a

@[simp]
lemma join_sndFieldOfContract_joinLift {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsΛ.1) :
    (join φsΛ φsucΛ).sndFieldOfContract (joinLiftLeft a) =
    (φsΛ.sndFieldOfContract a) := by
  apply eq_sndFieldOfContract_of_mem _ _ (φsΛ.fstFieldOfContract a) (φsΛ.sndFieldOfContract a)
  · simp [joinLiftLeft]
  · simp [joinLiftLeft]
  · exact fstFieldOfContract_lt_sndFieldOfContract φsΛ a

lemma mem_join_right_iff {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : Finset (Fin [φsΛ]ᵘᶜ.length)) :
    a ∈ φsucΛ.1 ↔ a.map uncontractedListEmd ∈ (join φsΛ φsucΛ).1 := by
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  have h1' : ¬ Finset.map uncontractedListEmd a ∈ φsΛ.1 :=
    uncontractedListEmd_finset_not_mem a
  simp only [h1', false_or]
  apply Iff.intro
  · intro h
    use a
    simp only [h, true_and]
    rw [Finset.mapEmbedding_apply]
  · intro h
    obtain ⟨a, ha, h2⟩ := h
    rw [Finset.mapEmbedding_apply] at h2
    simp only [Finset.map_inj] at h2
    subst h2
    exact ha

lemma join_card {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    (join φsΛ φsucΛ).1.card = φsΛ.1.card + φsucΛ.1.card := by
  simp only [join, Finset.le_eq_subset]
  rw [Finset.card_union_of_disjoint]
  simp only [Finset.card_map]
  rw [@Finset.disjoint_left]
  intro a ha
  simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding, not_exists, not_and]
  intro x hx
  by_contra hn
  have hdis : Disjoint (Finset.map uncontractedListEmd x) a := by
    exact uncontractedListEmd_finset_disjoint_left x a ha
  rw [Finset.mapEmbedding_apply] at hn
  rw [hn] at hdis
  simp only [disjoint_self, Finset.bot_eq_empty] at hdis
  have hcard := φsΛ.2.1 a ha
  simp_all

@[simp]
lemma empty_join {φs : List 𝓕.States} (φsΛ : WickContraction [empty (n := φs.length)]ᵘᶜ.length) :
    join empty φsΛ = congr (by simp) φsΛ := by
  apply Subtype.ext
  simp only [join, Finset.le_eq_subset, uncontractedListEmd_empty]
  ext a
  conv_lhs =>
    left
    left
    rw [empty]
  simp only [Finset.empty_union, Finset.mem_map, RelEmbedding.coe_toEmbedding]
  rw [mem_congr_iff]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    rw [Finset.mapEmbedding_apply]
    rw [Finset.map_map]
    apply Set.mem_of_eq_of_mem _ ha
    trans Finset.map (Equiv.refl _).toEmbedding a
    rfl
    simp
  · intro h
    use Finset.map (finCongr (by simp)).toEmbedding a
    simp only [h, true_and]
    trans Finset.map (Equiv.refl _).toEmbedding a
    rw [Finset.mapEmbedding_apply, Finset.map_map]
    rfl
    simp

@[simp]
lemma join_empty {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
    join φsΛ empty = φsΛ := by
  apply Subtype.ext
  ext a
  simp [join, empty]

lemma join_timeContract {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).timeContract = φsΛ.timeContract * φsucΛ.timeContract := by
  simp only [timeContract, List.get_eq_getElem]
  rw [prod_join]
  congr 1
  congr
  funext a
  simp

lemma join_staticContract {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).staticContract = φsΛ.staticContract * φsucΛ.staticContract := by
  simp only [staticContract, List.get_eq_getElem]
  rw [prod_join]
  congr 1
  congr
  funext a
  simp

lemma mem_join_uncontracted_of_mem_right_uncontracted {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length)
    (ha : i ∈ φsucΛ.uncontracted) :
    uncontractedListEmd i ∈ (join φsΛ φsucΛ).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at hp
  rcases hp with hp | hp
  · have hi : uncontractedListEmd i ∈ φsΛ.uncontracted := by
      exact uncontractedListEmd_mem_uncontracted i
    rw [mem_uncontracted_iff_not_contracted] at hi
    exact hi p hp
  · obtain ⟨p, hp, rfl⟩ := hp
    rw [Finset.mapEmbedding_apply]
    simp only [Finset.mem_map']
    rw [mem_uncontracted_iff_not_contracted] at ha
    exact ha p hp

lemma exists_mem_left_uncontracted_of_mem_join_uncontracted {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin φs.length)
    (ha : i ∈ (join φsΛ φsucΛ).uncontracted) :
    i ∈ φsΛ.uncontracted := by
  rw [@mem_uncontracted_iff_not_contracted]
  rw [@mem_uncontracted_iff_not_contracted] at ha
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding] at ha
  intro p hp
  simp_all

lemma exists_mem_right_uncontracted_of_mem_join_uncontracted {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin φs.length)
    (hi : i ∈ (join φsΛ φsucΛ).uncontracted) :
    ∃ a, uncontractedListEmd a = i ∧ a ∈ φsucΛ.uncontracted := by
  have hi' := exists_mem_left_uncontracted_of_mem_join_uncontracted _ _ i hi
  obtain ⟨j, rfl⟩ := uncontractedListEmd_surjective_mem_uncontracted i hi'
  use j
  simp only [true_and]
  rw [mem_uncontracted_iff_not_contracted] at hi
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  have hip := hi (p.map uncontractedListEmd) (by
    simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    right
    use p
    simp only [hp, true_and]
    rw [Finset.mapEmbedding_apply])
  simpa using hip

lemma join_uncontractedList {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).uncontractedList = List.map uncontractedListEmd φsucΛ.uncontractedList := by
  rw [uncontractedList_eq_sort]
  rw [uncontractedList_eq_sort]
  rw [fin_finset_sort_map_monotone]
  congr
  ext a
  simp only [Finset.mem_map]
  apply Iff.intro
  · intro h
    obtain ⟨a, rfl, ha⟩ := exists_mem_right_uncontracted_of_mem_join_uncontracted _ _ a h
    use a, ha
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    exact mem_join_uncontracted_of_mem_right_uncontracted φsΛ φsucΛ a ha
  · intro a b h
    exact uncontractedListEmd_strictMono h

lemma join_uncontractedList_get {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    ((join φsΛ φsucΛ).uncontractedList).get =
    φsΛ.uncontractedListEmd ∘ (φsucΛ.uncontractedList).get ∘
        (Fin.cast (by rw [join_uncontractedList]; simp)) := by
  have h1 {n : ℕ} (l1 l2 : List (Fin n)) (h : l1 = l2) :
      l1.get = l2.get ∘ Fin.cast (by rw [h]) := by
    subst h
    rfl
  conv_lhs => rw [h1 _ _ (join_uncontractedList φsΛ φsucΛ)]
  ext i
  simp

lemma join_uncontractedListGet {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).uncontractedListGet = φsucΛ.uncontractedListGet := by
  simp only [uncontractedListGet, join_uncontractedList, List.map_map, List.map_inj_left,
    Function.comp_apply, List.get_eq_getElem, List.getElem_map]
  intro a ha
  simp only [uncontractedListEmd, uncontractedIndexEquiv, List.get_eq_getElem,
    Equiv.trans_toEmbedding, Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.coe_fn_mk,
    Function.Embedding.coe_subtype]
  rfl

lemma join_uncontractedListEmb {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).uncontractedListEmd =
    ((finCongr (congrArg List.length (join_uncontractedListGet _ _))).toEmbedding.trans
      φsucΛ.uncontractedListEmd).trans φsΛ.uncontractedListEmd := by
  refine Function.Embedding.ext_iff.mpr (congrFun ?_)
  change uncontractedListEmd.toFun = _
  rw [uncontractedListEmd_toFun_eq_get]
  rw [join_uncontractedList_get]
  rfl

lemma join_assoc {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (φsucΛ' : WickContraction [φsΛ.join φsucΛ]ᵘᶜ.length) :
    join (join φsΛ φsucΛ) (φsucΛ') = join φsΛ (join φsucΛ (congr
      (congrArg List.length (join_uncontractedListGet _ _)) φsucΛ')) := by
  apply Subtype.ext
  ext a
  by_cases ha : a ∈ φsΛ.1
  · simp [ha, join]
  simp only [join, Finset.le_eq_subset, Finset.union_assoc, Finset.mem_union, ha, Finset.mem_map,
    RelEmbedding.coe_toEmbedding, false_or]
  apply Iff.intro
  · intro h
    rcases h with h | h
    · obtain ⟨a, ha', rfl⟩ := h
      use a
      simp [ha']
    · obtain ⟨a, ha', rfl⟩ := h
      let a' := congrLift (congrArg List.length (join_uncontractedListGet _ _)) ⟨a, ha'⟩
      let a'' := joinLiftRight a'
      use a''
      apply And.intro
      · right
        use a'
        apply And.intro
        · exact a'.2
        · simp only [joinLiftRight, a'']
          rfl
      · simp only [a'']
        rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
        simp only [a', joinLiftRight, congrLift]
        rw [join_uncontractedListEmb]
        simp [Finset.map_map]
  · intro h
    obtain ⟨a, ha', rfl⟩ := h
    rcases ha' with ha' | ha'
    · left
      use a
    · obtain ⟨a, ha', rfl⟩ := ha'
      right
      let a' := congrLiftInv _ ⟨a, ha'⟩
      use a'
      simp only [Finset.coe_mem, true_and]
      simp only [a']
      rw [Finset.mapEmbedding_apply]
      rw [join_uncontractedListEmb]
      simp only [congrLiftInv, ← Finset.map_map]
      congr
      rw [Finset.map_map]
      change Finset.map (Equiv.refl _).toEmbedding a = _
      simp only [Equiv.refl_toEmbedding, Finset.map_refl]

lemma join_getDual?_apply_uncontractedListEmb_eq_none_iff {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).getDual? (uncontractedListEmd i) = none
    ↔ φsucΛ.getDual? i = none := by
  rw [getDual?_eq_none_iff_mem_uncontracted, getDual?_eq_none_iff_mem_uncontracted]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha', ha⟩ := exists_mem_right_uncontracted_of_mem_join_uncontracted _ _
      (uncontractedListEmd i) h
    simp only [EmbeddingLike.apply_eq_iff_eq] at ha'
    subst ha'
    exact ha
  · intro h
    exact mem_join_uncontracted_of_mem_right_uncontracted φsΛ φsucΛ i h

lemma join_getDual?_apply_uncontractedListEmb_isSome_iff {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length) :
    ((join φsΛ φsucΛ).getDual? (uncontractedListEmd i)).isSome
    ↔ (φsucΛ.getDual? i).isSome := by
  rw [← Decidable.not_iff_not]
  simp [join_getDual?_apply_uncontractedListEmb_eq_none_iff]

lemma join_getDual?_apply_uncontractedListEmb_some {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length)
    (hi :((join φsΛ φsucΛ).getDual? (uncontractedListEmd i)).isSome) :
    ((join φsΛ φsucΛ).getDual? (uncontractedListEmd i)) =
    some (uncontractedListEmd ((φsucΛ.getDual? i).get (by
    simpa [join_getDual?_apply_uncontractedListEmb_isSome_iff]using hi))) := by
  rw [getDual?_eq_some_iff_mem]
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  right
  use {i, (φsucΛ.getDual? i).get (by
    simpa [join_getDual?_apply_uncontractedListEmb_isSome_iff] using hi)}
  simp only [self_getDual?_get_mem, true_and]
  rw [Finset.mapEmbedding_apply]
  simp

@[simp]
lemma join_getDual?_apply_uncontractedListEmb {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length) :
    ((join φsΛ φsucΛ).getDual? (uncontractedListEmd i)) =
    Option.map uncontractedListEmd (φsucΛ.getDual? i) := by
  by_cases h : (φsucΛ.getDual? i).isSome
  · rw [join_getDual?_apply_uncontractedListEmb_some]
    have h1 : (φsucΛ.getDual? i) = (φsucΛ.getDual? i).get (by simpa using h) :=
      Eq.symm (Option.some_get h)
    conv_rhs => rw [h1]
    simp only [Option.map_some']
    exact (join_getDual?_apply_uncontractedListEmb_isSome_iff φsΛ φsucΛ i).mpr h
  · simp only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none] at h
    rw [h]
    simp only [Option.map_none', join_getDual?_apply_uncontractedListEmb_eq_none_iff]
    exact h

/-!

## Subcontractions and quotient contractions

-/

section

variable {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)

lemma join_sub_quot (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    join (subContraction S ha) (quotContraction S ha) = φsΛ := by
  apply Subtype.ext
  ext a
  simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
    RelEmbedding.coe_toEmbedding]
  apply Iff.intro
  · intro h
    rcases h with h | h
    · exact mem_of_mem_subContraction h
    · obtain ⟨a, ha, rfl⟩ := h
      apply mem_of_mem_quotContraction ha
  · intro h
    have h1 := mem_subContraction_or_quotContraction (S := S) (a := a) (hs := ha) h
    rcases h1 with h1 | h1
    · simp [h1]
    · right
      obtain ⟨a, rfl, ha⟩ := h1
      use a
      simp only [ha, true_and]
      rw [Finset.mapEmbedding_apply]

lemma subContraction_card_plus_quotContraction_card_eq (S : Finset (Finset (Fin φs.length)))
    (ha : S ⊆ φsΛ.1) :
    (subContraction S ha).1.card + (quotContraction S ha).1.card = φsΛ.1.card := by
  rw [← join_card]
  simp [join_sub_quot]

end
open FieldStatistic

lemma stat_signFinset_right {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i j : Fin [φsΛ]ᵘᶜ.length) :
    (𝓕 |>ₛ ⟨[φsΛ]ᵘᶜ.get, φsucΛ.signFinset i j⟩) =
    (𝓕 |>ₛ ⟨φs.get, (φsucΛ.signFinset i j).map uncontractedListEmd⟩) := by
  simp only [ofFinset]
  congr 1
  rw [← fin_finset_sort_map_monotone]
  simp only [List.map_map, List.map_inj_left, Finset.mem_sort, List.get_eq_getElem,
    Function.comp_apply, getElem_uncontractedListEmd, implies_true]
  intro i j h
  exact uncontractedListEmd_strictMono h

lemma signFinset_right_map_uncontractedListEmd_eq_filter {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length) (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length)
    (i j : Fin [φsΛ]ᵘᶜ.length) : (φsucΛ.signFinset i j).map uncontractedListEmd =
    ((join φsΛ φsucΛ).signFinset (uncontractedListEmd i) (uncontractedListEmd j)).filter
    (fun c => c ∈ φsΛ.uncontracted) := by
  ext a
  simp only [Finset.mem_map, Finset.mem_filter]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    apply And.intro
    · simp_all only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      join_getDual?_apply_uncontractedListEmb, Option.map_eq_none', Option.isSome_map']
      apply And.intro
      · exact uncontractedListEmd_strictMono ha.1
      · apply And.intro
        · exact uncontractedListEmd_strictMono ha.2.1
        · have ha2 := ha.2.2
          simp_all only [and_true]
          rcases ha2 with ha2 | ha2
          · simp [ha2]
          · right
            intro h
            apply lt_of_lt_of_eq (uncontractedListEmd_strictMono (ha2 h))
            rw [Option.get_map]
    · exact uncontractedListEmd_mem_uncontracted a
  · intro h
    have h2 := h.2
    have h2' := uncontractedListEmd_surjective_mem_uncontracted a h.2
    obtain ⟨a, rfl⟩ := h2'
    use a
    simp_all only [signFinset, Finset.mem_filter, Finset.mem_univ,
      join_getDual?_apply_uncontractedListEmb, Option.map_eq_none', Option.isSome_map', true_and,
      and_true, and_self]
    apply And.intro
    · have h1 := h.1
      rw [StrictMono.lt_iff_lt] at h1
      exact h1
      exact fun _ _ h => uncontractedListEmd_strictMono h
    · apply And.intro
      · have h1 := h.2.1
        rw [StrictMono.lt_iff_lt] at h1
        exact h1
        exact fun _ _ h => uncontractedListEmd_strictMono h
      · have h1 := h.2.2
        simp_all only [and_true]
        rcases h1 with h1 | h1
        · simp [h1]
        · right
          intro h
          have h1' := h1 h
          have hl : uncontractedListEmd i < uncontractedListEmd ((φsucΛ.getDual? a).get h) := by
            apply lt_of_lt_of_eq h1'
            simp [Option.get_map]
          rw [StrictMono.lt_iff_lt] at hl
          exact hl
          exact fun _ _ h => uncontractedListEmd_strictMono h

lemma sign_right_eq_prod_mul_prod {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    φsucΛ.sign = (∏ a, 𝓢(𝓕|>ₛ [φsΛ]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
    ((join φsΛ φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
      (uncontractedListEmd (φsucΛ.sndFieldOfContract a))).filter
      (fun c => ¬ c ∈ φsΛ.uncontracted)⟩)) *
    (∏ a, 𝓢(𝓕|>ₛ [φsΛ]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
      ((join φsΛ φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
        (uncontractedListEmd (φsucΛ.sndFieldOfContract a)))⟩)) := by
  rw [← Finset.prod_mul_distrib, sign]
  congr
  funext a
  rw [← map_mul]
  congr
  rw [stat_signFinset_right, signFinset_right_map_uncontractedListEmd_eq_filter]
  rw [ofFinset_filter]

lemma join_singleton_signFinset_eq_filter {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).signFinset i j =
    ((singleton h).signFinset i j).filter (fun c => ¬
    (((join (singleton h) φsucΛ).getDual? c).isSome ∧
    ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
    (((join (singleton h) φsucΛ).getDual? c).get h1) < i))) := by
  ext a
  simp only [signFinset, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_forall, not_lt,
    and_assoc, and_congr_right_iff]
  intro h1 h2
  have h1 : (singleton h).getDual? a = none := by
    rw [singleton_getDual?_eq_none_iff_neq]
    omega
  simp only [h1, Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, or_self, true_and]
  apply Iff.intro
  · intro h1 h2
    rcases h1 with h1 | h1
    · simp only [h1, Option.isSome_none, Bool.false_eq_true, IsEmpty.exists_iff]
      have h2' : ¬ (((singleton h).join φsucΛ).getDual? a).isSome := by
        exact Option.not_isSome_iff_eq_none.mpr h1
      exact h2' h2
    use h2
    have h1 := h1 h2
    omega
  · intro h2
    by_cases h2' : (((singleton h).join φsucΛ).getDual? a).isSome = true
    · have h2 := h2 h2'
      obtain ⟨hb, h2⟩ := h2
      right
      intro hl
      apply lt_of_le_of_ne h2
      by_contra hn
      have hij : ((singleton h).join φsucΛ).getDual? i = j := by
        rw [@getDual?_eq_some_iff_mem]
        simp [join, singleton]
      simp only [hn, getDual?_getDual?_get_get, Option.some.injEq] at hij
      omega
    · simp only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none] at h2'
      simp [h2']

lemma join_singleton_left_signFinset_eq_filter {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (𝓕 |>ₛ ⟨φs.get, (singleton h).signFinset i j⟩)
    = (𝓕 |>ₛ ⟨φs.get, (join (singleton h) φsucΛ).signFinset i j⟩) *
      (𝓕 |>ₛ ⟨φs.get, ((singleton h).signFinset i j).filter (fun c =>
      (((join (singleton h) φsucΛ).getDual? c).isSome ∧
      ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
      (((join (singleton h) φsucΛ).getDual? c).get h1) < i)))⟩) := by
  conv_rhs =>
    left
    rw [join_singleton_signFinset_eq_filter]
  rw [mul_comm]
  exact (ofFinset_filter_mul_neg 𝓕.statesStatistic _ _ _).symm

/-- The difference in sign between `φsucΛ.sign` and the direct contribution of `φsucΛ` to
  `(join (singleton h) φsucΛ)`. -/
def joinSignRightExtra {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) : ℂ :=
    ∏ a, 𝓢(𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
    ((join (singleton h) φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
    (uncontractedListEmd (φsucΛ.sndFieldOfContract a))).filter
    (fun c => ¬ c ∈ (singleton h).uncontracted)⟩)

/-- The difference in sign between `(singleton h).sign` and the direct contribution of
  `(singleton h)` to `(join (singleton h) φsucΛ)`. -/
def joinSignLeftExtra {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) : ℂ :=
    𝓢(𝓕 |>ₛ φs[j], (𝓕 |>ₛ ⟨φs.get, ((singleton h).signFinset i j).filter (fun c =>
      (((join (singleton h) φsucΛ).getDual? c).isSome ∧
      ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
      (((join (singleton h) φsucΛ).getDual? c).get h1) < i)))⟩))

lemma join_singleton_sign_left {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (singleton h).sign = 𝓢(𝓕 |>ₛ φs[j],
    (𝓕 |>ₛ ⟨φs.get, (join (singleton h) φsucΛ).signFinset i j⟩)) * (joinSignLeftExtra h φsucΛ) := by
  rw [singleton_sign_expand]
  rw [join_singleton_left_signFinset_eq_filter h φsucΛ]
  rw [map_mul]
  rfl

lemma join_singleton_sign_right {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    φsucΛ.sign =
    (joinSignRightExtra h φsucΛ) *
    (∏ a, 𝓢(𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get,
      ((join (singleton h) φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
        (uncontractedListEmd (φsucΛ.sndFieldOfContract a)))⟩)) := by
  rw [sign_right_eq_prod_mul_prod]
  rfl

@[simp]
lemma join_singleton_getDual?_left {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).getDual? i = some j := by
  rw [@getDual?_eq_some_iff_mem]
  simp [singleton, join]

@[simp]
lemma join_singleton_getDual?_right {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).getDual? j = some i := by
  rw [@getDual?_eq_some_iff_mem]
  simp only [join, singleton, Finset.le_eq_subset, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_map, RelEmbedding.coe_toEmbedding]
  left
  exact Finset.pair_comm j i

lemma joinSignRightExtra_eq_i_j_finset_eq_if {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    joinSignRightExtra h φsucΛ = ∏ a,
    𝓢((𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a]),
    𝓕 |>ₛ ⟨φs.get, (if uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j ∧
        j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) ∧
        uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i then {j} else ∅)
        ∪ (if uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i ∧
        i < uncontractedListEmd (φsucΛ.sndFieldOfContract a) then {i} else ∅)⟩) := by
  rw [joinSignRightExtra]
  congr
  funext a
  congr
  rw [signFinset]
  rw [Finset.filter_comm]
  have h11 : (Finset.filter (fun c => c ∉ (singleton h).uncontracted) Finset.univ) = {i, j} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [@mem_uncontracted_iff_not_contracted]
    simp only [singleton, Finset.mem_singleton, forall_eq, Finset.mem_insert, not_or, not_and,
      Decidable.not_not]
    omega
  rw [h11]
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
  have hjneqfst := singleton_uncontractedEmd_neq_right h (φsucΛ.fstFieldOfContract a)
  have hjneqsnd := singleton_uncontractedEmd_neq_right h (φsucΛ.sndFieldOfContract a)
  have hineqfst := singleton_uncontractedEmd_neq_left h (φsucΛ.fstFieldOfContract a)
  have hineqsnd := singleton_uncontractedEmd_neq_left h (φsucΛ.sndFieldOfContract a)
  by_cases hj1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j
  · simp only [hj1, false_and, ↓reduceIte, Finset.not_mem_empty, false_or]
    have hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
    simp only [hi1, false_and, ↓reduceIte, Finset.not_mem_empty, iff_false, not_and, not_or,
      not_forall, not_lt]
    intro hxij h1 h2
    omega
  · have hj1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j := by
      omega
    by_cases hi1 : ¬ i < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
    · simp only [hi1, and_false, ↓reduceIte, Finset.not_mem_empty, or_false]
      have hj2 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
      simp only [hj2, false_and, and_false, ↓reduceIte, Finset.not_mem_empty, iff_false, not_and,
        not_or, not_forall, not_lt]
      intro hxij h1 h2
      omega
    · have hi1 : i < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by
        omega
      simp only [hj1, true_and, hi1, and_true]
      by_cases hi2 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i
      · simp only [hi2, and_false, ↓reduceIte, Finset.not_mem_empty, or_self, iff_false, not_and,
        not_or, not_forall, not_lt]
        by_cases hj3 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
        · omega
        · have hj4 : j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
          intro h
          rcases h with h | h
          · subst h
            omega
          · subst h
            simp only [join_singleton_getDual?_right, reduceCtorEq, not_false_eq_true,
              Option.get_some, Option.isSome_some, exists_const, true_and]
            omega
      · have hi2 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
        simp only [hi2, and_true, ↓reduceIte, Finset.mem_singleton]
        by_cases hj3 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
        · simp only [hj3, ↓reduceIte, Finset.not_mem_empty, false_or]
          apply Iff.intro
          · intro h
            omega
          · intro h
            subst h
            simp only [true_or, join_singleton_getDual?_left, reduceCtorEq, Option.isSome_some,
              Option.get_some, forall_const, false_or, true_and]
            omega
        · have hj3 : j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
          simp only [hj3, ↓reduceIte, Finset.mem_singleton]
          apply Iff.intro
          · intro h
            omega
          · intro h
            rcases h with h1 | h1
            · subst h1
              simp only [or_true, join_singleton_getDual?_right, reduceCtorEq, Option.isSome_some,
                Option.get_some, forall_const, false_or, true_and]
              omega
            · subst h1
              simp only [true_or, join_singleton_getDual?_left, reduceCtorEq, Option.isSome_some,
                Option.get_some, forall_const, false_or, true_and]
              omega

lemma joinSignLeftExtra_eq_joinSignRightExtra {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j) (hs : (𝓕 |>ₛ φs[i]) = (𝓕 |>ₛ φs[j]))
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    joinSignLeftExtra h φsucΛ = joinSignRightExtra h φsucΛ := by
  /- Simplifying joinSignLeftExtra. -/
  rw [joinSignLeftExtra]
  rw [ofFinset_eq_prod]
  rw [map_prod]
  let e2 : Fin φs.length ≃ {x // (((singleton h).join φsucΛ).getDual? x).isSome} ⊕
    {x // ¬ (((singleton h).join φsucΛ).getDual? x).isSome} := by
    exact (Equiv.sumCompl fun a => (((singleton h).join φsucΛ).getDual? a).isSome = true).symm
  rw [← e2.symm.prod_comp]
  simp only [Fin.getElem_fin, Fintype.prod_sum_type, instCommGroup]
  conv_lhs =>
    enter [2, 2, x]
    simp only [Equiv.symm_symm, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, e2]
    rw [if_neg (by
        simp only [Finset.mem_filter, mem_signFinset, not_and, not_forall, not_lt, and_imp]
        intro h1 h2
        have hx := x.2
        simp_all)]
  simp only [Finset.mem_filter, mem_signFinset, map_one, Finset.prod_const_one, mul_one]
  rw [← ((singleton h).join φsucΛ).sigmaContractedEquiv.prod_comp]
  erw [Finset.prod_sigma]
  conv_lhs =>
    enter [2, a]
    rw [prod_finset_eq_mul_fst_snd]
    simp [e2, sigmaContractedEquiv]
  rw [prod_join]
  rw [singleton_prod]
  simp only [join_fstFieldOfContract_joinLiftLeft, singleton_fstFieldOfContract,
    join_sndFieldOfContract_joinLift, singleton_sndFieldOfContract, lt_self_iff_false, and_false,
    ↓reduceIte, map_one, mul_one, join_fstFieldOfContract_joinLiftRight,
    join_sndFieldOfContract_joinLiftRight, getElem_uncontractedListEmd]
  rw [if_neg (by omega)]
  simp only [map_one, one_mul]
  /- Introducing joinSignRightExtra. -/
  rw [joinSignRightExtra_eq_i_j_finset_eq_if]
  congr
  funext a
  have hjneqsnd := singleton_uncontractedEmd_neq_right h (φsucΛ.sndFieldOfContract a)
  have hl : uncontractedListEmd (φsucΛ.fstFieldOfContract a) <
      uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by
    apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a
  by_cases hj1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j
  · have hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
    simp [hj1, hi1]
  · have hj1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j := by omega
    simp only [hj1, and_true, instCommGroup, Fin.getElem_fin, true_and]
    by_cases hi2 : ¬ i < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
    · have hi1 : ¬ i < uncontractedListEmd (φsucΛ.fstFieldOfContract a) := by omega
      have hj2 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
      simp [hi2, hj2, hi1]
    · have hi2 : i < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
      have hi2n : ¬ uncontractedListEmd (φsucΛ.sndFieldOfContract a) < i := by omega
      simp only [hi2n, and_false, ↓reduceIte, map_one, hi2, true_and, one_mul, and_true]
      by_cases hj2 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
      · simp only [hj2, false_and, ↓reduceIte, Finset.empty_union]
        have hj2 : uncontractedListEmd (φsucΛ.sndFieldOfContract a) < j:= by omega
        simp only [hj2, true_and]
        by_cases hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i
        · simp [hi1]
        · have hi1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
          simp only [hi1, ↓reduceIte, ofFinset_singleton, List.get_eq_getElem]
          erw [hs]
          exact exchangeSign_symm (𝓕|>ₛφs[↑j]) (𝓕|>ₛ[singleton h]ᵘᶜ[↑(φsucΛ.sndFieldOfContract a)])
      · simp only [not_lt, not_le] at hj2
        simp only [hj2, true_and]
        by_cases hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i
        · simp [hi1]
        · have hi1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
          simp only [hi1, and_true, ↓reduceIte]
          have hj2 : ¬ uncontractedListEmd (φsucΛ.sndFieldOfContract a) < j := by omega
          simp only [hj2, ↓reduceIte, map_one]
          rw [← ofFinset_union_disjoint]
          simp only [instCommGroup, ofFinset_singleton, List.get_eq_getElem, hs]
          erw [hs]
          simp only [Fin.getElem_fin, mul_self, map_one]
          simp only [Finset.disjoint_singleton_right, Finset.mem_singleton]
          exact Fin.ne_of_lt h

lemma join_sign_singleton {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j) (hs : (𝓕 |>ₛ φs[i]) = (𝓕 |>ₛ φs[j]))
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).sign = (singleton h).sign * φsucΛ.sign := by
  rw [join_singleton_sign_right]
  rw [join_singleton_sign_left h φsucΛ]
  rw [joinSignLeftExtra_eq_joinSignRightExtra h hs φsucΛ]
  rw [← mul_assoc]
  rw [mul_assoc _ _ (joinSignRightExtra h φsucΛ)]
  have h1 : (joinSignRightExtra h φsucΛ * joinSignRightExtra h φsucΛ) = 1 := by
    rw [← joinSignLeftExtra_eq_joinSignRightExtra h hs φsucΛ]
    simp [joinSignLeftExtra]
  simp only [instCommGroup, Fin.getElem_fin, h1, mul_one]
  rw [sign]
  rw [prod_join]
  congr
  · rw [singleton_prod]
    simp
  · funext a
    simp

lemma exists_contraction_pair_of_card_ge_zero {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (h : 0 < φsΛ.1.card) :
    ∃ a, a ∈ φsΛ.1 := by
  simpa using h

lemma exists_join_singleton_of_card_ge_zero {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (h : 0 < φsΛ.1.card) (hc : φsΛ.GradingCompliant) :
    ∃ (i j : Fin φs.length) (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length),
    φsΛ = join (singleton h) φsucΛ ∧ (𝓕 |>ₛ φs[i]) = (𝓕 |>ₛ φs[j])
    ∧ φsucΛ.GradingCompliant ∧ φsucΛ.1.card + 1 = φsΛ.1.card := by
  obtain ⟨a, ha⟩ := exists_contraction_pair_of_card_ge_zero φsΛ h
  use φsΛ.fstFieldOfContract ⟨a, ha⟩
  use φsΛ.sndFieldOfContract ⟨a, ha⟩
  use φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩
  let φsucΛ :
    WickContraction [singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩)]ᵘᶜ.length :=
    congr (by simp [← subContraction_singleton_eq_singleton])
    (φsΛ.quotContraction {a} (by simpa using ha))
  use φsucΛ
  simp only [Fin.getElem_fin]
  apply And.intro
  · have h1 := join_congr (subContraction_singleton_eq_singleton _ ⟨a, ha⟩).symm (φsucΛ := φsucΛ)
    simp only [id_eq, eq_mpr_eq_cast, h1, congr_trans_apply, congr_refl, φsucΛ]
    rw [join_sub_quot]
  · apply And.intro (hc ⟨a, ha⟩)
    apply And.intro
    · simp only [id_eq, eq_mpr_eq_cast, φsucΛ]
      rw [gradingCompliant_congr (φs' := [(φsΛ.subContraction {a} (by simpa using ha))]ᵘᶜ)]
      simp only [id_eq, eq_mpr_eq_cast, congr_trans_apply, congr_refl]
      exact quotContraction_gradingCompliant hc
      rw [← subContraction_singleton_eq_singleton]
    · simp only [id_eq, eq_mpr_eq_cast, card_congr, φsucΛ]
      have h1 := subContraction_card_plus_quotContraction_card_eq _ {a} (by simpa using ha)
      simp only [subContraction, Finset.card_singleton, id_eq, eq_mpr_eq_cast] at h1
      omega

lemma join_sign_induction {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (hc : φsΛ.GradingCompliant) :
    (n : ℕ) → (hn : φsΛ.1.card = n) →
    (join φsΛ φsucΛ).sign = φsΛ.sign * φsucΛ.sign
  | 0, hn => by
    rw [@card_zero_iff_empty] at hn
    subst hn
    simp only [empty_join, sign_empty, one_mul]
    apply sign_congr
    simp
  | Nat.succ n, hn => by
    obtain ⟨i, j, hij, φsucΛ', rfl, h1, h2, h3⟩ :=
      exists_join_singleton_of_card_ge_zero φsΛ (by simp [hn]) hc
    rw [join_assoc]
    rw [join_sign_singleton hij h1]
    rw [join_sign_singleton hij h1]
    have hn : φsucΛ'.1.card = n := by
      omega
    rw [join_sign_induction φsucΛ' (congr (by simp [join_uncontractedListGet]) φsucΛ) h2
      n hn]
    rw [mul_assoc]
    simp only [mul_eq_mul_left_iff]
    left
    left
    apply sign_congr
    exact join_uncontractedListGet (singleton hij) φsucΛ'

lemma join_sign {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (hc : φsΛ.GradingCompliant) :
    (join φsΛ φsucΛ).sign = φsΛ.sign * φsucΛ.sign := by
  exact join_sign_induction φsΛ φsucΛ hc (φsΛ).1.card rfl

lemma join_not_gradingCompliant_of_left_not_gradingCompliant {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length) (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length)
    (hc : ¬ φsΛ.GradingCompliant) : ¬ (join φsΛ φsucΛ).GradingCompliant := by
  simp_all only [GradingCompliant, Fin.getElem_fin, Subtype.forall, not_forall]
  obtain ⟨a, ha, ha2⟩ := hc
  use (joinLiftLeft (φsucΛ := φsucΛ) ⟨a, ha⟩).1
  use (joinLiftLeft (φsucΛ := φsucΛ) ⟨a, ha⟩).2
  simp only [Subtype.coe_eta, join_fstFieldOfContract_joinLiftLeft,
    join_sndFieldOfContract_joinLift]
  exact ha2

lemma join_sign_timeContract {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).sign • (join φsΛ φsucΛ).timeContract.1 =
    (φsΛ.sign • φsΛ.timeContract.1) * (φsucΛ.sign • φsucΛ.timeContract.1) := by
  rw [join_timeContract]
  by_cases h : φsΛ.GradingCompliant
  · rw [join_sign _ _ h]
    simp [smul_smul, mul_comm]
  · rw [timeContract_of_not_gradingCompliant _ _ h]
    simp

end WickContraction
