/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.CrAnStates
/-!

# Creation and annihlation sections

This module defines creation and annihilation sections, which represent different ways to associate
fields with creation or annihilation operators.

## Main definitions

- `CrAnSection φs` : Represents sections in `𝓕.CrAnStates` over a list of states `φs`.
  Given fields `φ₁...φₙ`, this captures all possible ways to assign each field as either a creation
  or annihilation operator.

- `head`, `tail` : Access the first element and remaining elements of a section

- `cons` : Constructs a new section by prepending a creation/annihilation state

- Various equivalences:
  * `nilEquiv` : Empty sections
  * `singletonEquiv` : Sections over single elements
  * `consEquiv` : Separates head and tail
  * `appendEquiv` : Splits sections at a given point

All sections form finite types and support operations like taking/dropping elements and
concatenation while preserving the relationship between states and their operator assignments.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

/-- The sections in `𝓕.CrAnStates` over a list `φs : List 𝓕.States`.
  In terms of physics, given some fields `φ₁...φₙ`, the different ways one can associate
  each field as a `creation` or an `annilation` operator. E.g. the number of terms
  `φ₁⁰φ₂¹...φₙ⁰` `φ₁¹φ₂¹...φₙ⁰` etc. If some fields are exclusively creation or annhilation
  operators at this point (e.g. ansymptotic states) this is accounted for. -/
def CrAnSection (φs : List 𝓕.States) : Type :=
  {ψs : List 𝓕.CrAnStates //
    List.map 𝓕.crAnStatesToStates ψs = φs}
  -- Π i, 𝓕.statesToCreateAnnihilateType (φs.get i)

namespace CrAnSection
open FieldStatistic
variable {𝓕 : FieldSpecification} {φs : List 𝓕.States}

@[simp]
lemma length_eq (ψs : CrAnSection φs) : ψs.1.length = φs.length := by
  simpa using congrArg List.length ψs.2

/-- The tail of a section for `φs`. -/
def tail : {φs : List 𝓕.States} → (ψs : CrAnSection φs) → CrAnSection φs.tail
  | [], ⟨[], h⟩ => ⟨[], h⟩
  | φ :: φs, ⟨[], h⟩ => False.elim (by simp at h)
  | φ :: φs, ⟨ψ :: ψs, h⟩ => ⟨ψs, by rw [List.map_cons, List.cons.injEq] at h; exact h.2⟩

lemma head_state_eq {φ : 𝓕.States} : (ψs : CrAnSection (φ :: φs)) →
    (ψs.1.head (by simp [← List.length_pos_iff_ne_nil])).1 = φ
  | ⟨[], h⟩ => False.elim (by simp at h)
  | ⟨ψ :: ψs, h⟩ => by
    simp only [List.map_cons, List.cons.injEq] at h
    exact h.1

lemma statistics_eq_state_statistics (ψs : CrAnSection φs) :
    (𝓕 |>ₛ ψs.1) = 𝓕 |>ₛ φs := by
  erw [FieldStatistic.ofList_eq_prod, FieldStatistic.ofList_eq_prod, crAnStatistics]
  rw [← List.map_comp_map, Function.comp_apply, ψs.2]

lemma take_statistics_eq_take_state_statistics (ψs : CrAnSection φs) n :
    (𝓕 |>ₛ (ψs.1.take n)) = 𝓕 |>ₛ (φs.take n) := by
  erw [FieldStatistic.ofList_eq_prod, FieldStatistic.ofList_eq_prod, crAnStatistics]
  simp only [instCommGroup, List.map_take]
  rw [← List.map_comp_map, Function.comp_apply, ψs.2]

/-- The head of a section for `φ :: φs` as an element in `𝓕.statesToCreateAnnihilateType φ`. -/
def head : {φ : 𝓕.States} → (ψs : CrAnSection (φ :: φs)) →
    𝓕.statesToCrAnType φ
  | φ, ⟨[], h⟩ => False.elim (by simp at h)
  | φ, ⟨ψ :: ψs, h⟩ => 𝓕.statesToCreateAnnihilateTypeCongr (by
    simpa using head_state_eq ⟨ψ :: ψs, h⟩) ψ.2

lemma eq_head_cons_tail {φ : 𝓕.States} {ψs : CrAnSection (φ :: φs)} :
    ψs.1 = ⟨φ, head ψs⟩ :: ψs.tail.1 := by
  match ψs with
  | ⟨[], h⟩ => exact False.elim (by simp at h)
  | ⟨ψ :: ψs, h⟩ =>
    have h2 := head_state_eq ⟨ψ :: ψs, h⟩
    simp only [List.head_cons] at h2
    subst h2
    rfl

/-- The creation of a section from for `φ : φs` from a section for `φs` and a
  element of `𝓕.statesToCreateAnnihilateType φ`. -/
def cons {φ : 𝓕.States} (ψ : 𝓕.statesToCrAnType φ) (ψs : CrAnSection φs) :
    CrAnSection (φ :: φs) := ⟨⟨φ, ψ⟩ :: ψs.1, by
  simp [List.map_cons, ψs.2]⟩

/-- For the empty list of states there is only one `CrAnSection`. Corresponding to the
  empty list of `CrAnStates`. -/
def nilEquiv : CrAnSection (𝓕 := 𝓕) [] ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], rfl⟩
  left_inv ψs := Subtype.ext <| by
    have h2 := ψs.2
    simp only [List.map_eq_nil_iff] at h2
    simp [h2]
  right_inv _ := by
    simp

/-- The creation and annihlation sections for a singleton list is given by
  a choice of `𝓕.statesToCreateAnnihilateType φ`. If `φ` is a asymptotic state
  there is no choice here, else there are two choices. -/
def singletonEquiv {φ : 𝓕.States} : CrAnSection [φ] ≃
    𝓕.statesToCrAnType φ where
  toFun ψs := ψs.head
  invFun ψ := ⟨[⟨φ, ψ⟩], by simp⟩
  left_inv ψs := by
    apply Subtype.ext
    simp only
    have h1 := eq_head_cons_tail (ψs := ψs)
    rw [h1]
    have h2 := ψs.tail.2
    simp only [List.tail_cons, List.map_eq_nil_iff] at h2
    simp [h2]
  right_inv ψ := by
    simp only [head]
    rfl

/-- An equivalence seperating the head of a creation and annhilation section
  from the tail. -/
def consEquiv {φ : 𝓕.States} {φs : List 𝓕.States} : CrAnSection (φ :: φs) ≃
    𝓕.statesToCrAnType φ × CrAnSection φs where
  toFun ψs := ⟨ψs.head, ψs.tail⟩
  invFun ψψs :=
    match ψψs with
    | (ψ, ψs) => cons ψ ψs
  left_inv ψs := by
    apply Subtype.ext
    exact Eq.symm eq_head_cons_tail
  right_inv ψψs := by
    match ψψs with
    | (ψ, ψs) => rfl

/-- The instance of a finite type on `CrAnSection`s defined recursively through
  `consEquiv`. -/
instance fintype : (φs : List 𝓕.States) → Fintype (CrAnSection φs)
  | [] => Fintype.ofEquiv _ nilEquiv.symm
  | _ :: φs =>
    haveI : Fintype (CrAnSection φs) := fintype φs
    Fintype.ofEquiv _ consEquiv.symm

@[simp]
lemma sum_nil (f : CrAnSection (𝓕 := 𝓕) [] → M) [AddCommMonoid M] :
    ∑ (s : CrAnSection []), f s = f ⟨[], rfl⟩ := by
  rw [← nilEquiv.symm.sum_comp]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
  rfl

lemma sum_cons (f : CrAnSection (φ :: φs) → M) [AddCommMonoid M] :
    ∑ (s : CrAnSection (φ :: φs)), f s = ∑ (a : 𝓕.statesToCrAnType φ),
    ∑ (s : CrAnSection φs), f (cons a s) := by
  rw [← consEquiv.symm.sum_comp, Fintype.sum_prod_type]
  rfl

lemma sum_over_length {s : CrAnSection φs} (f : Fin s.1.length → M)
    [AddCommMonoid M] : ∑ (n : Fin s.1.length), f n =
    ∑ (n : Fin φs.length), f (Fin.cast (length_eq s).symm n) := by
  rw [← (finCongr (length_eq s)).sum_comp]
  rfl

/-- The equivalence between `CrAnSection φs` and
  `CrAnSection φs'` induced by an equality `φs = φs'`. -/
def congr : {φs φs' : List 𝓕.States} → (h : φs = φs') →
    CrAnSection φs ≃ CrAnSection φs'
  | _, _, rfl => Equiv.refl _

@[simp]
lemma congr_fst {φs φs' : List 𝓕.States} (h : φs = φs') (ψs : CrAnSection φs) :
    (congr h ψs).1 = ψs.1 := by
  cases h
  rfl

@[simp]
lemma congr_symm {φs φs' : List 𝓕.States} (h : φs = φs') :
    (congr h).symm = congr h.symm := by
  cases h
  rfl

@[simp]
lemma congr_trans_apply {φs φs' φs'' : List 𝓕.States} (h1 : φs = φs') (h2 : φs' = φs'')
    (ψs : CrAnSection φs) :
    (congr h2 (congr h1 ψs)) = congr (by rw [h1, h2]) ψs := by
  subst h1 h2
  rfl

/-- Returns the first `n` elements of a section and its underlying list. -/
def take (n : ℕ) (ψs : CrAnSection φs) : CrAnSection (φs.take n) :=
  ⟨ψs.1.take n, by simp [ψs.2]⟩

@[simp]
lemma take_congr {φs φs' : List 𝓕.States} (h : φs = φs') (n : ℕ)
    (ψs : CrAnSection φs) :
    (take n (congr h ψs)) = congr (by rw [h]) (take n ψs) := by
  subst h
  rfl

/-- Removes the first `n` elements of a section and its underlying list. -/
def drop (n : ℕ) (ψs : CrAnSection φs) : CrAnSection (φs.drop n) :=
  ⟨ψs.1.drop n, by simp [ψs.2]⟩

@[simp]
lemma drop_congr {φs φs' : List 𝓕.States} (h : φs = φs') (n : ℕ)
    (ψs : CrAnSection φs) :
    (drop n (congr h ψs)) = congr (by rw [h]) (drop n ψs) := by
  subst h
  rfl

/-- Appends two sections and their underlying lists. -/
def append {φs φs' : List 𝓕.States} (ψs : CrAnSection φs)
    (ψs' : CrAnSection φs') : CrAnSection (φs ++ φs') :=
  ⟨ψs.1 ++ ψs'.1, by simp [ψs.2, ψs'.2]⟩

lemma append_assoc {φs φs' φs'' : List 𝓕.States} (ψs : CrAnSection φs)
    (ψs' : CrAnSection φs') (ψs'' : CrAnSection φs'') :
    append ψs (append ψs' ψs'') = congr (by simp) (append (append ψs ψs') ψs'') := by
  apply Subtype.ext
  simp [append]

lemma append_assoc' {φs φs' φs'' : List 𝓕.States} (ψs : CrAnSection φs)
    (ψs' : CrAnSection φs') (ψs'' : CrAnSection φs'') :
    (append (append ψs ψs') ψs'') = congr (by simp) (append ψs (append ψs' ψs'')) := by
  apply Subtype.ext
  simp [append]

lemma singletonEquiv_append_eq_cons {φs : List 𝓕.States} {φ : 𝓕.States}
    (ψs : CrAnSection φs) (ψ : 𝓕.statesToCrAnType φ) :
    append (singletonEquiv.symm ψ) ψs = cons ψ ψs := by
  apply Subtype.ext
  simp [append, cons, singletonEquiv]

@[simp]
lemma take_append_drop {n : ℕ} (ψs : CrAnSection φs) :
    append (take n ψs) (drop n ψs) = congr (List.take_append_drop n φs).symm ψs := by
  apply Subtype.ext
  simp [take, drop, append]

lemma congr_append {φs1 φs1' φs2 φs2' : List 𝓕.States} (h1 : φs1 = φs1') (h2 : φs2 = φs2')
    (ψs1 : CrAnSection φs1) (ψs2 : CrAnSection φs2) :
    (append (congr h1 ψs1) (congr h2 ψs2)) = congr (by rw [h1, h2]) (append ψs1 ψs2) := by
  subst h1 h2
  rfl

@[simp]
lemma congr_fst_append {φs1 φs1' φs2 : List 𝓕.States} (h1 : φs1 = φs1')
    (ψs1 : CrAnSection φs1) (ψs2 : CrAnSection φs2) :
    (append (congr h1 ψs1) (ψs2)) = congr (by rw [h1]) (append ψs1 ψs2) := by
  subst h1
  rfl

@[simp]
lemma congr_snd_append {φs1 φs2 φs2' : List 𝓕.States} (h2 : φs2 = φs2')
    (ψs1 : CrAnSection φs1) (ψs2 : CrAnSection φs2) :
    (append ψs1 (congr h2 ψs2)) = congr (by rw [h2]) (append ψs1 ψs2) := by
  subst h2
  rfl

@[simp]
lemma take_left {φs φs' : List 𝓕.States} (ψs : CrAnSection φs)
    (ψs' : CrAnSection φs') :
    take φs.length (ψs.append ψs') = congr (by simp) ψs := by
  apply Subtype.ext
  simp [take, append]

@[simp]
lemma drop_left {φs φs' : List 𝓕.States} (ψs : CrAnSection φs)
    (ψs' : CrAnSection φs') :
    drop φs.length (ψs.append ψs') = congr (by simp) ψs' := by
  apply Subtype.ext
  simp [drop, append]

/-- The equivalence between `CrAnSection (φs ++ φs')` and
  `CrAnSection φs × CrAnSection φs` formed by `append`, `take`
  and `drop` and their interrelationship. -/
def appendEquiv {φs φs' : List 𝓕.States} : CrAnSection (φs ++ φs') ≃
    CrAnSection φs × CrAnSection φs' where
  toFun ψs := (congr (List.take_left φs φs') (take φs.length ψs),
    congr (List.drop_left φs φs') (drop φs.length ψs))
  invFun ψsψs' := append ψsψs'.1 ψsψs'.2
  left_inv ψs := by
    apply Subtype.ext
    simp
  right_inv ψsψs' := by
    match ψsψs' with
    | (ψs, ψs') =>
    simp only [take_left, drop_left, Prod.mk.injEq]
    refine And.intro (Subtype.ext ?_) (Subtype.ext ?_)
    · simp
    · simp

@[simp]
lemma _root_.List.map_eraseIdx {α β : Type} (f : α → β) : (l : List α) → (n : ℕ) →
    List.map f (l.eraseIdx n) = (List.map f l).eraseIdx n
  | [], _ => rfl
  | a :: l, 0 => rfl
  | a :: l, n+1 => by
    simp only [List.eraseIdx, List.map_cons, List.cons.injEq, true_and]
    exact List.map_eraseIdx f l n

/-- Erasing an element from a section and it's underlying list. -/
def eraseIdx (n : ℕ) (ψs : CrAnSection φs) : CrAnSection (φs.eraseIdx n) :=
  ⟨ψs.1.eraseIdx n, by simp [ψs.2]⟩

/-- The equivalence formed by extracting an element from a section. -/
def eraseIdxEquiv (n : ℕ) (φs : List 𝓕.States) (hn : n < φs.length) :
    CrAnSection φs ≃ 𝓕.statesToCrAnType φs[n] ×
    CrAnSection (φs.eraseIdx n) :=
  (congr (by simp only [List.take_concat_get', List.take_append_drop])).trans <|
  appendEquiv.trans <|
  (Equiv.prodCongr (appendEquiv.trans (Equiv.prodComm _ _)) (Equiv.refl _)).trans <|
  (Equiv.prodAssoc _ _ _).trans <|
  Equiv.prodCongr singletonEquiv <|
  appendEquiv.symm.trans <|
  congr (List.eraseIdx_eq_take_drop_succ φs n).symm

@[simp]
lemma eraseIdxEquiv_apply_snd {n : ℕ} (ψs : CrAnSection φs) (hn : n < φs.length) :
    (eraseIdxEquiv n φs hn ψs).snd = eraseIdx n ψs := by
  apply Subtype.ext
  simp only [eraseIdxEquiv, appendEquiv, take, List.take_concat_get', List.length_take, drop,
    append, Equiv.trans_apply, Equiv.coe_fn_mk, congr_fst, Equiv.prodCongr_apply, Equiv.coe_trans,
    Equiv.coe_prodComm, Equiv.coe_refl, Prod.map_apply, Function.comp_apply, Prod.swap_prod_mk,
    id_eq, Equiv.prodAssoc_apply, Equiv.coe_fn_symm_mk, eraseIdx]
  rw [Nat.min_eq_left (Nat.le_of_succ_le hn), Nat.min_eq_left hn, List.take_take]
  simp only [Nat.succ_eq_add_one, le_add_iff_nonneg_right, zero_le, inf_of_le_left]
  exact Eq.symm (List.eraseIdx_eq_take_drop_succ ψs.1 n)

lemma eraseIdxEquiv_symm_eq_take_cons_drop {n : ℕ} (φs : List 𝓕.States) (hn : n < φs.length)
    (a : 𝓕.statesToCrAnType φs[n]) (s : CrAnSection (φs.eraseIdx n)) :
    (eraseIdxEquiv n φs hn).symm ⟨a, s⟩ =
    congr (by
    rw [HepLean.List.take_eraseIdx_same, HepLean.List.drop_eraseIdx_succ]
    conv_rhs => rw [← List.take_append_drop n φs]) (append (take n s) (cons a (drop n s))) := by
  simp only [eraseIdxEquiv, appendEquiv, Equiv.symm_trans_apply, congr_symm, Equiv.prodCongr_symm,
    Equiv.refl_symm, Equiv.prodCongr_apply, Prod.map_apply, Equiv.symm_symm, Equiv.coe_fn_mk,
    take_congr, congr_trans_apply, drop_congr, Equiv.prodAssoc_symm_apply, Equiv.coe_refl,
    Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk, Equiv.coe_fn_symm_mk,
    congr_fst_append, id_eq, congr_snd_append]
  rw [append_assoc', singletonEquiv_append_eq_cons]
  simp only [List.singleton_append, congr_trans_apply]
  apply Subtype.ext
  simp only [congr_fst]
  have hn : (List.take n φs).length = n := by
    rw [@List.length_take]
    simp only [inf_eq_left]
    exact Nat.le_of_succ_le hn
  rw [hn]

@[simp]
lemma eraseIdxEquiv_symm_getElem {n : ℕ} (φs : List 𝓕.States) (hn : n < φs.length)
    (a : 𝓕.statesToCrAnType φs[n]) (s : CrAnSection (φs.eraseIdx n)) :
    getElem ((eraseIdxEquiv n φs hn).symm ⟨a,s⟩).1 n
    (by rw [length_eq]; exact hn) = ⟨φs[n], a⟩ := by
  rw [eraseIdxEquiv_symm_eq_take_cons_drop]
  simp only [append, take, cons, drop, congr_fst]
  rw [List.getElem_append]
  simp only [List.length_take, length_eq, lt_inf_iff, lt_self_iff_false, false_and, ↓reduceDIte]
  have h0 : n ⊓ (φs.eraseIdx n).length = n := by
    simp only [inf_eq_left]
    rw [← HepLean.List.eraseIdx_length _ ⟨n, hn⟩] at hn
    exact Nat.le_of_lt_succ hn
  simp [h0]

@[simp]
lemma eraseIdxEquiv_symm_eraseIdx {n : ℕ} (φs : List 𝓕.States) (hn : n < φs.length)
    (a : 𝓕.statesToCrAnType φs[n]) (s : CrAnSection (φs.eraseIdx n)) :
    ((eraseIdxEquiv n φs hn).symm ⟨a, s⟩).1.eraseIdx n = s.1 := by
  change (((eraseIdxEquiv n φs hn).symm ⟨a, s⟩).eraseIdx n).1 = _
  rw [← eraseIdxEquiv_apply_snd _ hn]
  simp

lemma sum_eraseIdxEquiv (n : ℕ) (φs : List 𝓕.States) (hn : n < φs.length)
    (f : CrAnSection φs → M) [AddCommMonoid M] : ∑ (s : CrAnSection φs), f s =
    ∑ (a : 𝓕.statesToCrAnType φs[n]), ∑ (s : CrAnSection (φs.eraseIdx n)),
    f ((eraseIdxEquiv n φs hn).symm ⟨a, s⟩) := by
  rw [← (eraseIdxEquiv n φs hn).symm.sum_comp]
  rw [Fintype.sum_prod_type]

end CrAnSection

end FieldSpecification
