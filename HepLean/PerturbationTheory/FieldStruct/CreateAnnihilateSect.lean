/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.CreateAnnihilate
import HepLean.PerturbationTheory.CreateAnnihilate
/-!

# Creation and annihlation sections

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

/-- The sections in `𝓕.CreateAnnihilateStates` over a list `φs : List 𝓕.States`.
  In terms of physics, given some fields `φ₁...φₙ`, the different ways one can associate
  each field as a `creation` or an `annilation` operator. E.g. the number of terms
  `φ₁⁰φ₂¹...φₙ⁰` `φ₁¹φ₂¹...φₙ⁰` etc. If some fields are exclusively creation or annhilation
  operators at this point (e.g. ansymptotic states) this is accounted for. -/
def CreateAnnihilateSect (φs : List 𝓕.States) : Type :=
  {ψs : List 𝓕.CreateAnnihilateStates //
    List.map 𝓕.createAnnihilateStatesToStates ψs = φs}
  -- Π i, 𝓕.statesToCreateAnnihilateType (φs.get i)

namespace CreateAnnihilateSect

variable {𝓕 : FieldStruct} {φs : List 𝓕.States}

@[simp]
lemma length_eq (ψs : CreateAnnihilateSect φs) : ψs.1.length = φs.length := by
  simpa using congrArg List.length ψs.2

/-- The tail of a section for `φs`. -/
def tail : {φs : List 𝓕.States} → (ψs : CreateAnnihilateSect φs) → CreateAnnihilateSect φs.tail
  | [], ⟨[], h⟩ => ⟨[], h⟩
  | φ :: φs, ⟨[], h⟩ => False.elim (by simp at h)
  | φ :: φs, ⟨ψ :: ψs, h⟩ => ⟨ψs, by rw [List.map_cons, List.cons.injEq] at h; exact h.2⟩

lemma head_state_eq {φ : 𝓕.States} : (ψs : CreateAnnihilateSect (φ :: φs)) →
    (ψs.1.head (by simp [← List.length_pos_iff_ne_nil])).1 = φ
  | ⟨[], h⟩ => False.elim (by simp at h)
  | ⟨ψ :: ψs, h⟩ => by
    simp at h
    exact h.1

/-- The head of a section for `φ :: φs` as an element in `𝓕.statesToCreateAnnihilateType φ`. -/
def head : {φ : 𝓕.States} → (ψs : CreateAnnihilateSect (φ :: φs)) →
    𝓕.statesToCreateAnnihilateType φ
  | φ, ⟨[], h⟩ => False.elim (by simp at h)
  | φ, ⟨ψ :: ψs, h⟩ => 𝓕.statesToCreateAnnihilateTypeCongr (by
    simpa using head_state_eq ⟨ψ :: ψs, h⟩) ψ.2

lemma eq_head_cons_tail {φ : 𝓕.States} {ψs : CreateAnnihilateSect (φ :: φs)} :
    ψs.1 = ⟨φ, head ψs⟩ :: ψs.tail.1 := by
  match ψs with
  | ⟨[], h⟩ => exact False.elim (by simp at h)
  | ⟨ψ :: ψs, h⟩ =>
    have h2 := head_state_eq ⟨ψ :: ψs, h⟩
    simp at h2
    subst h2
    rfl

/-- The creation of a section from for `φ : φs` from a section for `φs` and a
  element of `𝓕.statesToCreateAnnihilateType φ`. -/
def cons {φ : 𝓕.States} (ψ : 𝓕.statesToCreateAnnihilateType φ) (ψs : CreateAnnihilateSect φs) :
    CreateAnnihilateSect (φ :: φs) := ⟨⟨φ, ψ⟩ :: ψs.1, by
  simp [List.map_cons, ψs.2]⟩

/-- The creation and annihlation sections for a singleton list is given by
  a choice of `𝓕.statesToCreateAnnihilateType φ`. If `φ` is a asymptotic state
  there is no choice here, else there are two choices. -/
def singletonEquiv {φ : 𝓕.States} : CreateAnnihilateSect [φ] ≃
    𝓕.statesToCreateAnnihilateType φ where
  toFun ψs := ψs.head
  invFun ψ := ⟨[⟨φ, ψ⟩], by simp⟩
  left_inv ψs := by
    apply Subtype.ext
    simp
    have h1 := eq_head_cons_tail (ψs := ψs)
    rw [h1]
    have h2 := ψs.tail.2
    simp at h2
    simp [h2]
  right_inv ψ := by
    simp [head]
    rfl

/-- An equivalence seperating the head of a creation and annhilation section
  from the tail. -/
def consEquiv {φ : 𝓕.States} {φs : List 𝓕.States} : CreateAnnihilateSect (φ :: φs) ≃
    𝓕.statesToCreateAnnihilateType φ × CreateAnnihilateSect φs where
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

/-- The equivalence between `CreateAnnihilateSect φs` and
  `CreateAnnihilateSect φs'` induced by an equality `φs = φs'`. -/
def congr : {φs φs' : List 𝓕.States} → (h : φs = φs') →
    CreateAnnihilateSect φs ≃ CreateAnnihilateSect φs'
  | _, _, rfl => Equiv.refl _

@[simp]
lemma congr_fst {φs φs' : List 𝓕.States} (h : φs = φs') (ψs : CreateAnnihilateSect φs) :
    (congr h ψs).1 = ψs.1 := by
  cases h
  rfl

/-- Returns the first `n` elements of a section and its underlying list. -/
def take (n : ℕ) (ψs : CreateAnnihilateSect φs) : CreateAnnihilateSect (φs.take n) :=
  ⟨ψs.1.take n, by simp [ψs.2]⟩

/-- Removes the first `n` elements of a section and its underlying list. -/
def drop (n : ℕ) (ψs : CreateAnnihilateSect φs) : CreateAnnihilateSect (φs.drop n) :=
  ⟨ψs.1.drop n, by simp [ψs.2]⟩

/-- Appends two sections and their underlying lists. -/
def append {φs φs' : List 𝓕.States} (ψs : CreateAnnihilateSect φs)
    (ψs' : CreateAnnihilateSect φs') : CreateAnnihilateSect (φs ++ φs') :=
  ⟨ψs.1 ++ ψs'.1, by simp [ψs.2, ψs'.2]⟩

@[simp]
lemma take_append_drop {n : ℕ} (ψs : CreateAnnihilateSect φs) :
    append (take n ψs) (drop n ψs) = congr (List.take_append_drop n φs).symm ψs := by
  apply Subtype.ext
  simp [take, drop, append]

@[simp]
lemma congr_append {φs1 φs1' φs2 φs2' : List 𝓕.States}
    (h1 : φs1 = φs1') (h2 : φs2 = φs2')
    (ψs1 : CreateAnnihilateSect φs1) (ψs2 : CreateAnnihilateSect φs2) :
    (append (congr h1 ψs1) (congr h2 ψs2)) = congr (by rw [h1, h2]) (append ψs1 ψs2) := by
  subst h1 h2
  rfl

@[simp]
lemma take_left {φs φs' : List 𝓕.States} (ψs : CreateAnnihilateSect φs)
    (ψs' : CreateAnnihilateSect φs') :
    take φs.length (ψs.append ψs') = congr (by simp) ψs := by
  apply Subtype.ext
  simp [take, append]

@[simp]
lemma drop_left {φs φs' : List 𝓕.States} (ψs : CreateAnnihilateSect φs)
    (ψs' : CreateAnnihilateSect φs') :
    drop φs.length (ψs.append ψs') = congr (by simp) ψs' := by
  apply Subtype.ext
  simp [drop, append]

/-- The equivalence between `CreateAnnihilateSect (φs ++ φs')` and
  `CreateAnnihilateSect φs × CreateAnnihilateSect φs` formed by `append`, `take`
  and `drop` and their interrelationship. -/
def appendEquiv {φs φs' : List 𝓕.States} : CreateAnnihilateSect (φs ++ φs') ≃
    CreateAnnihilateSect φs × CreateAnnihilateSect φs' where
  toFun ψs := (congr (List.take_left φs φs') (take φs.length ψs),
    congr (List.drop_left φs φs') (drop φs.length ψs))
  invFun ψsψs' := append ψsψs'.1 ψsψs'.2
  left_inv ψs := by
    apply Subtype.ext
    simp
  right_inv ψsψs' := by
    match ψsψs' with
    | (ψs, ψs') =>
    simp
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
def eraseIdx (n : ℕ) (ψs : CreateAnnihilateSect φs) : CreateAnnihilateSect (φs.eraseIdx n) :=
  ⟨ψs.1.eraseIdx n, by simp [ψs.2]⟩

/-- The equivalence formed by extracting an element from a section. -/
def eraseIdxEquiv (n : ℕ) (φs : List 𝓕.States) (hn : n < φs.length) :
    CreateAnnihilateSect φs ≃ 𝓕.statesToCreateAnnihilateType φs[n] ×
    CreateAnnihilateSect (φs.eraseIdx n) :=
  (congr (by simp only [List.take_concat_get', List.take_append_drop])).trans <|
  appendEquiv.trans <|
  (Equiv.prodCongr (appendEquiv.trans (Equiv.prodComm _ _)) (Equiv.refl _)).trans <|
  (Equiv.prodAssoc _ _ _).trans <|
  Equiv.prodCongr singletonEquiv <|
  appendEquiv.symm.trans <|
  congr (List.eraseIdx_eq_take_drop_succ φs n).symm

@[simp]
lemma eraseIdxEquiv_apply_snd {n : ℕ} (ψs : CreateAnnihilateSect φs) (hn : n < φs.length) :
    (eraseIdxEquiv n φs hn ψs).snd = eraseIdx n ψs := by
  apply Subtype.ext
  simp only [eraseIdxEquiv, appendEquiv, take, List.take_concat_get', List.length_take, drop,
    append, Equiv.trans_apply, Equiv.coe_fn_mk, congr_fst, Equiv.prodCongr_apply, Equiv.coe_trans,
    Equiv.coe_prodComm, Equiv.coe_refl, Prod.map_apply, Function.comp_apply, Prod.swap_prod_mk,
    id_eq, Equiv.prodAssoc_apply, Equiv.coe_fn_symm_mk, eraseIdx]
  rw [Nat.min_eq_left (Nat.le_of_succ_le hn), Nat.min_eq_left hn, List.take_take]
  simp only [Nat.succ_eq_add_one, le_add_iff_nonneg_right, zero_le, inf_of_le_left]
  exact Eq.symm (List.eraseIdx_eq_take_drop_succ ψs.1 n)

end CreateAnnihilateSect

end FieldStruct
