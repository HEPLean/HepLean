/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.OperatorMap
/-!

# Contractions of a list of fields

-/

namespace Wick

open HepLean.List
open FieldStatistic

variable {𝓕 : Type}

/-- Given a list of fields `φs`, the type of pairwise-contractions associated with `φs`
  which have the list `φsᵤₙ` uncontracted. -/
inductive ContractionsAux : (φs : List 𝓕) → (φsᵤₙ : List 𝓕) → Type
  | nil : ContractionsAux [] []
  | cons {φs : List 𝓕} {φsᵤₙ : List 𝓕} {φ : 𝓕} (i : Option (Fin φsᵤₙ.length)) :
    ContractionsAux φs φsᵤₙ → ContractionsAux (φ :: φs) (optionEraseZ φsᵤₙ φ i)

/-- Given a list of fields `l`, the type of pairwise-contractions associated with `l`. -/
def Contractions (φs : List 𝓕) : Type := Σ aux, ContractionsAux φs aux

namespace Contractions

variable {l : List 𝓕} (c : Contractions l)

/-- The list of uncontracted fields. -/
def normalize : List 𝓕 := c.1

lemma contractions_nil (a : Contractions ([] : List 𝓕)) : a = ⟨[], ContractionsAux.nil⟩ := by
  cases a
  rename_i aux c
  cases c
  rfl

def embedUncontracted {l : List 𝓕} (c : Contractions l) : Fin c.normalize.length → Fin l.length :=
  match l, c with
  | [], ⟨[], ContractionsAux.nil⟩ => Fin.elim0
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) none c⟩ =>
    Fin.cons ⟨0, Nat.zero_lt_succ φs.length⟩ (Fin.succ ∘ (embedUncontracted ⟨aux, c⟩))
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some n) c⟩ => by
    let lc := embedUncontracted ⟨aux, c⟩
    refine Fin.succ ∘ lc ∘ Fin.cast ?_ ∘ Fin.succAbove ⟨n, by
      rw [normalize, optionEraseZ_some_length]
      omega⟩
    simp only [normalize, optionEraseZ_some_length]
    have hq : aux.length ≠ 0 := by
      by_contra hn
      rw [hn] at n
      exact Fin.elim0 n
    omega

lemma embedUncontracted_injective  {l : List 𝓕} (c : Contractions l) :
    Function.Injective c.embedUncontracted := by
  match l, c with
  | [], ⟨[], ContractionsAux.nil⟩ =>
    dsimp [embedUncontracted]
    intro i
    exact Fin.elim0 i
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) none c⟩ =>
    dsimp [embedUncontracted]
    refine Fin.cons_injective_iff.mpr ?_
    apply And.intro
    · simp only [Set.mem_range, Function.comp_apply, not_exists]
      exact fun x => Fin.succ_ne_zero (embedUncontracted ⟨aux, c⟩ x)
    · exact Function.Injective.comp (Fin.succ_injective φs.length)
        (embedUncontracted_injective ⟨aux, c⟩)
  |  φ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some i) c⟩ =>
      dsimp [embedUncontracted]
      refine Function.Injective.comp (Fin.succ_injective φs.length) ?hf
      refine Function.Injective.comp (embedUncontracted_injective ⟨aux, c⟩) ?hf.hf
      refine Function.Injective.comp (Fin.cast_injective (embedUncontracted.proof_5 φ φs aux i c))
        Fin.succAbove_right_injective



/-- Establishes uniqueness of contractions for a single field, showing that any contraction
  of a single field must be equivalent to the trivial contraction with no pairing. -/
lemma contractions_single {i : 𝓕} (a : Contractions [i]) : a =
    ⟨[i], ContractionsAux.cons none ContractionsAux.nil⟩ := by
  cases a
  rename_i aux c
  cases c
  rename_i aux' c'
  cases c'
  cases aux'
  simp only [List.length_nil, optionEraseZ]
  rename_i x
  exact Fin.elim0 x

/--
  This function provides an equivalence between the type of contractions for an empty list of fields
  and the unit type, indicating that there is only one possible contraction for an empty list.
-/
def nilEquiv : Contractions ([] : List 𝓕) ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨[], ContractionsAux.nil⟩
  left_inv a := Eq.symm (contractions_nil a)
  right_inv _ := rfl

/-- The equivalence between contractions of `a :: l` and contractions of
  `Contractions l` paired with an optional element of `Fin (c.normalize).length` specifying
  what `a` contracts with if any. -/
def consEquiv {φ : 𝓕} {φs : List 𝓕} :
    Contractions (φ :: φs) ≃ (c : Contractions φs) × Option (Fin c.normalize.length) where
  toFun c :=
    match c with
    | ⟨aux, c⟩ =>
    match c with
    | ContractionsAux.cons (φsᵤₙ := aux') i c => ⟨⟨aux', c⟩, i⟩
  invFun ci :=
    ⟨(optionEraseZ (ci.fst.normalize) φ ci.2), ContractionsAux.cons (φ := φ) ci.2 ci.1.2⟩
  left_inv c := by
    match c with
    | ⟨aux, c⟩ =>
    match c with
    | ContractionsAux.cons (φsᵤₙ := aux') i c => rfl
  right_inv ci := by rfl

/-- The type of contractions is decidable. -/
instance decidable : (φs : List 𝓕) → DecidableEq (Contractions φs)
  | [] => fun a b =>
    match a, b with
    | ⟨_, a⟩, ⟨_, b⟩ =>
    match a, b with
    | ContractionsAux.nil, ContractionsAux.nil => isTrue rfl
  | _ :: φs =>
    haveI : DecidableEq (Contractions φs) := decidable φs
    haveI : DecidableEq ((c : Contractions φs) × Option (Fin (c.normalize).length)) :=
      Sigma.instDecidableEqSigma
    Equiv.decidableEq consEquiv

/-- The type of contractions is finite. -/
instance fintype : (φs : List 𝓕) → Fintype (Contractions φs)
  | [] => {
    elems := {⟨[], ContractionsAux.nil⟩}
    complete := by
      intro a
      rw [Finset.mem_singleton]
      exact contractions_nil a}
  | φ :: φs =>
    haveI : Fintype (Contractions φs) := fintype φs
    haveI : Fintype ((c : Contractions φs) × Option (Fin (c.normalize).length)) :=
      Sigma.instFintype
    Fintype.ofEquiv _ consEquiv.symm

/-- A contraction is a full contraction if there normalizing list of fields is empty. -/
def IsFull : Prop := c.normalize = []

/-- Provides a decidable instance for determining if a contraction is full
  (i.e., all fields are paired). -/
instance isFull_decidable : Decidable c.IsFull := by
  have hn : c.IsFull ↔ c.normalize.length = 0 := by
    simp [IsFull]
  apply decidable_of_decidable_of_iff hn.symm

def toOptionList : {l : List 𝓕} →  (c : Contractions l)  → List (Option (Fin l.length))
  | [], ⟨[], ContractionsAux.nil⟩ => []
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux) none c⟩ => none ::
    List.map (Option.map Fin.succ) (toOptionList ⟨aux, c⟩)
  | _ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some n) c⟩ =>
    some (Fin.succ (embedUncontracted ⟨aux, c⟩ n)) ::
    List.set ((List.map (Option.map Fin.succ) (toOptionList ⟨aux, c⟩)))
      (embedUncontracted ⟨aux, c⟩ n) (some ⟨0, Nat.zero_lt_succ φs.length⟩)

lemma toOptionList_length {l : List 𝓕} (c : Contractions l) : c.toOptionList.length = l.length := by
  match l, c with
  | [], ⟨[], ContractionsAux.nil⟩ =>
    dsimp [toOptionList]
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux) none c⟩ =>
    dsimp [toOptionList]
    rw [List.length_map, toOptionList_length ⟨aux, c⟩]
  | _ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some n) c⟩ =>
    dsimp [toOptionList]
    rw [List.length_set, List.length_map, toOptionList_length ⟨aux, c⟩]

def toFinOptionMap {l : List 𝓕} (c : Contractions l) : Fin l.length → Option (Fin l.length) :=
  c.toOptionList.get ∘ Fin.cast (toOptionList_length c).symm

lemma toFinOptionMap_neq_self {l : List 𝓕} (c : Contractions l) (i : Fin l.length) :
    c.toFinOptionMap i ≠ some i := by
  match l, c with
  | [], ⟨[], ContractionsAux.nil⟩ =>
    exact Fin.elim0 i
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux) none c⟩ =>
    dsimp [toFinOptionMap, toOptionList]
    match i with
    | ⟨0, _⟩ =>
      exact Option.noConfusion
    | ⟨n + 1, h⟩ =>
      simp only [List.getElem_cons_succ, List.getElem_map, List.length_cons]
      have hn := toFinOptionMap_neq_self ⟨aux, c⟩ ⟨n, Nat.succ_lt_succ_iff.mp h⟩
      simp only [Option.map_eq_some', not_exists, not_and]
      intro x hx
      simp only [toFinOptionMap, Function.comp_apply, Fin.cast_mk, List.get_eq_getElem, hx, ne_eq,
        Option.some.injEq] at hn
      rw [Fin.ext_iff] at hn ⊢
      simp_all
  | _ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some n) c⟩ =>
    dsimp [toFinOptionMap, toOptionList]
    match i with
    | ⟨0, _⟩ =>
      simp only [List.getElem_cons_zero, List.length_cons, Fin.zero_eta, Option.some.injEq, ne_eq]
      exact Fin.succ_ne_zero (embedUncontracted ⟨aux, c⟩ n)
    | ⟨n + 1, h⟩ =>
      simp only [List.getElem_cons_succ, List.length_cons, ne_eq]
      rw [List.getElem_set]
      split
      · exact ne_of_beq_false rfl
      · simp only [List.getElem_map, Option.map_eq_some', not_exists, not_and]
        intro x hx
        have hn := toFinOptionMap_neq_self ⟨aux, c⟩ ⟨n, Nat.succ_lt_succ_iff.mp h⟩
        simp only [toFinOptionMap, Function.comp_apply, Fin.cast_mk, List.get_eq_getElem, hx, ne_eq,
          Option.some.injEq] at hn
        rw [Fin.ext_iff] at hn ⊢
        simp_all

@[simp]
lemma toFinOptionMap_embedUncontracted {l : List 𝓕} (c : Contractions l)
    (i : Fin c.normalize.length) : c.toFinOptionMap (embedUncontracted c i) = none := by
  match l, c with
  | [], ⟨[], ContractionsAux.nil⟩ =>
    exact Fin.elim0 i
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux) none c⟩ =>
    dsimp [toFinOptionMap, toOptionList, embedUncontracted]
    match i with
    | ⟨0, _⟩ =>
      rfl
    | ⟨n + 1, h⟩ =>
      rw [show ⟨n + 1, h⟩ = Fin.succ ⟨n,  Nat.succ_lt_succ_iff.mp h⟩ by rfl]
      rw [Fin.cons_succ]
      simp only [Function.comp_apply, Fin.val_succ, List.getElem_cons_succ, List.getElem_map,
        Option.map_eq_none']
      exact toFinOptionMap_embedUncontracted ⟨aux, c⟩ ⟨n, Nat.succ_lt_succ_iff.mp h⟩
  | _ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some n) c⟩ =>
    dsimp [toFinOptionMap, toOptionList, embedUncontracted]
    rw [List.getElem_set]
    split
    · rename_i hs
      have hx := embedUncontracted_injective ⟨aux, c⟩ (Fin.val_injective hs)
      refine False.elim ?_
      have hn := Fin.succAbove_ne ⟨n, embedUncontracted.proof_6 _ φs aux n c⟩ i
      simp [Fin.ext_iff] at hx
      simp [Fin.ext_iff] at hn
      exact hn (id (Eq.symm hx))
    · simp
      exact toFinOptionMap_embedUncontracted ⟨aux, c⟩ _

lemma toFinOptionMap_involutive {l : List 𝓕} (c : Contractions l) (i j : Fin l.length) :
    c.toFinOptionMap i = some j → c.toFinOptionMap j = some i := by
  match l, c with
  | [], ⟨[], ContractionsAux.nil⟩ =>
    exact Fin.elim0 i
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux) none c⟩ =>
    dsimp [toFinOptionMap, toOptionList]
    match i, j with
    | ⟨0, _⟩, j =>
      exact Option.noConfusion
    | ⟨n + 1, h⟩, ⟨0, _⟩ =>
      simp
      intro x hx
      exact Fin.succ_ne_zero x
    | ⟨n + 1, hn⟩, ⟨m + 1, hm⟩ =>
      intro h1
      have hnm := toFinOptionMap_involutive ⟨aux, c⟩ ⟨n, Nat.succ_lt_succ_iff.mp hn⟩
        ⟨m, Nat.succ_lt_succ_iff.mp hm⟩
      simp
      simp [toFinOptionMap] at hnm
      have hnm' := hnm (by
        simp at h1
        obtain ⟨a, ha, ha2⟩ := h1
        rw [ha]
        simp only [Option.some.injEq]
        rw [Fin.ext_iff] at ha2 ⊢
        simp_all)
      use ⟨n, Nat.succ_lt_succ_iff.mp hn⟩
      simpa using hnm'
  | _ :: φs, ⟨_, .cons (φsᵤₙ := aux) (some n) c⟩ =>
    dsimp [toFinOptionMap, toOptionList]
    match i, j with
    | ⟨0, _⟩, j =>
      intro hj
      simp only [List.getElem_cons_zero, Option.some.injEq] at hj
      subst hj
      simp
    | ⟨n' + 1, h⟩, ⟨0, _⟩ =>
      intro hj
      simp at hj
      simp
      rw [List.getElem_set] at hj
      simp_all only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, List.getElem_map,
        ite_eq_left_iff, Option.map_eq_some']
      simp [Fin.ext_iff]
      by_contra hn
      have hn' := hj hn
      obtain ⟨a, ha, ha2⟩ := hn'
      exact Fin.succ_ne_zero a ha2
    | ⟨n' + 1, hn⟩, ⟨m + 1, hm⟩ =>
      simp
      rw [List.getElem_set, List.getElem_set]
      simp
      split
      · intro h
        simp [Fin.ext_iff] at h
      rename_i hn'
      intro h1
      split
      · rename_i hnx
        have hnm := toFinOptionMap_involutive ⟨aux, c⟩ ⟨n', Nat.succ_lt_succ_iff.mp hn⟩
          ⟨m, Nat.succ_lt_succ_iff.mp hm⟩
        subst hnx
        simp at hnm
        refine False.elim (hnm ?_)
        simp at h1
        obtain ⟨a, ha, ha2⟩ := h1
        have ha' : (embedUncontracted ⟨aux, c⟩ n) = a := by
          rw [Fin.ext_iff] at ha2 ⊢
          simp_all
        rw [ha']
        rw [← ha]
        rfl
      · rename_i hnx
        have hnm := toFinOptionMap_involutive ⟨aux, c⟩ ⟨n', Nat.succ_lt_succ_iff.mp hn⟩
          ⟨m, Nat.succ_lt_succ_iff.mp hm⟩ (by
          dsimp [toFinOptionMap]
          simp at h1
          obtain ⟨a, ha, ha2⟩ := h1
          have ha' : a = ⟨m, by exact Nat.succ_lt_succ_iff.mp hm⟩ := by
            rw [Fin.ext_iff] at ha2 ⊢
            simp_all
          rw [← ha', ← ha])
        change Option.map Fin.succ (toFinOptionMap ⟨aux, c⟩ ⟨m, Nat.succ_lt_succ_iff.mp hm⟩)  = _
        rw [hnm]
        rfl

def toInvolution {l : List 𝓕} (c : Contractions l) : Fin l.length → Fin l.length :=
  fun i =>
  if h : Option.isSome (c.toFinOptionMap i) then Option.get (c.toFinOptionMap i) h else i

lemma toInvolution_of_isSome {l : List 𝓕} {c : Contractions l} {i : Fin l.length}
    (hs : Option.isSome (c.toFinOptionMap i)) :
    c.toInvolution i = Option.get (c.toFinOptionMap i) hs := by
  dsimp [toInvolution]
  rw [dif_pos hs]

lemma toInvolution_of_eq_none {l : List 𝓕} {c : Contractions l} {i : Fin l.length}
    (hs : (c.toFinOptionMap i) = none) :
    c.toInvolution i = i := by
  dsimp [toInvolution]
  rw [dif_neg]
  simp_all

lemma toInvolution_image_isSome {l : List 𝓕} {c : Contractions l} {i : Fin l.length}
    (hs : Option.isSome (c.toFinOptionMap i)) :
    Option.isSome (c.toFinOptionMap (c.toInvolution i)) := by
  dsimp [toInvolution]
  rw [dif_pos hs]
  have hx := toFinOptionMap_involutive c i ((c.toFinOptionMap i).get hs)
  simp at hx
  rw [hx]
  rfl

lemma toInvolution_involutive {l : List 𝓕} (c : Contractions l) :
    Function.Involutive c.toInvolution := by
  intro i
  by_cases h : Option.isSome (c.toFinOptionMap i)
  · have hx := toFinOptionMap_involutive c i ((c.toFinOptionMap i).get h)
    rw [toInvolution_of_isSome (toInvolution_image_isSome h)]
    simp only [Option.some_get, forall_const] at hx
    simp only [toInvolution_of_isSome h, hx, Option.get_some]
  · simp at h
    rw [toInvolution_of_eq_none h]
    rw [toInvolution_of_eq_none h]

def involutionEquiv1 {l : List 𝓕} :
    {f : Fin l.length → Fin l.length // Function.Involutive f } ≃
    {f : Fin l.length → Option (Fin l.length) // (∀ i, f i ≠ some i) ∧
    ∀ i j, f i = some j → f j = some i} where
  toFun f := ⟨fun i => if h : f.1 i = i then none else f.1 i,
    fun i => by
      simp,
    fun i j => by
      simp
      intro hi hij
      subst hij
      rw [f.2]
      simp
      exact fun a => hi (id (Eq.symm a))⟩
  invFun f := ⟨fun i => if h : (f.1 i).isSome then Option.get (f.1 i) h  else i,
    fun i => by
    by_cases h : Option.isSome (f.1 i)
    · simp [h]
      have hf := f.2.2 i (Option.get (f.1 i) h) (by simp)
      simp [hf]
    · simp
      rw [dif_neg]
      · rw [dif_neg h]
      · rw [dif_neg h]
        exact h⟩
  left_inv f := by
    simp
    ext i
    simp
    by_cases hf : f.1 i = i
    · simp [hf]
    · simp [hf]
  right_inv f := by
    simp
    ext1
    simp
    funext i
    obtain ⟨val, property⟩ := f
    obtain ⟨left, right⟩ := property
    simp_all only [ne_eq]
    split
    next h =>
      ext a : 1
      simp_all only [Option.mem_def, reduceCtorEq, false_iff]
      apply Aesop.BuiltinRules.not_intro
      intro a_1
      simp_all only [Option.isSome_some, Option.get_some, forall_const]
    next h =>
      simp_all only [not_forall]
      obtain ⟨w, h⟩ := h
      simp_all only [↓reduceDIte, Option.some_get]

def involutionCons (n : ℕ):
    {f : Fin n.succ → Fin n.succ // Function.Involutive f } ≃
    (f : {f : Fin n → Fin n // Function.Involutive f}) × {i : Option (Fin n) //
      ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)} where
  toFun f := ⟨⟨
    fun i =>
    if h : f.1 i.succ = 0 then i
    else Fin.pred (f.1 i.succ) h , by
    intro i
    by_cases h : f.1 i.succ = 0
    · simp [h]
    · simp [h]
      simp [f.2 i.succ]
      intro h
      exact False.elim (Fin.succ_ne_zero i h)⟩,
    ⟨if h : f.1 0 = 0 then none else Fin.pred (f.1 0) h , by
    by_cases h0 : f.1 0 = 0
    · simp [h0]
    · simp [h0]
      refine fun h => False.elim (h (f.2 0))⟩⟩
  invFun f := ⟨
      if h : (f.2.1).isSome then
        Fin.cons (f.2.1.get h).succ (Function.update (Fin.succ ∘ f.1.1) (f.2.1.get h) 0)
      else
        Fin.cons 0 (Fin.succ ∘ f.1.1)
    , by
    by_cases hs : (f.2.1).isSome
    · simp only [Nat.succ_eq_add_one, hs, ↓reduceDIte, Fin.coe_eq_castSucc]
      let a := f.2.1.get hs
      change Function.Involutive (Fin.cons a.succ (Function.update (Fin.succ ∘ ↑f.fst) a 0))
      intro i
      rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
      · subst hi
        rw [Fin.cons_zero, Fin.cons_succ]
        simp
      · subst hj
        rw [Fin.cons_succ]
        by_cases hja : j = a
        · subst hja
          simp
        · rw [Function.update_apply ]
          rw [if_neg hja]
          simp
          have hf2 := f.2.2 hs
          change f.1.1 a = a at hf2
          have hjf1 : f.1.1 j ≠ a := by
            by_contra hn
            have haj : j = f.1.1 a := by
              rw [← hn]
              rw [f.1.2]
            rw [hf2] at haj
            exact hja haj
          rw [Function.update_apply, if_neg hjf1]
          simp
          rw [f.1.2]
    · simp [hs]
      intro i
      rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
      · subst hi
        simp
      · subst hj
        simp
        rw [f.1.2]⟩
  left_inv f := by
    match f with
    | ⟨f, hf⟩ =>
    simp
    ext i
    by_cases h0 : f 0 = 0
    · simp [h0]
      rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
      · subst hi
        simp [h0]
      · subst hj
        simp [h0]
        by_cases hj : f j.succ =0
        · rw [← h0] at hj
          have hn := Function.Involutive.injective hf hj
          exact False.elim (Fin.succ_ne_zero j hn)
        · simp [hj]
          rw [Fin.ext_iff] at hj
          simp at hj
          omega
    · rw [if_neg h0]
      by_cases hf' : i = f 0
      · subst hf'
        simp
        rw [hf]
        simp
      · rw [Function.update_apply, if_neg hf']
        rcases Fin.eq_zero_or_eq_succ i with hi | ⟨j, hj⟩
        · subst hi
          simp
        · subst hj
          simp
          by_cases hj : f j.succ =0
          · rw [← hj] at hf'
            rw [hf] at hf'
            simp at hf'
          · simp [hj]
            rw [Fin.ext_iff] at hj
            simp at hj
            omega
  right_inv f := by
    match f with
    | ⟨⟨f, hf⟩, ⟨f0, hf0⟩⟩ =>
    ext i
    · simp
      by_cases hs : f0.isSome
      · simp [hs]
        by_cases hi : i = f0.get hs
        · simp [hi, Function.update_apply]
          exact Eq.symm (Fin.val_eq_of_eq (hf0 hs))
        · simp [hi]
          split
          · rename_i h
            exact False.elim (Fin.succ_ne_zero (f i) h)
          · rfl
      · simp [hs]
        split
        · rename_i h
          exact False.elim (Fin.succ_ne_zero (f i) h)
        · rfl
    · simp only [Nat.succ_eq_add_one,  Option.mem_def,
      Option.dite_none_left_eq_some, Option.some.injEq]
      by_cases hs : f0.isSome
      · simp only [hs, ↓reduceDIte]
        simp [Fin.cons_zero]
        have hx : ¬  (f0.get hs).succ = 0 :=  (Fin.succ_ne_zero (f0.get hs))
        simp [hx]
        refine Iff.intro (fun hi => ?_) (fun hi => ?_)
        · rw [← hi]
          exact
            Option.eq_some_of_isSome
              (Eq.mpr_prop (Eq.refl (f0.isSome = true))
                (of_eq_true (Eq.trans (congrArg (fun x => x = true) hs) (eq_self true))))
        · subst hi
          exact rfl
      · simp [hs]
        simp at hs
        subst hs
        exact ne_of_beq_false rfl

def uncontractedFromInduction :  {l : List 𝓕} → (f : {f : Fin l.length → Fin l.length // Function.Involutive f}) →
    List 𝓕
  | [], _ => []
  | φ :: φs, f =>
    let f' := involutionCons φs.length f
    let c' := uncontractedFromInduction f'.1
    if f'.2.1.isSome then
      c'
    else
      φ :: c'

lemma uncontractedFromInduction_length :  {l : List 𝓕} → (f : {f : Fin l.length → Fin l.length // Function.Involutive f}) →
    (uncontractedFromInduction f).length = ∑ i, if f.1 i = i then 1 else 0
  | [] => by
    intro f
    rfl
  | φ :: φs  => by
    intro f
    let f' := involutionCons φs.length f
    let c' := uncontractedFromInduction f'.1
    by_cases h : f'.2.1.isSome
    · dsimp [uncontractedFromInduction]
      rw [if_pos h]
      rw [uncontractedFromInduction_length f'.1]
      rw [Fin.sum_univ_succ]
      simp [f', involutionCons] at h
      rw [if_neg h]
      simp
      sorry
    · sorry




def uncontractedEquiv {l : List 𝓕} (f : {f : Fin l.length → Fin l.length // Function.Involutive f}) :
    {i : Option (Fin l.length) //
        ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)} ≃
    Option (Fin (uncontractedFromInduction f).length)  := by
  let e1 : {i : Option (Fin l.length) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}
        ≃ Option {i : Fin l.length // f.1 i = i} :=
    { toFun := fun i => match i with
        | ⟨some i, h⟩ => some ⟨i, by simpa using h⟩
        | ⟨none, h⟩ => none
      invFun := fun i => match i with
        | some ⟨i, h⟩ => ⟨some i, by simpa using h⟩
        | none => ⟨none, by simp⟩
      left_inv := by
        intro a
        cases a
        aesop
      right_inv := by
        intro a
        cases a
        rfl
        simp_all only [Subtype.coe_eta] }
  let s : Finset (Fin l.length) := Finset.univ.filter fun i => f.1 i = i
  let e2' : { i : Fin l.length // f.1 i = i} ≃ {i // i ∈ s} := by
    refine Equiv.subtypeEquivProp ?h
    funext i
    simp [s]
  let e2 : {i // i ∈ s} ≃ Fin (Finset.card s) := by
     refine (Finset.orderIsoOfFin _ ?_).symm.toEquiv
     simp [s]
  have hcard : (uncontractedFromInduction f).length = Finset.card s := by
    simp [s]
    rw [Finset.card_filter]
    rw [uncontractedFromInduction_length]
  sorry




def involutionEquiv : (l : List 𝓕) → Contractions l ≃
    {f : Fin l.length → Fin l.length // Function.Involutive f}
  | [] => {
    toFun := fun c => ⟨fun i => i, fun i => rfl⟩,
    invFun := fun f => ⟨[], ContractionsAux.nil⟩,
    left_inv := by
      intro a
      cases a
      rename_i aux c
      cases c
      rfl
    right_inv := by
      intro f
      ext i
      exact Fin.elim0 i}
  | φ :: φs => by
    refine Equiv.trans consEquiv ?_
    refine Equiv.trans ?_  (involutionCons φs.length).symm
    refine Equiv.sigmaCongr (involutionEquiv φs) (fun c => ?_)
    exact {
      toFun := fun i? => ⟨Option.map c.embedUncontracted i?, by
        intro h

        sorry⟩
      invFun := fun i => sorry
      left_inv := by
        sorry
      right_inv := by sorry
    }

/-- A structure specifying when a type `I` and a map `f :I → Type` corresponds to
  the splitting of a fields `φ` into a creation `n` and annihlation part `p`. -/
structure Splitting (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le] where
  /-- The creation part of the fields. The label `n` corresponds to the fact that
    in normal ordering these feilds get pushed to the negative (left) direction. -/
  𝓑n : 𝓕 → (Σ i, f i)
  /-- The annhilation part of the fields. The label `p` corresponds to the fact that
    in normal ordering these feilds get pushed to the positive (right) direction. -/
  𝓑p : 𝓕 → (Σ i, f i)
  /-- The complex coefficent of creation part of a field `i`. This is usually `0` or `1`. -/
  𝓧n : 𝓕 → ℂ
  /-- The complex coefficent of annhilation part of a field `i`. This is usually `0` or `1`. -/
  𝓧p : 𝓕 → ℂ
  h𝓑 : ∀ i, ofListLift f [i] 1 = ofList [𝓑n i] (𝓧n i) + ofList [𝓑p i] (𝓧p i)
  h𝓑n : ∀ i j, le (𝓑n i) j
  h𝓑p : ∀ i j, le j (𝓑p i)

/-- In the static wick's theorem, the term associated with a contraction `c` containing
  the contractions. -/
noncomputable def toCenterTerm (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (q : 𝓕 → FieldStatistic)
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ[ℂ] A) :
    {φs : List 𝓕} → (c : Contractions φs) → (S : Splitting f le) → A
  | [], ⟨[], .nil⟩, _ => 1
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux') none c⟩, S => toCenterTerm f q le F ⟨aux', c⟩ S
  | a :: _, ⟨_, .cons (φsᵤₙ := aux') (some n) c⟩, S => toCenterTerm f q le F ⟨aux', c⟩ S *
    superCommuteCoef q [aux'.get n] (List.take (↑n) aux') •
      F (((superCommute fun i => q i.fst) (ofList [S.𝓑p a] (S.𝓧p a)))
        (ofListLift f [aux'.get n] 1))

/-- Shows that adding a field with no contractions (none) to an existing set of contractions
  results in the same center term as the original contractions.

  Physically, this represents that an uncontracted (free) field does not affect
  the contraction structure of other fields in Wick's theorem. -/
lemma toCenterTerm_none (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (q : 𝓕 → FieldStatistic) {φs : List 𝓕}
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A)
    (S : Splitting f le) (φ : 𝓕) (c : Contractions φs) :
    toCenterTerm (φs := φ :: φs) f q le F (Contractions.consEquiv.symm ⟨c, none⟩) S =
    toCenterTerm f q le F c S := by
  rw [consEquiv]
  simp only [Equiv.coe_fn_symm_mk]
  dsimp [toCenterTerm]
  rfl

/-- Proves that the part of the term gained from Wick contractions is in
  the center of the algebra. -/
lemma toCenterTerm_center (f : 𝓕 → Type) [∀ i, Fintype (f i)]
    (q : 𝓕 → FieldStatistic)
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le]
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le F] :
    {φs : List 𝓕} → (c : Contractions φs) → (S : Splitting f le) →
    (c.toCenterTerm f q le F S) ∈ Subalgebra.center ℂ A
  | [], ⟨[], .nil⟩, _ => by
    dsimp [toCenterTerm]
    exact Subalgebra.one_mem (Subalgebra.center ℂ A)
  | _ :: _, ⟨_, .cons (φsᵤₙ := aux') none c⟩, S => by
    dsimp [toCenterTerm]
    exact toCenterTerm_center f q le F ⟨aux', c⟩ S
  | a :: _, ⟨_, .cons (φsᵤₙ := aux') (some n) c⟩, S => by
    dsimp [toCenterTerm]
    refine Subalgebra.mul_mem (Subalgebra.center ℂ A) ?hx ?hy
    exact toCenterTerm_center f q le F ⟨aux', c⟩ S
    apply Subalgebra.smul_mem
    rw [ofListLift_expand]
    rw [map_sum, map_sum]
    refine Subalgebra.sum_mem (Subalgebra.center ℂ A) ?hy.hx.h
    intro x _
    simp only [CreateAnnihilateSect.toList]
    rw [ofList_singleton]
    exact OperatorMap.superCommute_ofList_singleton_ι_center (q := fun i => q i.1)
      (le := le) F (S.𝓑p a) ⟨aux'[↑n], x.head⟩

end Contractions

end Wick
