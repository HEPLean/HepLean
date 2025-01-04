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

lemma consEquiv_ext {φs : List 𝓕} {c1 c2 : Contractions φs}
    {n1 : Option (Fin c1.normalize.length)} {n2 : Option (Fin c2.normalize.length)}
    (hc : c1 = c2) (hn : Option.map (finCongr (by rw [hc])) n1 = n2) :
    (⟨c1, n1⟩ :  (c : Contractions φs) × Option (Fin c.normalize.length)) = ⟨c2, n2⟩ := by
  subst hc
  subst hn
  simp

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

lemma involutionCons_ext {n : ℕ} {f1 f2 :  (f : {f : Fin n → Fin n // Function.Involutive f}) × {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}}
    (h1 : f1.1 = f2.1) (h2 : f1.2 = Equiv.subtypeEquivRight (by rw [h1]; simp) f2.2) : f1 = f2 := by
  cases f1
  cases f2
  simp at h1 h2
  subst h1
  rename_i fst snd snd_1
  simp_all only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  obtain ⟨val, property⟩ := fst
  obtain ⟨val_1, property_1⟩ := snd
  obtain ⟨val_2, property_2⟩ := snd_1
  simp_all only
  rfl

def uncontractedEquiv' {l : List 𝓕} (f : {f : Fin l.length → Fin l.length // Function.Involutive f}) :
    {i : Option (Fin l.length) //
        ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)} ≃
    Option (Fin (Finset.univ.filter fun i => f.1 i = i).card)  := by
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
  refine e1.trans (Equiv.optionCongr (e2'.trans (e2)))


lemma uncontractedEquiv'_none_image_zero {φs : List 𝓕}  {φ :  𝓕} :
    {f : {f : Fin (φ :: φs).length → Fin (φ :: φs).length // Function.Involutive f}}
    → uncontractedEquiv' (involutionCons φs.length f).1 (involutionCons φs.length f).2  = none
    → f.1 ⟨0, Nat.zero_lt_succ φs.length⟩ = ⟨0, Nat.zero_lt_succ φs.length⟩ := by
  intro f h
  simp only [Nat.succ_eq_add_one, involutionCons, Equiv.coe_fn_mk, uncontractedEquiv',
    Option.isSome_some, Option.get_some, Option.isSome_none, Equiv.trans_apply,
    Equiv.optionCongr_apply, Equiv.coe_trans, RelIso.coe_fn_toEquiv, Option.map_eq_none'] at h
  simp_all only [List.length_cons, Fin.zero_eta]
  obtain ⟨val, property⟩ := f
  simp_all only [List.length_cons]
  split at h
  next i i_1 h_1 heq =>
    split at heq
    next h_2 => simp_all only [reduceCtorEq]
    next h_2 => simp_all only [reduceCtorEq]
  next i h_1 heq =>
    split at heq
    next h_2 => simp_all only
    next h_2 => simp_all only [Subtype.mk.injEq, reduceCtorEq]

lemma uncontractedEquiv'_cast {l : List 𝓕} {f1 f2 : {f : Fin l.length → Fin l.length // Function.Involutive f}}
    (hf : f1 = f2):
    uncontractedEquiv' f1 =  (Equiv.subtypeEquivRight  (by rw [hf]; simp)).trans
      ((uncontractedEquiv' f2).trans (Equiv.optionCongr (finCongr (by rw [hf])))):= by
  subst hf
  simp
  rfl

lemma uncontractedEquiv'_none_succ {φs : List 𝓕}  {φ :  𝓕} :
    {f : {f : Fin (φ :: φs).length → Fin (φ :: φs).length // Function.Involutive f}}
    → uncontractedEquiv' (involutionCons φs.length f).1 (involutionCons φs.length f).2  = none
    → ∀ (x : Fin φs.length), f.1 x.succ  = x.succ ↔ (involutionCons φs.length f).1.1 x = x := by
  intro f h x
  simp [involutionCons]
  have hn' := uncontractedEquiv'_none_image_zero h
  have hx : ¬ f.1 x.succ = ⟨0,  Nat.zero_lt_succ φs.length⟩:= by
    rw [← hn']
    exact fun hn => Fin.succ_ne_zero x (Function.Involutive.injective f.2 hn)
  apply Iff.intro
  · intro h2 h3
    rw [Fin.ext_iff]
    simp [h2]
  · intro h2
    have h2' := h2 hx
    conv_rhs => rw [← h2']
    simp


lemma uncontractedEquiv'_isSome_image_zero {φs : List 𝓕}  {φ :  𝓕} :
    {f : {f : Fin (φ :: φs).length → Fin (φ :: φs).length // Function.Involutive f}}
    → (uncontractedEquiv' (involutionCons φs.length f).1 (involutionCons φs.length f).2).isSome
    → ¬ f.1 ⟨0, Nat.zero_lt_succ φs.length⟩ = ⟨0, Nat.zero_lt_succ φs.length⟩ := by
  intro f hf
  simp [uncontractedEquiv', involutionCons] at hf
  simp_all only [List.length_cons, Fin.zero_eta]
  obtain ⟨val, property⟩ := f
  simp_all only [List.length_cons]
  apply Aesop.BuiltinRules.not_intro
  intro a
  simp_all only [↓reduceDIte, Option.isSome_none, Bool.false_eq_true]



def uncontractedFromInvolution:  {φs : List 𝓕} →
    (f : {f : Fin φs.length → Fin φs.length // Function.Involutive f}) →
    {l : List 𝓕 // l.length = (Finset.univ.filter fun i => f.1 i = i).card}
  | [], _ => ⟨[], by simp⟩
  | φ :: φs, f =>
    let luc := uncontractedFromInvolution (involutionCons φs.length f).fst
    let n' := uncontractedEquiv' (involutionCons φs.length f).1 (involutionCons φs.length f).2
    if  hn : n' = none then
      have hn' := uncontractedEquiv'_none_image_zero (φs := φs) (φ := φ) (f := f) hn
      ⟨optionEraseZ luc φ none, by
        simp [optionEraseZ]
        rw [← luc.2]
        conv_rhs => rw [Finset.card_filter]
        rw [Fin.sum_univ_succ]
        conv_rhs => erw [if_pos hn']
        ring_nf
        simp only [Nat.succ_eq_add_one, Mathlib.Vector.length_val,  Nat.cast_id,
          add_right_inj]
        rw [Finset.card_filter]
        apply congrArg
        funext i
        refine ite_congr ?h.h.h₁ (congrFun rfl) (congrFun rfl)
        rw [uncontractedEquiv'_none_succ hn]⟩
    else
      let n := n'.get (Option.isSome_iff_ne_none.mpr hn)
      let np : Fin luc.1.length := ⟨n.1, by
        rw [luc.2]
        exact n.prop⟩
      ⟨optionEraseZ luc φ (some np), by
      let k' := (involutionCons φs.length f).2
      have hkIsSome : (k'.1).isSome := by
        simp [n', uncontractedEquiv' ] at hn
        split at hn
        · simp_all only [reduceCtorEq, not_false_eq_true, Nat.succ_eq_add_one, Option.isSome_some, k']
        · simp_all only [not_true_eq_false]
      let k := k'.1.get hkIsSome
      rw [optionEraseZ_some_length]
      have hksucc : k.succ = f.1 ⟨0, Nat.zero_lt_succ φs.length⟩ := by
        simp [k, k', involutionCons]
      have hzero : ⟨0, Nat.zero_lt_succ φs.length⟩  = f.1 k.succ := by
        rw [hksucc]
        rw [f.2]
      have hkcons : ((involutionCons φs.length) f).1.1 k = k := by
        exact k'.2 hkIsSome
      have hksuccNe : f.1 k.succ ≠ k.succ := by
        conv_rhs => rw [hksucc]
        exact fun hn => Fin.succ_ne_zero k (Function.Involutive.injective f.2 hn )
      have hluc : 1 ≤ luc.1.length := by
        simp
        use k
        simp [involutionCons]
        rw [hksucc, f.2]
        simp
      rw [propext (Nat.sub_eq_iff_eq_add' hluc)]
      have h0 : ¬  f.1 ⟨0, Nat.zero_lt_succ φs.length⟩ = ⟨0, Nat.zero_lt_succ φs.length⟩ := by
        exact Option.isSome_dite'.mp hkIsSome
      conv_rhs =>
        rw [Finset.card_filter]
        erw [Fin.sum_univ_succ]
        erw [if_neg h0]
      simp only [Nat.succ_eq_add_one, Mathlib.Vector.length_val, List.length_cons,
        Nat.cast_id, zero_add]
      conv_rhs => lhs; rw [Eq.symm (Fintype.sum_ite_eq' k fun j => 1)]
      rw [← Finset.sum_add_distrib]
      rw [Finset.card_filter]
      apply congrArg
      funext i
      by_cases hik : i = k
      · subst hik
        simp [hkcons, hksuccNe]
      · simp [hik]
        refine ite_congr ?_ (congrFun rfl) (congrFun rfl)
        simp [involutionCons]
        have hfi : f.1 i.succ ≠ ⟨0, Nat.zero_lt_succ φs.length⟩ := by
          rw [hzero]
          by_contra hn
          have hik' := (Function.Involutive.injective f.2 hn)
          simp only [List.length_cons, Fin.succ_inj] at hik'
          exact hik hik'
        apply Iff.intro
        · intro h
          have h' := h hfi
          conv_rhs => rw [← h']
          simp
        · intro h hfi
          simp [Fin.ext_iff]
          rw [h]
          simp⟩

lemma uncontractedFromInvolution_cons {φs : List 𝓕} {φ : 𝓕}
    (f : {f : Fin (φ :: φs).length → Fin (φ :: φs).length // Function.Involutive f}) :
    uncontractedFromInvolution f =
    optionEraseZ (uncontractedFromInvolution (involutionCons φs.length f).fst) φ
    (Option.map (finCongr ((uncontractedFromInvolution (involutionCons φs.length f).fst).2.symm))
    (uncontractedEquiv' (involutionCons φs.length f).1 (involutionCons φs.length f).2)) := by
  let luc := uncontractedFromInvolution (involutionCons φs.length f).fst
  let n' := uncontractedEquiv' (involutionCons φs.length f).1 (involutionCons φs.length f).2
  change _ = optionEraseZ luc φ
    (Option.map (finCongr ((uncontractedFromInvolution (involutionCons φs.length f).fst).2.symm)) n')
  dsimp [uncontractedFromInvolution]
  by_cases hn : n' = none
  · have hn' := hn
    simp [n'] at hn'
    simp [hn']
    rw [hn]
    rfl
  · have hn' := hn
    simp [n'] at hn'
    simp [hn']
    congr
    simp [n']
    simp_all only [Nat.succ_eq_add_one, not_false_eq_true, n', luc]
    obtain ⟨val, property⟩ := f
    obtain ⟨val_1, property_1⟩ := luc
    simp_all only [Nat.succ_eq_add_one, List.length_cons]
    ext a : 1
    simp_all only [Option.mem_def, Option.some.injEq, Option.map_eq_some', finCongr_apply]
    apply Iff.intro
    · intro a_1
      subst a_1
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only [Option.some_get]
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      simp_all only [Option.get_some]
      rfl

def auxCongr  : {φs: List 𝓕} →  {φsᵤₙ φsᵤₙ' : List 𝓕} → (h : φsᵤₙ = φsᵤₙ') →
    ContractionsAux φs φsᵤₙ ≃ ContractionsAux φs φsᵤₙ'
  | _, _, _, Eq.refl _ => Equiv.refl _

lemma auxCongr_ext {φs: List 𝓕} {c c2 : Contractions φs} (h : c.1 = c2.1)
    (hx : c.2 =  auxCongr h.symm c2.2) : c = c2 := by
  cases c
  cases c2
  simp at h
  subst h
  simp [auxCongr] at hx
  subst hx
  rfl


lemma uncontractedEquiv'_cast' {l : List 𝓕} {f1 f2 : {f : Fin l.length → Fin l.length // Function.Involutive f}}
  {N : ℕ} (hf : f1 = f2) (n : Option (Fin N)) (hn1 : N = (Finset.filter (fun i => f1.1 i = i) Finset.univ).card)
  (hn2 : N = (Finset.filter (fun i => f2.1 i = i) Finset.univ).card):
    HEq ((uncontractedEquiv' f1).symm (Option.map (finCongr hn1) n)) ((uncontractedEquiv' f2).symm (Option.map (finCongr hn2) n)) := by
  subst hf
  rfl

def toInvolution'  : {φs : List 𝓕} →  (c : Contractions φs) →
    {f : {f : Fin φs.length → Fin φs.length // Function.Involutive f} //
    uncontractedFromInvolution f = c.1}
  | [], ⟨[], ContractionsAux.nil⟩ => ⟨⟨fun i => i, by
    intro i
    simp⟩, by rfl⟩
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) n c⟩ => by
    let ⟨⟨f', hf1⟩, hf2⟩ := toInvolution' ⟨aux, c⟩
    let n' : Option (Fin (uncontractedFromInvolution ⟨f', hf1⟩).1.length) :=
      Option.map (finCongr (by rw [hf2])) n
    let F := (involutionCons φs.length).symm ⟨⟨f', hf1⟩,
       (uncontractedEquiv' ⟨f', hf1⟩).symm
       (Option.map (finCongr ((uncontractedFromInvolution ⟨f', hf1⟩).2))  n')⟩
    refine ⟨F, ?_⟩
    have hF0 : ((involutionCons φs.length) F) = ⟨⟨f', hf1⟩,
       (uncontractedEquiv'  ⟨f', hf1⟩).symm
       (Option.map (finCongr ((uncontractedFromInvolution ⟨f', hf1⟩).2))  n')⟩ := by
      simp [F]
    have hF1 : ((involutionCons φs.length) F).fst = ⟨f', hf1⟩ := by
      rw [hF0]
    have hF2L : ((uncontractedFromInvolution ⟨f', hf1⟩)).1.length =
      (Finset.filter (fun i => ((involutionCons φs.length) F).1.1 i = i) Finset.univ).card := by
      apply  Eq.trans ((uncontractedFromInvolution ⟨f', hf1⟩)).2
      congr
      rw [hF1]
    have hF2 : ((involutionCons φs.length) F).snd = (uncontractedEquiv' ((involutionCons φs.length) F).fst).symm
      (Option.map (finCongr hF2L) n') := by
      rw [@Sigma.subtype_ext_iff] at hF0
      ext1
      rw [hF0.2]
      simp
      congr 1
      · rw [hF1]
      · refine uncontractedEquiv'_cast' ?_ n' _ _
        rw [hF1]
    rw [uncontractedFromInvolution_cons]
    have hx := (toInvolution' ⟨aux, c⟩).2
    simp at hx
    simp
    refine optionEraseZ_ext ?_ ?_ ?_
    · dsimp [F]
      rw [Equiv.apply_symm_apply]
      simp
      rw [← hx]
      simp_all only
    · rfl
    · simp [hF2]
      dsimp [n']
      simp [finCongr]
      simp only [Nat.succ_eq_add_one, id_eq, eq_mpr_eq_cast, F, n']
      ext a : 1
      simp only [Option.mem_def, Option.map_eq_some', Function.comp_apply, Fin.cast_trans,
        Fin.cast_eq_self, exists_eq_right]

lemma toInvolution'_length {φs φsᵤₙ : List 𝓕} {c : ContractionsAux φs φsᵤₙ} :
    φsᵤₙ.length = (Finset.filter (fun i => (toInvolution' ⟨φsᵤₙ, c⟩).1.1 i = i) Finset.univ).card
     := by
  have h2 := (toInvolution' ⟨φsᵤₙ, c⟩).2
  simp at h2
  conv_lhs => rw [← h2]
  exact Mathlib.Vector.length_val (uncontractedFromInvolution (toInvolution' ⟨φsᵤₙ, c⟩).1)

lemma toInvolution'_cons {φs φsᵤₙ : List 𝓕} {φ : 𝓕}
    (c : ContractionsAux φs φsᵤₙ) (n : Option (Fin (φsᵤₙ.length))) :
    (toInvolution' ⟨optionEraseZ φsᵤₙ φ n, ContractionsAux.cons n c⟩).1
    = (involutionCons φs.length).symm ⟨(toInvolution' ⟨φsᵤₙ, c⟩).1,
      (uncontractedEquiv' (toInvolution' ⟨φsᵤₙ, c⟩).1).symm
      (Option.map (finCongr (toInvolution'_length)) n)⟩ := by
  dsimp [toInvolution']
  congr 3
  rw [Option.map_map]
  simp [finCongr]
  rfl

lemma toInvolution_consEquiv {φs : List 𝓕} {φ : 𝓕}
    (c : Contractions φs) (n : Option (Fin (c.normalize.length))) :
    (toInvolution' ((consEquiv (φ := φ)).symm ⟨c, n⟩)).1 =
    (involutionCons φs.length).symm ⟨(toInvolution' c).1,
      (uncontractedEquiv' (toInvolution' c).1).symm
      (Option.map (finCongr (toInvolution'_length)) n)⟩ := by
  erw [toInvolution'_cons]
  rfl

def fromInvolutionAux  : {l : List 𝓕} →
  (f : {f : Fin l.length → Fin l.length // Function.Involutive f}) →
    ContractionsAux l (uncontractedFromInvolution f)
  | [] => fun _ =>  ContractionsAux.nil
  | _ :: φs => fun f =>
    let f' := involutionCons φs.length f
    let c' := fromInvolutionAux f'.1
    let n' := Option.map (finCongr ((uncontractedFromInvolution f'.fst).2.symm))
      (uncontractedEquiv' f'.1 f'.2)
    auxCongr (uncontractedFromInvolution_cons f).symm (ContractionsAux.cons n' c')

def fromInvolution {φs : List 𝓕} (f : {f : Fin φs.length → Fin φs.length // Function.Involutive f}) :
    Contractions φs := ⟨uncontractedFromInvolution f, fromInvolutionAux f⟩

lemma fromInvolution_cons {φs : List 𝓕} {φ : 𝓕}
      (f : {f : Fin (φ :: φs).length → Fin (φ :: φs).length // Function.Involutive f}) :
    let f' := involutionCons φs.length f
    fromInvolution f = consEquiv.symm
    ⟨fromInvolution f'.1, Option.map (finCongr ((uncontractedFromInvolution f'.fst).2.symm))
      (uncontractedEquiv' f'.1 f'.2)⟩ := by
  refine auxCongr_ext ?_ ?_
  · dsimp [fromInvolution]
    rw [uncontractedFromInvolution_cons]
    rfl
  · dsimp [fromInvolution, fromInvolutionAux]
    rfl

lemma fromInvolution_of_involutionCons
    {φs : List 𝓕} {φ : 𝓕}
    (f : {f : Fin (φs ).length → Fin (φs).length // Function.Involutive f})
    (n : { i : Option (Fin φs.length) // ∀ (h : i.isSome = true), f.1 (i.get h) = i.get h }):
    fromInvolution (φs := φ :: φs) ((involutionCons φs.length).symm ⟨f, n⟩) =
    consEquiv.symm
    ⟨fromInvolution f, Option.map (finCongr ((uncontractedFromInvolution f).2.symm))
      (uncontractedEquiv' f n)⟩ := by
  rw [fromInvolution_cons]
  congr 1
  simp
  rw [Equiv.apply_symm_apply]




lemma toInvolution_fromInvolution : {φs : List 𝓕} → (c : Contractions φs) →
    fromInvolution (toInvolution' c) = c
  | [], ⟨[], ContractionsAux.nil⟩ => rfl
  | φ :: φs, ⟨_, .cons (φsᵤₙ := φsᵤₙ) n c⟩ => by
    rw [toInvolution'_cons]
    rw [fromInvolution_of_involutionCons]
    rw [Equiv.symm_apply_eq]
    dsimp [consEquiv]
    refine consEquiv_ext ?_ ?_
    · exact toInvolution_fromInvolution ⟨φsᵤₙ, c⟩
    · simp [finCongr]
      ext a : 1
      simp only [Option.mem_def, Option.map_eq_some', Function.comp_apply, Fin.cast_trans,
        Fin.cast_eq_self, exists_eq_right]

lemma fromInvolution_toInvolution : {φs : List 𝓕} →  (f : {f : Fin (φs ).length → Fin (φs).length // Function.Involutive f})
    → toInvolution' (fromInvolution f) = f
  | [], _ => by
    ext x
    exact Fin.elim0 x
  | φ :: φs, f => by
    rw [fromInvolution_cons]
    rw [toInvolution_consEquiv]
    erw [Equiv.symm_apply_eq]
    have hx := fromInvolution_toInvolution ((involutionCons φs.length) f).fst
    apply involutionCons_ext ?_ ?_
    · simp only [Nat.succ_eq_add_one, List.length_cons]
      exact hx
    · simp only [Nat.succ_eq_add_one, Option.map_map, List.length_cons]
      rw [Equiv.symm_apply_eq]
      conv_rhs =>
        lhs
        rw  [uncontractedEquiv'_cast hx]
      simp  [Nat.succ_eq_add_one,- eq_mpr_eq_cast, Equiv.trans_apply, -Equiv.optionCongr_apply]
      rfl

def equivInvolutions {φs : List 𝓕} :
    Contractions φs ≃ {f : Fin φs.length → Fin φs.length // Function.Involutive f} where
  toFun := fun c =>  toInvolution' c
  invFun := fromInvolution
  left_inv := toInvolution_fromInvolution
  right_inv := fromInvolution_toInvolution

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
