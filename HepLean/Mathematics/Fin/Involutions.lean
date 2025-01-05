/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Factorial.DoubleFactorial
/-!
# Fin involutions

Some properties of involutions of `Fin n`.

These involutions are used in e.g. proving results about Wick contractions.

-/
namespace HepLean.Fin

open Nat

def involutionCons (n : ℕ) : {f : Fin n.succ → Fin n.succ // Function.Involutive f } ≃
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

lemma involutionCons_ext {n : ℕ} {f1 f2 :  (f : {f : Fin n → Fin n // Function.Involutive f}) ×
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}}
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


def involutionAddEquiv {n : ℕ} (f : {f : Fin n → Fin n // Function.Involutive f}) :
    {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)} ≃
    Option (Fin (Finset.univ.filter fun i => f.1 i = i).card)  := by
  let e1 : {i : Option (Fin n) // ∀ (h : i.isSome), f.1 (Option.get i h) = (Option.get i h)}
        ≃ Option {i : Fin n // f.1 i = i} :=
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
  let s : Finset (Fin n) := Finset.univ.filter fun i => f.1 i = i
  let e2' : { i : Fin n // f.1 i = i} ≃ {i // i ∈ s} := by
    refine Equiv.subtypeEquivProp ?h
    funext i
    simp [s]
  let e2 : {i // i ∈ s} ≃ Fin (Finset.card s) := by
     refine (Finset.orderIsoOfFin _ ?_).symm.toEquiv
     simp [s]
  refine e1.trans (Equiv.optionCongr (e2'.trans (e2)))


lemma involutionAddEquiv_none_image_zero {n : ℕ} :
    {f : {f : Fin n.succ → Fin n.succ // Function.Involutive f}}
    → involutionAddEquiv (involutionCons n f).1 (involutionCons n f).2  = none
    → f.1 ⟨0, Nat.zero_lt_succ n⟩ = ⟨0, Nat.zero_lt_succ n⟩ := by
  intro f h
  simp only [Nat.succ_eq_add_one, involutionCons, Equiv.coe_fn_mk, involutionAddEquiv,
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

lemma involutionAddEquiv_cast {n : ℕ} {f1 f2 : {f : Fin n → Fin n // Function.Involutive f}}
    (hf : f1 = f2):
    involutionAddEquiv f1 =  (Equiv.subtypeEquivRight  (by rw [hf]; simp)).trans
      ((involutionAddEquiv f2).trans (Equiv.optionCongr (finCongr (by rw [hf])))):= by
  subst hf
  simp
  rfl


lemma involutionAddEquiv_cast' {m : ℕ} {f1 f2 : {f : Fin m → Fin m // Function.Involutive f}}
  {N : ℕ} (hf : f1 = f2) (n : Option (Fin N)) (hn1 : N = (Finset.filter (fun i => f1.1 i = i) Finset.univ).card)
  (hn2 : N = (Finset.filter (fun i => f2.1 i = i) Finset.univ).card):
    HEq ((involutionAddEquiv f1).symm (Option.map (finCongr hn1) n)) ((involutionAddEquiv f2).symm (Option.map (finCongr hn2) n)) := by
  subst hf
  rfl

lemma involutionAddEquiv_none_succ {n : ℕ}
    {f : {f : Fin n.succ → Fin n.succ // Function.Involutive f}}
    (h : involutionAddEquiv (involutionCons n f).1 (involutionCons n f).2  = none)
    (x : Fin n) : f.1 x.succ  = x.succ ↔ (involutionCons n f).1.1 x = x := by
  simp [involutionCons]
  have hn' := involutionAddEquiv_none_image_zero h
  have hx : ¬ f.1 x.succ = ⟨0,  Nat.zero_lt_succ n⟩:= by
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

lemma involutionAddEquiv_isSome_image_zero {n : ℕ} :
    {f : {f : Fin n.succ → Fin n.succ // Function.Involutive f}}
    → (involutionAddEquiv (involutionCons n f).1 (involutionCons n f).2).isSome
    → ¬ f.1 ⟨0, Nat.zero_lt_succ n⟩ = ⟨0, Nat.zero_lt_succ n⟩ := by
  intro f hf
  simp [involutionAddEquiv, involutionCons] at hf
  simp_all only [List.length_cons, Fin.zero_eta]
  obtain ⟨val, property⟩ := f
  simp_all only [List.length_cons]
  apply Aesop.BuiltinRules.not_intro
  intro a
  simp_all only [↓reduceDIte, Option.isSome_none, Bool.false_eq_true]

def involutionNoFixedEquivSum {n : ℕ} :
    {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f
    ∧ ∀ i, f i ≠ i} ≃ Σ (k : Fin (2 * n + 1)),
     {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f
    ∧ (∀ i, f i ≠ i) ∧ f 0 = k.succ} where
  toFun f := ⟨(f.1 0).pred (f.2.2 0), ⟨f.1, f.2.1, by simpa using f.2.2⟩⟩
  invFun f := ⟨f.2.1, ⟨f.2.2.1, f.2.2.2.1⟩⟩
  left_inv f := by
    rfl
  right_inv f := by
    simp
    ext
    · simp
      rw [f.2.2.2.2]
      simp
    · simp

/-!

## Equivalences of involutions with no fixed points.

The main aim of thes equivalences is to define `involutionNoFixedZeroEquivProd`.

-/

def involutionNoFixedZeroSetEquivEquiv {n : ℕ}
    (k : Fin (2 * n + 1)) (e : Fin (2 * n.succ) ≃ Fin (2 * n.succ)) :
     {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f
    ∧ (∀ i, f i ≠ i) ∧ f 0 = k.succ} ≃
    {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive (e.symm ∘ f ∘ e) ∧
      (∀ i, (e.symm ∘ f ∘ e) i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} where
  toFun f := ⟨e ∘ f.1 ∘ e.symm, by
    intro i
    simp
    rw [f.2.1], by
      simpa using f.2.2.1, by simpa using f.2.2.2⟩
  invFun f := ⟨e.symm ∘ f.1 ∘ e, by
    intro i
    simp
    have hf2 := f.2.1 i
    simpa using hf2, by
      simpa using f.2.2.1, by simpa using f.2.2.2⟩
  left_inv f := by
    ext i
    simp
  right_inv f := by
    ext i
    simp

def involutionNoFixedZeroSetEquivSetEquiv {n : ℕ} (k : Fin (2 * n + 1)) (e : Fin (2 * n.succ) ≃ Fin (2 * n.succ)) :
  {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive (e.symm ∘ f ∘ e) ∧
      (∀ i, (e.symm ∘ f ∘ e) i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} ≃
    {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧  (e.symm ∘ f ∘ e) 0 = k.succ} := by
  refine Equiv.subtypeEquivRight ?_
  intro f
  have h1 : Function.Involutive (⇑e.symm ∘ f ∘ ⇑e) ↔ Function.Involutive f := by
    apply Iff.intro
    · intro h i
      have hi := h (e.symm i)
      simpa using hi
    · intro h i
      have hi := h (e i)
      simp [hi]
  rw [h1]
  simp
  intro h1 h2
  apply Iff.intro
  · intro h i
    have hi := h (e.symm i)
    simpa using hi
  · intro h i
    have hi := h (e i)
    by_contra hn
    nth_rewrite 2 [← hn] at hi
    simp at hi


def involutionNoFixedZeroSetEquivEquiv' {n : ℕ} (k : Fin (2 * n + 1)) (e : Fin (2 * n.succ) ≃ Fin (2 * n.succ)) :
    {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧  (e.symm ∘ f ∘ e) 0 = k.succ}
      ≃ {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧  f (e 0) = e k.succ} := by
  refine Equiv.subtypeEquivRight ?_
  simp
  intro f hi h1
  exact Equiv.symm_apply_eq e

def involutionNoFixedZeroSetEquivSetOne {n : ℕ} (k : Fin (2 * n + 1)) :
    {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧  f 0 = k.succ}
      ≃ {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧  f 0 = 1} := by
  refine Equiv.trans (involutionNoFixedZeroSetEquivEquiv k (Equiv.swap k.succ 1)) ?_
  refine Equiv.trans (involutionNoFixedZeroSetEquivSetEquiv k (Equiv.swap k.succ 1)) ?_
  refine Equiv.trans (involutionNoFixedZeroSetEquivEquiv' k (Equiv.swap k.succ 1)) ?_
  refine  Equiv.subtypeEquivRight ?_
  simp
  intro f hi h1
  rw [Equiv.swap_apply_of_ne_of_ne]
  · exact Ne.symm (Fin.succ_ne_zero k)
  · exact Fin.zero_ne_one

def involutionNoFixedSetOne {n : ℕ} :
     {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧  f 0 = 1} ≃
      {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f ∧
      (∀ i, f i ≠ i)} where
  toFun f := by
    have hf1 : f.1 1 = 0 := by
      have hf := f.2.2.2
      simp [← hf]
      rw [f.2.1]
    let f' := f.1 ∘ Fin.succ ∘ Fin.succ
    have hf' (i : Fin (2 * n)) : f' i ≠ 0 := by
      simp [f']
      simp [← hf1]
      by_contra hn
      have hn' := Function.Involutive.injective f.2.1 hn
      simp [Fin.ext_iff] at hn'
    let f'' := fun i => (f' i).pred (hf' i)
    have hf'' (i : Fin (2 * n)) : f'' i ≠ 0 := by
      simp [f'']
      rw [@Fin.pred_eq_iff_eq_succ]
      simp [f']
      simp [← f.2.2.2 ]
      by_contra hn
      have hn' := Function.Involutive.injective f.2.1 hn
      simp [Fin.ext_iff] at hn'
    let f''' := fun i => (f'' i).pred (hf'' i)
    refine ⟨f''', ?_, ?_⟩
    · intro i
      simp [f''', f'', f']
      simp [f.2.1 i.succ.succ]
    · intro i
      simp [f''', f'', f']
      rw [@Fin.pred_eq_iff_eq_succ]
      rw [@Fin.pred_eq_iff_eq_succ]
      exact f.2.2.1 i.succ.succ
  invFun f := by
    let f' := fun (i : Fin (2 * n.succ))=>
      match i with
      | ⟨0, h⟩ => 1
      | ⟨1, h⟩ => 0
      | ⟨(Nat.succ (Nat.succ n)), h⟩ => (f.1 ⟨n, by omega⟩).succ.succ
    refine ⟨f', ?_, ?_, ?_⟩
    · intro i
      match i with
      | ⟨0, h⟩ => rfl
      | ⟨1, h⟩ => rfl
      | ⟨(Nat.succ (Nat.succ m)), h⟩ =>
        simp [f']
        split
        · rename_i h
          simp at h
          exact False.elim (Fin.succ_ne_zero (f.1 ⟨m, _⟩).succ h)
        · rename_i h
          simp [Fin.ext_iff] at h
        · rename_i h
          rename_i x r
          simp_all [Fin.ext_iff]
          have hfn {a b : ℕ} {ha : a < 2 * n} {hb : b < 2 * n}
            (hab : ↑(f.1 ⟨a, ha⟩) = b): ↑(f.1 ⟨b, hb⟩) = a := by
            have ht : f.1 ⟨a, ha⟩ = ⟨b, hb⟩ := by
              simp [hab, Fin.ext_iff]
            rw [← ht, f.2.1]
          exact hfn h
    · intro i
      match i with
      | ⟨0, h⟩ =>
        simp [f']
        split
        · rename_i h
          simp
        · rename_i h
          simp [Fin.ext_iff] at h
        · rename_i h
          simp [Fin.ext_iff] at h
      | ⟨1, h⟩ =>
        simp [f']
        split
        · rename_i h
          simp at h
        · rename_i h
          simp
        · rename_i h
          simp [Fin.ext_iff] at h
      | ⟨(Nat.succ (Nat.succ m)), h⟩ =>
        simp [f', Fin.ext_iff]
        have hf:= f.2.2 ⟨m, by exact Nat.add_lt_add_iff_right.mp h⟩
        simp [Fin.ext_iff] at hf
        omega
    · simp [f']
      split
      · rename_i h
        simp
      · rename_i h
        simp at h
      · rename_i h
        simp [Fin.ext_iff] at h
  left_inv f := by
    have hf1 : f.1 1 = 0 := by
      have hf := f.2.2.2
      simp [← hf]
      rw [f.2.1]
    simp
    ext i
    simp
    split
    · simp
      rw [f.2.2.2]
      simp
    · simp
      rw [hf1]
      simp
    · rfl
  right_inv f := by
    simp
    ext i
    simp
    split
    · rename_i h
      simp [Fin.ext_iff]  at h
    · rename_i h
      simp [Fin.ext_iff] at h
    · rename_i h
      simp
      congr
      apply congrArg
      simp_all [Fin.ext_iff]


def involutionNoFixedZeroSetEquiv {n : ℕ} (k : Fin (2 * n + 1)) :
    {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧  f 0 = k.succ}
      ≃ {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f ∧ (∀ i, f i ≠ i)} := by
  refine Equiv.trans (involutionNoFixedZeroSetEquivSetOne k) involutionNoFixedSetOne

def involutionNoFixedEquivSumSame {n : ℕ} :
    {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    ≃  Σ (_ : Fin (2 * n + 1)), {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f ∧ (∀ i, f i ≠ i)} := by
  refine Equiv.trans involutionNoFixedEquivSum ?_
  refine Equiv.sigmaCongrRight involutionNoFixedZeroSetEquiv

def involutionNoFixedZeroEquivProd {n : ℕ} :
    {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    ≃ Fin (2 * n + 1) × {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f ∧ (∀ i, f i ≠ i)} := by
  refine Equiv.trans involutionNoFixedEquivSumSame ?_
  exact Equiv.sigmaEquivProd (Fin (2 * n + 1))
      { f // Function.Involutive f ∧ ∀ (i : Fin (2 * n)), f i ≠ i}

/-!

## Cardinality

-/


instance {n : ℕ}  : Fintype { f // Function.Involutive f ∧ ∀ (i : Fin n), f i ≠ i } := by
  haveI : DecidablePred fun x => Function.Involutive x := by
    intro f
    apply Fintype.decidableForallFintype (α := Fin n)
  haveI : DecidablePred fun x => Function.Involutive x ∧ ∀ (i : Fin n), x i ≠ i := by
     intro x
     apply instDecidableAnd
  apply Subtype.fintype

lemma involutionNoFixed_card_succ {n : ℕ} :
   Fintype.card {f : Fin (2 * n.succ) → Fin (2 * n.succ) // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    = (2 * n + 1) * Fintype.card {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f ∧ (∀ i, f i ≠ i)} := by
  rw [Fintype.card_congr (involutionNoFixedZeroEquivProd)]
  rw [Fintype.card_prod ]
  congr
  exact Fintype.card_fin (2 * n + 1)


lemma involutionNoFixed_card_mul_two : (n : ℕ) →
   Fintype.card {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    = (2 * n - 1)‼
  | 0 => rfl
  | Nat.succ n => by
    rw [involutionNoFixed_card_succ]
    rw [involutionNoFixed_card_mul_two n]
    exact Eq.symm (Nat.doubleFactorial_add_one (Nat.mul 2 n))

lemma involutionNoFixed_card_even : (n : ℕ) → (he : Even n) →
    Fintype.card {f : Fin n → Fin n  // Function.Involutive f ∧ (∀ i, f i ≠ i)} = (n - 1)‼ := by
  intro n he
  obtain ⟨r, hr⟩ := he
  have hr' : n = 2 * r := by omega
  subst hr'
  exact involutionNoFixed_card_mul_two r

end HepLean.Fin
