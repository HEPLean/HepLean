/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.Basic
/-!

# Involutions

There is an isomorphism between the type of contractions of a list `l` and
the type of involutions from `Fin l.length` to `Fin l.length`.

Likewise, there is an isomorphism from the type of full contractions of a list `l`
and the type of fixed-point free involutions from `Fin l.length` to `Fin l.length`.

Given this, the number of full contractions of a list `l` is
is given by the OEIS sequence A000085.

-/

namespace Wick

open HepLean.List
open HepLean.Fin
open FieldStatistic

variable {𝓕 : Type}
namespace Contractions

variable {l : List 𝓕}

/-!

## From Involution.

-/

def uncontractedFromInvolution :  {φs : List 𝓕} →
    (f : {f : Fin φs.length → Fin φs.length // Function.Involutive f}) →
    {l : List 𝓕 // l.length = (Finset.univ.filter fun i => f.1 i = i).card}
  | [], _ => ⟨[], by simp⟩
  | φ :: φs, f =>
    let luc := uncontractedFromInvolution (involutionCons φs.length f).fst
    let n' := involutionAddEquiv (involutionCons φs.length f).1 (involutionCons φs.length f).2
    if  hn : n' = none then
      have hn' := involutionAddEquiv_none_image_zero (n := φs.length) (f := f) hn
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
        rw [involutionAddEquiv_none_succ hn]⟩
    else
      let n := n'.get (Option.isSome_iff_ne_none.mpr hn)
      let np : Fin luc.1.length := ⟨n.1, by
        rw [luc.2]
        exact n.prop⟩
      ⟨optionEraseZ luc φ (some np), by
      let k' := (involutionCons φs.length f).2
      have hkIsSome : (k'.1).isSome := by
        simp [n', involutionAddEquiv ] at hn
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
    (involutionAddEquiv (involutionCons φs.length f).1 (involutionCons φs.length f).2)) := by
  let luc := uncontractedFromInvolution (involutionCons φs.length f).fst
  let n' := involutionAddEquiv (involutionCons φs.length f).1 (involutionCons φs.length f).2
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

def fromInvolutionAux  : {l : List 𝓕} →
  (f : {f : Fin l.length → Fin l.length // Function.Involutive f}) →
    ContractionsAux l (uncontractedFromInvolution f)
  | [] => fun _ =>  ContractionsAux.nil
  | _ :: φs => fun f =>
    let f' := involutionCons φs.length f
    let c' := fromInvolutionAux f'.1
    let n' := Option.map (finCongr ((uncontractedFromInvolution f'.fst).2.symm))
      (involutionAddEquiv f'.1 f'.2)
    auxCongr (uncontractedFromInvolution_cons f).symm (ContractionsAux.cons n' c')

def fromInvolution {φs : List 𝓕} (f : {f : Fin φs.length → Fin φs.length // Function.Involutive f}) :
    Contractions φs := ⟨uncontractedFromInvolution f, fromInvolutionAux f⟩

lemma fromInvolution_cons {φs : List 𝓕} {φ : 𝓕}
      (f : {f : Fin (φ :: φs).length → Fin (φ :: φs).length // Function.Involutive f}) :
    let f' := involutionCons φs.length f
    fromInvolution f = consEquiv.symm
    ⟨fromInvolution f'.1, Option.map (finCongr ((uncontractedFromInvolution f'.fst).2.symm))
      (involutionAddEquiv f'.1 f'.2)⟩ := by
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
      (involutionAddEquiv f n)⟩ := by
  rw [fromInvolution_cons]
  congr 1
  simp
  rw [Equiv.apply_symm_apply]


/-!

## To Involution.

-/

def toInvolution  : {φs : List 𝓕} →  (c : Contractions φs) →
    {f : {f : Fin φs.length → Fin φs.length // Function.Involutive f} //
    uncontractedFromInvolution f = c.1}
  | [], ⟨[], ContractionsAux.nil⟩ => ⟨⟨fun i => i, by
    intro i
    simp⟩, by rfl⟩
  | φ :: φs, ⟨_, .cons (φsᵤₙ := aux) n c⟩ => by
    let ⟨⟨f', hf1⟩, hf2⟩ := toInvolution ⟨aux, c⟩
    let n' : Option (Fin (uncontractedFromInvolution ⟨f', hf1⟩).1.length) :=
      Option.map (finCongr (by rw [hf2])) n
    let F := (involutionCons φs.length).symm ⟨⟨f', hf1⟩,
       (involutionAddEquiv ⟨f', hf1⟩).symm
       (Option.map (finCongr ((uncontractedFromInvolution ⟨f', hf1⟩).2))  n')⟩
    refine ⟨F, ?_⟩
    have hF0 : ((involutionCons φs.length) F) = ⟨⟨f', hf1⟩,
       (involutionAddEquiv  ⟨f', hf1⟩).symm
       (Option.map (finCongr ((uncontractedFromInvolution ⟨f', hf1⟩).2))  n')⟩ := by
      simp [F]
    have hF1 : ((involutionCons φs.length) F).fst = ⟨f', hf1⟩ := by
      rw [hF0]
    have hF2L : ((uncontractedFromInvolution ⟨f', hf1⟩)).1.length =
      (Finset.filter (fun i => ((involutionCons φs.length) F).1.1 i = i) Finset.univ).card := by
      apply  Eq.trans ((uncontractedFromInvolution ⟨f', hf1⟩)).2
      congr
      rw [hF1]
    have hF2 : ((involutionCons φs.length) F).snd = (involutionAddEquiv ((involutionCons φs.length) F).fst).symm
      (Option.map (finCongr hF2L) n') := by
      rw [@Sigma.subtype_ext_iff] at hF0
      ext1
      rw [hF0.2]
      simp
      congr 1
      · rw [hF1]
      · refine involutionAddEquiv_cast' ?_ n' _ _
        rw [hF1]
    rw [uncontractedFromInvolution_cons]
    have hx := (toInvolution ⟨aux, c⟩).2
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

lemma toInvolution_length {φs φsᵤₙ : List 𝓕} {c : ContractionsAux φs φsᵤₙ} :
    φsᵤₙ.length = (Finset.filter (fun i => (toInvolution ⟨φsᵤₙ, c⟩).1.1 i = i) Finset.univ).card
     := by
  have h2 := (toInvolution ⟨φsᵤₙ, c⟩).2
  simp at h2
  conv_lhs => rw [← h2]
  exact Mathlib.Vector.length_val (uncontractedFromInvolution (toInvolution ⟨φsᵤₙ, c⟩).1)

lemma toInvolution_cons {φs φsᵤₙ : List 𝓕} {φ : 𝓕}
    (c : ContractionsAux φs φsᵤₙ) (n : Option (Fin (φsᵤₙ.length))) :
    (toInvolution ⟨optionEraseZ φsᵤₙ φ n, ContractionsAux.cons n c⟩).1
    = (involutionCons φs.length).symm ⟨(toInvolution ⟨φsᵤₙ, c⟩).1,
      (involutionAddEquiv (toInvolution ⟨φsᵤₙ, c⟩).1).symm
      (Option.map (finCongr (toInvolution_length)) n)⟩ := by
  dsimp [toInvolution]
  congr 3
  rw [Option.map_map]
  simp [finCongr]
  rfl

lemma toInvolution_consEquiv {φs : List 𝓕} {φ : 𝓕}
    (c : Contractions φs) (n : Option (Fin (c.uncontracted.length))) :
    (toInvolution ((consEquiv (φ := φ)).symm ⟨c, n⟩)).1 =
    (involutionCons φs.length).symm ⟨(toInvolution c).1,
      (involutionAddEquiv (toInvolution c).1).symm
      (Option.map (finCongr (toInvolution_length)) n)⟩ := by
  erw [toInvolution_cons]
  rfl

/-!

## Involution equiv.

-/

lemma toInvolution_fromInvolution : {φs : List 𝓕} → (c : Contractions φs) →
    fromInvolution (toInvolution c) = c
  | [], ⟨[], ContractionsAux.nil⟩ => rfl
  | φ :: φs, ⟨_, .cons (φsᵤₙ := φsᵤₙ) n c⟩ => by
    rw [toInvolution_cons]
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
    → toInvolution (fromInvolution f) = f
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
        rw  [involutionAddEquiv_cast hx]
      simp  [Nat.succ_eq_add_one,- eq_mpr_eq_cast, Equiv.trans_apply, -Equiv.optionCongr_apply]
      rfl

def equivInvolutions {φs : List 𝓕} :
    Contractions φs ≃ {f : Fin φs.length → Fin φs.length // Function.Involutive f} where
  toFun := fun c =>  toInvolution c
  invFun := fromInvolution
  left_inv := toInvolution_fromInvolution
  right_inv := fromInvolution_toInvolution


/-!

## Full contractions and involutions.
-/
lemma isFull_iff_uncontractedFromInvolution_empty {φs : List 𝓕} (c : Contractions φs) :
    IsFull c ↔ (uncontractedFromInvolution (equivInvolutions c)).1 = [] := by
  let l := toInvolution c
  erw [l.2]
  rfl

lemma isFull_iff_filter_card_involution_zero  {φs : List 𝓕} (c : Contractions φs) :
    IsFull c ↔ (Finset.univ.filter fun i => (equivInvolutions c).1 i = i).card = 0 := by
  rw [isFull_iff_uncontractedFromInvolution_empty, List.ext_get_iff]
  simp

lemma isFull_iff_involution_no_fixed_points {φs : List 𝓕} (c : Contractions φs) :
    IsFull c ↔ ∀ (i : Fin φs.length), (equivInvolutions c).1 i ≠ i := by
  rw [isFull_iff_filter_card_involution_zero]
  simp
  rw [Finset.filter_eq_empty_iff]
  apply Iff.intro
  · intro h
    intro i
    refine h (Finset.mem_univ i)
  · intro i h
    exact fun a => i h


open Nat in
def isFullInvolutionEquiv {φs : List 𝓕} :
    {c : Contractions φs // IsFull c} ≃ {f : Fin φs.length → Fin φs.length // Function.Involutive f ∧ (∀ i, f i ≠ i)} where
  toFun c := ⟨equivInvolutions c.1, by
    apply And.intro (equivInvolutions c.1).2
    rw [← isFull_iff_involution_no_fixed_points]
    exact c.2
    ⟩
  invFun f := ⟨equivInvolutions.symm ⟨f.1, f.2.1⟩, by
    rw [isFull_iff_involution_no_fixed_points]
    simpa using f.2.2⟩
  left_inv c := by simp
  right_inv f := by simp


end Contractions

end Wick
