/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import HepLean.Mathematics.Fin
/-!
# List lemmas

-/
namespace HepLean.List

open Fin
open HepLean
variable {n : Nat}

/-- The equivalence between `Fin (a :: l).length` and `Fin (List.orderedInsert r a l).length`
  mapping `0` in the former to the location of `a` in the latter. -/
def insertEquiv {α : Type} (r : α → α → Prop) [DecidableRel r] (a : α) : (l : List α) →
    Fin (a :: l).length ≃ Fin (List.orderedInsert r a l).length
| [] => Equiv.refl _
| b :: l => by
  if r a b then
    exact (Fin.castOrderIso (List.orderedInsert_length r (b :: l) a).symm).toEquiv
  else
    let e := insertEquiv (r := r) a l
    let e2 : Fin (a :: b :: l).length ≃ Fin (b :: a :: l).length :=
      Equiv.swap ⟨0, Nat.zero_lt_succ (b :: l).length⟩ ⟨1, Nat.one_lt_succ_succ l.length⟩
    let e3 : Fin (b :: a :: l).length ≃ Fin (b :: List.orderedInsert r a l).length :=
      Fin.equivCons e
    let e4 : Fin (b :: List.orderedInsert r a l).length ≃
        Fin (List.orderedInsert r a (b :: l)).length :=
      (Fin.castOrderIso (by
        rw [List.orderedInsert_length]
        simpa using List.orderedInsert_length r l a)).toEquiv
    exact e2.trans (e3.trans e4)

lemma insertEquiv_congr {α : Type} {r : α → α → Prop} [DecidableRel r] (a : α) (l l' : List α)
    (h : l = l') : insertEquiv r a l = (Fin.castOrderIso (by simp [h])).toEquiv.trans
    ((insertEquiv r a l').trans (Fin.castOrderIso (by simp [h])).toEquiv) := by
  subst h
  rfl

lemma insertEquiv_cons_pos {α : Type} {r : α → α → Prop} [DecidableRel r] (a b : α) (hab : r a b)
    (l : List α) : insertEquiv r a (b :: l) =
    (Fin.castOrderIso (List.orderedInsert_length r (b :: l) a).symm).toEquiv := by
  simp [insertEquiv, hab]

lemma insertEquiv_cons_neg {α : Type} {r : α → α → Prop} [DecidableRel r] (a b : α) (hab : ¬ r a b)
    (l : List α) : insertEquiv r a (b :: l) =
    let e := insertEquiv r a l
    let e2 : Fin (a :: b :: l).length ≃ Fin (b :: a :: l).length :=
      Equiv.swap ⟨0, Nat.zero_lt_succ (b :: l).length⟩ ⟨1, Nat.one_lt_succ_succ l.length⟩
    let e3 : Fin (b :: a :: l).length ≃ Fin (b :: List.orderedInsert r a l).length :=
      Fin.equivCons e
    let e4 : Fin (b :: List.orderedInsert r a l).length ≃
        Fin (List.orderedInsert r a (b :: l)).length :=
      (Fin.castOrderIso (by
        rw [List.orderedInsert_length]
        simpa using List.orderedInsert_length r l a)).toEquiv
    e2.trans (e3.trans e4) := by
  simp [insertEquiv, hab]

lemma insertEquiv_get {α : Type} {r : α → α → Prop} [DecidableRel r] (a : α) : (l : List α) →
    (a :: l).get ∘ (insertEquiv r a l).symm = (List.orderedInsert r a l).get
  | [] => by
    simp [insertEquiv]
  | b :: l => by
    by_cases hr : r a b
    · rw [insertEquiv_cons_pos a b hr l]
      simp_all only [List.orderedInsert.eq_2, List.length_cons, OrderIso.toEquiv_symm,
        Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
      ext x : 1
      simp_all only [Function.comp_apply, Fin.castOrderIso_apply, List.get_eq_getElem,
        List.length_cons, Fin.coe_cast, ↓reduceIte]
    · rw [insertEquiv_cons_neg a b hr l]
      trans (b :: List.orderedInsert r a l).get ∘ Fin.cast (by
        rw [List.orderedInsert_length]
        simp [List.orderedInsert_length])
      · simp only [List.orderedInsert.eq_2, List.length_cons, Fin.zero_eta, Fin.mk_one]
        ext x
        match x with
        | ⟨0, h⟩ => rfl
        | ⟨Nat.succ x, h⟩ =>
          simp only [Nat.succ_eq_add_one, Function.comp_apply, Equiv.symm_trans_apply,
            Equiv.symm_swap, OrderIso.toEquiv_symm, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv,
            Fin.castOrderIso_apply, Fin.cast_mk, equivCons_symm_succ, List.get_eq_getElem,
            List.length_cons, List.getElem_cons_succ]
          have hswap (n : Fin (b :: a :: l).length) :
              (a :: b :: l).get (Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩ n) = (b :: a :: l).get n := by
            match n with
            | ⟨0, h⟩ => rfl
            | ⟨1, h⟩ => rfl
            | ⟨Nat.succ (Nat.succ x), h⟩ => rfl
          trans (a :: b :: l).get (Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩
            ((insertEquiv r a l).symm ⟨x, by simpa [List.orderedInsert_length, hr] using h⟩).succ)
          · simp
          · rw [hswap]
            simp only [List.length_cons, List.get_eq_getElem, Fin.val_succ, List.getElem_cons_succ]
            change _ = (List.orderedInsert r a l).get _
            rw [← insertEquiv_get (r := r) a l]
            simp
      · simp_all only [List.orderedInsert.eq_2, List.length_cons]
        ext x : 1
        simp_all only [Function.comp_apply, List.get_eq_getElem, List.length_cons, Fin.coe_cast,
          ↓reduceIte]

/-- The equivalence between `Fin l.length ≃ Fin (List.insertionSort r l).length` induced by the
  sorting algorithm. -/
def insertionSortEquiv {α : Type} (r : α → α → Prop) [DecidableRel r] : (l : List α) →
    Fin l.length ≃ Fin (List.insertionSort r l).length
  | [] => Equiv.refl _
  | a :: l =>
    (Fin.equivCons (insertionSortEquiv r l)).trans (insertEquiv r a (List.insertionSort r l))

lemma insertionSortEquiv_get {α : Type} {r : α → α → Prop} [DecidableRel r] : (l : List α) →
    l.get ∘ (insertionSortEquiv r l).symm = (List.insertionSort r l).get
  | [] => by
    simp [insertionSortEquiv]
  | a :: l => by
    rw [insertionSortEquiv]
    change ((a :: l).get ∘ ((Fin.equivCons (insertionSortEquiv r l))).symm) ∘
      (insertEquiv r a (List.insertionSort r l)).symm = _
    have hl : (a :: l).get ∘ ((Fin.equivCons (insertionSortEquiv r l))).symm =
        (a :: List.insertionSort r l).get := by
      ext x
      match x with
      | ⟨0, h⟩ => rfl
      | ⟨Nat.succ x, h⟩ =>
        change _ = (List.insertionSort r l).get _
        rw [← insertionSortEquiv_get (r := r) l]
        rfl
    rw [hl]
    rw [insertEquiv_get (r := r) a (List.insertionSort r l)]
    rfl

lemma insertionSort_eq_ofFn {α : Type} {r : α → α → Prop} [DecidableRel r] (l : List α) :
    List.insertionSort r l = List.ofFn (l.get ∘ (insertionSortEquiv r l).symm) := by
  rw [insertionSortEquiv_get (r := r)]
  exact Eq.symm (List.ofFn_get (List.insertionSort r l))

end HepLean.List
