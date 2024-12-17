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

def orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    Fin (List.orderedInsert le1 r0 r).length :=
  ⟨(List.takeWhile (fun b => decide ¬ le1 r0 b) r).length, by
    rw [List.orderedInsert_length]
    have h1 : (List.takeWhile (fun b => decide ¬le1 r0 b) r).length ≤ r.length :=
      List.Sublist.length_le (List.takeWhile_sublist fun b => decide ¬le1 r0 b)
    omega⟩

lemma orderedInsertPos_lt_length {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) : orderedInsertPos le1 r r0 < (r0 :: r).length := by
  simp only [orderedInsertPos, List.length_cons]
  have h1 : (List.takeWhile (fun b => decide ¬le1 r0 b) r).length ≤ r.length :=
    List.Sublist.length_le (List.takeWhile_sublist fun b => decide ¬le1 r0 b)
  omega

@[simp]
lemma orderedInsert_get_orderedInsertPos {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) :
    (List.orderedInsert le1 r0 r)[(orderedInsertPos le1 r r0).val] = r0 := by
  simp [orderedInsertPos, List.orderedInsert_eq_take_drop]
  rw [List.getElem_append]
  simp


@[simp]
lemma orderedInsert_get_lt {I : Type} (le1 : I → I → Prop) [DecidableRel le1]
    (r : List I) (r0 : I) (i : Fin (List.orderedInsert le1 r0 r).length)
    (hi : i.val < orderedInsertPos le1 r r0) :
    (List.orderedInsert le1 r0 r)[i] = r.get ⟨i, by
      simp only [orderedInsertPos] at hi
      have h1 : (List.takeWhile (fun b => decide ¬le1 r0 b) r).length ≤ r.length :=
        List.Sublist.length_le (List.takeWhile_sublist fun b => decide ¬le1 r0 b)
      omega⟩ := by
  simp [orderedInsertPos] at hi
  simp [List.orderedInsert_eq_take_drop]
  rw [List.getElem_append]
  simp [hi]
  rw [List.IsPrefix.getElem]
  exact List.takeWhile_prefix fun b => !decide (le1 r0 b)

def orderedInsertEquiv  {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I) (r0 : I) :
    Fin (r0 :: r).length ≃ Fin (List.orderedInsert le1 r0 r).length := by
  let e2 : Fin (List.orderedInsert le1 r0 r).length ≃ Fin (r0 :: r).length :=
    (Fin.castOrderIso (List.orderedInsert_length le1 r r0)).toEquiv
  let e3 : Fin (r0 :: r).length ≃ Fin 1 ⊕ Fin (r).length := finExtractOne 0
  let e4 : Fin (r0 :: r).length ≃ Fin 1 ⊕ Fin (r).length := finExtractOne ⟨orderedInsertPos le1 r r0, orderedInsertPos_lt_length le1 r r0⟩
  exact e3.trans (e4.symm.trans e2.symm)

@[simp]
lemma orderedInsertEquiv_zero {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) : orderedInsertEquiv le1 r r0 ⟨0, by simp⟩ = orderedInsertPos le1 r r0 := by
  simp [orderedInsertEquiv]

@[simp]
lemma orderedInsertEquiv_succ {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) (n : ℕ) (hn : Nat.succ n < (r0 :: r).length) :
    orderedInsertEquiv le1 r r0 ⟨Nat.succ n, hn⟩ = Fin.cast (List.orderedInsert_length le1 r r0).symm
    ((Fin.succAbove ⟨(orderedInsertPos le1 r r0), orderedInsertPos_lt_length le1 r r0⟩) ⟨n, Nat.succ_lt_succ_iff.mp hn⟩) := by
  simp [orderedInsertEquiv]
  match r with
  | [] =>
    simp
  | r1 :: r =>
    erw [finExtractOne_apply_neq]
    simp [orderedInsertPos]
    rfl
    exact ne_of_beq_false rfl


lemma get_eq_orderedInsertEquiv {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (r0 : I) :
    (r0 :: r).get = (List.orderedInsert le1 r0 r).get ∘ (orderedInsertEquiv le1 r r0) := by
  funext x
  match x with
  | ⟨0, h⟩ =>
    simp
    erw [orderedInsertEquiv_zero]
    simp
  | ⟨Nat.succ n, h⟩ =>
    simp
    erw [orderedInsertEquiv_succ]
    simp [Fin.succAbove]
    by_cases hn : n < ↑(orderedInsertPos le1 r r0)
    · simp [hn]
      erw [orderedInsert_get_lt le1 r r0 ⟨n, by omega⟩ ]
      rfl
      simpa using hn
    · simp [hn]
      simp [List.orderedInsert_eq_take_drop]
      rw [List.getElem_append]
      have hn' : ¬ n + 1 < (List.takeWhile (fun b => !decide (le1 r0 b)) r).length := by
        simp [orderedInsertPos]  at hn
        omega
      simp [hn']
      have hnn : n + 1 - (List.takeWhile (fun b => !decide (le1 r0 b)) r).length =
        (n - (List.takeWhile (fun b => !decide (le1 r0 b)) r).length) + 1 := by
        simp [orderedInsertPos]  at hn
        omega
      simp [hnn]
      conv_rhs =>
        rw [List.IsSuffix.getElem (List.dropWhile_suffix fun b => !decide (le1 r0 b))]
      congr
      have hr : r.length = (List.takeWhile (fun b => !decide (le1 r0 b)) r).length +  (List.dropWhile (fun b => !decide (le1 r0 b)) r).length := by
        rw [← List.length_append]
        congr
        exact Eq.symm (List.takeWhile_append_dropWhile (fun b => !decide (le1 r0 b)) r)
      simp [hr]
      omega


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

lemma insertionSort_get_comp_insertionSortEquiv  {α : Type} {r : α → α → Prop} [DecidableRel r] (l : List α)  :
    (List.insertionSort r l).get ∘ (insertionSortEquiv r l) = l.get := by
  rw [← insertionSortEquiv_get]
  funext x
  simp

lemma insertionSort_eq_ofFn {α : Type} {r : α → α → Prop} [DecidableRel r] (l : List α) :
    List.insertionSort r l = List.ofFn (l.get ∘ (insertionSortEquiv r l).symm) := by
  rw [insertionSortEquiv_get (r := r)]
  exact Eq.symm (List.ofFn_get (List.insertionSort r l))



def optionErase {I : Type} (l : List I) (i : Option (Fin l.length)) : List I :=
  match i with
  | none => l
  | some i => List.eraseIdx l i

def optionEraseZ {I : Type} (l : List I) (a : I) (i : Option (Fin l.length)) : List I :=
  match i with
  | none => a :: l
  | some i => List.eraseIdx l i

lemma eraseIdx_length {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).length + 1 = l.length := by
  simp [List.length_eraseIdx]
  have hi := i.prop
  omega

lemma eraseIdx_cons_length {I : Type} (a : I) (l : List I) (i : Fin (a :: l).length) :
    (List.eraseIdx (a :: l) i).length= l.length := by
  simp [List.length_eraseIdx]


lemma eraseIdx_get {I : Type} (l : List I) (i : Fin l.length) :
    (List.eraseIdx l i).get  = l.get ∘ (Fin.cast (eraseIdx_length l i)) ∘ (Fin.cast (eraseIdx_length l i).symm i).succAbove := by
  ext x
  simp only [Function.comp_apply, List.get_eq_getElem, List.eraseIdx, List.getElem_eraseIdx]
  simp [Fin.succAbove]
  by_cases hi: x.castSucc < Fin.cast (by exact Eq.symm (eraseIdx_length l i)) i
  · simp [ hi]
    intro h
    rw [Fin.lt_def] at hi
    simp_all
    omega
  · simp [ hi]
    rw [Fin.lt_def] at hi
    simp at hi
    have hn : ¬ x.val < i.val := by omega
    simp [hn]


lemma eraseIdx_insertionSort_length {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (n : Fin r.length ) :
    ((List.insertionSort le1 r).eraseIdx ↑((HepLean.List.insertionSortEquiv le1 r) n)).length
    = (List.insertionSort le1 (r.eraseIdx n)).length := by
  rw [List.length_eraseIdx]
  have hn := ((insertionSortEquiv le1 r) n).prop
  simp [List.length_insertionSort] at hn
  simp [hn]
  rw [List.length_eraseIdx]
  simp

lemma eraseIdx_insertionSort_get {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (n : Fin r.length ) :
    ((List.insertionSort le1 r).eraseIdx ↑((HepLean.List.insertionSortEquiv le1 r) n)).get
    = (List.insertionSort le1 (r.eraseIdx n)).get ∘ Fin.cast (eraseIdx_insertionSort_length le1 r n) := by
  rw [eraseIdx_get, ← insertionSortEquiv_get, ← insertionSortEquiv_get,
    eraseIdx_get]

@[simp]
lemma eraseIdx_orderedInsert_zero {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
     (r0 : I) :
    (List.orderedInsert le1 r0 r).eraseIdx ↑((insertEquiv le1 r0 r) ⟨0, by simp⟩) = r := by
  induction r with
  | nil => simp
  | cons r1 r ih =>
    by_cases hr0 : le1 r0 r1
    · simp [hr0, insertEquiv]
    · simp [hr0, insertEquiv, equivCons]
      simpa using ih

@[simp]
lemma eraseIdx_orderedInsert_succ_succ {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
     (r0 : I) (n : ℕ) (hn : Nat.succ (Nat.succ n) < (r0 :: r).length) :
    (List.orderedInsert le1 r0 r).eraseIdx ↑((insertEquiv le1 r0 r) ⟨Nat.succ (Nat.succ n), hn⟩) =
    List.orderedInsert le1 r0 (r.eraseIdx (Nat.succ n)) := by
  induction r with
  | nil => simp at hn
  | cons r1 r ih =>
    by_cases hr0 : le1 r0 r1
    · simp [hr0, insertEquiv]
    · simp [hr0, insertEquiv]
      rw [Equiv.swap_apply_of_ne_of_ne]
      simp
      have h1 (n : ℕ) (hn : n + 1 < (r0 :: r).length) : (List.orderedInsert le1 r0 r).eraseIdx ↑((insertEquiv le1 r0 r) ⟨n + 1, hn⟩) =
        List.orderedInsert le1 r0 (r.eraseIdx n) := by
        match n with
        | 0 => simp
        | Nat.succ n =>
          exact ih ?_
        sorry
      exact h1 n (Nat.succ_lt_succ_iff.mp hn)
      simp
      rw [Fin.ext_iff]
      simp
      simp
      rw [Fin.ext_iff]
      simp

lemma eraseIdx_insertionSort_zero {I : Type} (le1 : I → I → Prop) [DecidableRel le1] (r : List I)
    (h0 : 0 < r.length) :
    ((List.insertionSort le1 r).eraseIdx ↑((HepLean.List.insertionSortEquiv le1 r) ⟨0, h0⟩))
    = (List.insertionSort le1 (r.eraseIdx 0)) := by
  induction r with
  | nil => simp
  | cons r0 r ih =>
    simp [insertionSortEquiv]
    erw [eraseIdx_orderedInsert_zero]

lemma eraseIdx_insertionSort_succ {I : Type} (le1 : I → I → Prop) [DecidableRel le1] :
    (n : ℕ) →  (r : List I) → (hn :  n < r.length) →
    ((List.insertionSort le1 r).eraseIdx ↑((HepLean.List.insertionSortEquiv le1 r) ⟨n, hn⟩))
    = (List.insertionSort le1 (r.eraseIdx n))
  | 0, _, _ => by exact eraseIdx_insertionSort_zero le1 _ _
  | Nat.succ n, [], hn => by
    simp [insertionSortEquiv]
  | Nat.succ 0, (r0 :: r), hn => by
    simp [insertionSortEquiv]



  | Nat.succ (Nat.succ n), (r0 :: r), hn => by
    simp [insertionSortEquiv]
    rw [eraseIdx_orderedInsert_succ_succ]
    exact eraseIdx_insertionSort_succ n r (Nat.lt_of_succ_lt hn)


end HepLean.List
