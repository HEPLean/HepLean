/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Mathematics.List
import HepLean.PerturbationTheory.Wick.Signs.SuperCommuteCoef
/-!

# Insert sign

-/

namespace Wick
open HepLean.List
open FieldStatistic

section
/-!

## Basic properties of lists

To be replaced with Mathlib or Lean definitions when/where appropraite.
-/

lemma take_insert_same {I : Type} (i : I) :
    (n : ℕ) → (r : List I) →
    List.take n (List.insertIdx n i r) = List.take n r
  | 0, _ => by simp
  | _+1, [] => by simp
  | n+1, a::as => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.cons.injEq, true_and]
    exact take_insert_same i n as

lemma take_eraseIdx_same {I : Type} :
    (n : ℕ) → (r : List I) →
    List.take n (List.eraseIdx r n) = List.take n r
  | 0, _ => by simp
  | _+1, [] => by simp
  | n+1, a::as => by
    simp only [List.eraseIdx_cons_succ, List.take_succ_cons, List.cons.injEq, true_and]
    exact take_eraseIdx_same n as

lemma take_insert_gt {I : Type} (i : I) :
    (n m : ℕ) → (h : n < m) → (r : List I) →
    List.take n (List.insertIdx m i r) = List.take n r
  | 0, 0, _, _ => by simp
  | 0, m + 1, _, _ => by simp
  | n+1, m + 1, _, [] => by simp
  | n+1, m + 1, h, a::as => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.cons.injEq, true_and]
    refine take_insert_gt i n m (Nat.succ_lt_succ_iff.mp h) as

lemma take_insert_let {I : Type} (i : I) :
    (n m : ℕ) → (h : m ≤ n) → (r : List I) → (hm : m ≤ r.length) →
    (List.take (n + 1) (List.insertIdx m i r)).Perm (i :: List.take n r)
  | 0, 0, h, _, _ => by simp
  | m + 1, 0, h, r, _ => by simp
  | n + 1, m + 1, h, [], hm => by
    simp at hm
  | n + 1, m + 1, h, a::as, hm => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons]
    have hp : (i :: a :: List.take n as).Perm (a :: i :: List.take n as) := by
      exact List.Perm.swap a i (List.take n as)
    refine List.Perm.trans ?_ hp.symm
    refine List.Perm.cons a ?_
    exact take_insert_let i n m (Nat.le_of_succ_le_succ h) as (Nat.le_of_succ_le_succ hm)

end

/-!

## Insert sign

-/

section InsertSign

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic)

/-- The sign associated with inserting a field `φ` into a list of fields `φs` at
  the `n`th position. -/
def insertSign (n : ℕ) (φ : 𝓕) (φs : List 𝓕) : ℂ :=
  superCommuteCoef q [φ] (List.take n φs)

/-- If `φ` is bosonic, there is no sign associated with inserting it into a list of fields. -/
lemma insertSign_bosonic (n : ℕ)  (φ : 𝓕) (φs : List 𝓕) (hφ : q φ = bosonic) :
    insertSign q n φ φs = 1 := by
  simp only [insertSign, superCommuteCoef, ofList_singleton, hφ, reduceCtorEq, false_and,
    ↓reduceIte]

lemma insertSign_insert (n : ℕ) (φ : 𝓕) (φs : List 𝓕) :
    insertSign q n φ φs = insertSign q n φ (List.insertIdx n φ φs) := by
  simp only [insertSign]
  congr 1
  rw [take_insert_same]

lemma insertSign_eraseIdx (n : ℕ) (φ : 𝓕) (φs : List 𝓕) :
    insertSign q n φ (φs.eraseIdx n) = insertSign q n φ φs := by
  simp only [insertSign]
  congr 1
  rw [take_eraseIdx_same]

lemma insertSign_zero (φ : 𝓕) (φs : List 𝓕) : insertSign q 0 φ φs = 1 := by
  simp [insertSign, superCommuteCoef]

lemma insertSign_succ_cons (n : ℕ) (φ0 φ1 : 𝓕) (φs : List 𝓕) : insertSign q (n + 1) φ0 (φ1 :: φs) =
    superCommuteCoef q [φ0] [φ1] * insertSign q n φ0 φs := by
  simp only [insertSign, List.take_succ_cons]
  rw [superCommuteCoef_cons]

lemma insertSign_insert_gt (n m : ℕ) (φ0 φ1 : 𝓕) (φs : List 𝓕) (hn : n < m) :
    insertSign q n φ0 (List.insertIdx m φ1 φs) = insertSign q n φ0 φs := by
  rw [insertSign, insertSign]
  congr 1
  exact take_insert_gt φ1 n m hn φs

lemma insertSign_insert_lt_eq_insertSort (n m : ℕ) (φ0 φ1 : 𝓕) (φs : List 𝓕) (hn : m ≤ n)
    (hm : m ≤ φs.length) :
    insertSign q (n + 1) φ0 (List.insertIdx m φ1 φs) = insertSign q (n + 1) φ0 (φ1 :: φs) := by
  rw [insertSign, insertSign]
  apply superCommuteCoef_perm_snd
  simp only [List.take_succ_cons]
  refine take_insert_let φ1 n m hn φs hm

lemma insertSign_insert_lt (n m : ℕ) (φ0 φ1 : 𝓕) (φs : List 𝓕) (hn : m ≤ n) (hm : m ≤ φs.length) :
    insertSign q (n + 1) φ0 (List.insertIdx m φ1 φs) = superCommuteCoef q [φ0] [φ1] *
    insertSign q n φ0 φs := by
  rw [insertSign_insert_lt_eq_insertSort, insertSign_succ_cons]
  · exact hn
  · exact hm

end InsertSign

end Wick
