/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Mathematics.List
import HepLean.PerturbationTheory.Wick.Signs.SuperCommuteCoef
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick
open HepLean.List


def insertSign {I : Type} (q : I → Fin 2) (n : ℕ) (r0 : I) (r : List I) : ℂ :=
  superCommuteCoef q [r0] (List.take n r)

lemma take_insert_same {I : Type} (i : I) :
    (n : ℕ) → (r : List I) →
    List.take n (List.insertIdx n i r) = List.take n r
  | 0, _ => by simp
  | _+1, [] => by simp
  | n+1, a::as => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.cons.injEq, true_and]
    exact take_insert_same i n as

lemma insertSign_insert {I : Type} (q : I → Fin 2) (n : ℕ)
    (r0 : I) (r : List I) : insertSign q n r0 r = insertSign q n r0 (List.insertIdx n r0 r) := by
  simp only [insertSign]
  congr 1
  rw [take_insert_same]

lemma take_eraseIdx_same {I : Type} :
    (n : ℕ) → (r : List I) →
    List.take n (List.eraseIdx r n) = List.take n r
  | 0, _ => by simp
  | _+1, [] => by simp
  | n+1, a::as => by
    simp only [List.eraseIdx_cons_succ, List.take_succ_cons, List.cons.injEq, true_and]
    exact take_eraseIdx_same n as

lemma insertSign_eraseIdx {I : Type} (q : I → Fin 2) (n : ℕ)
    (r0 : I) (r : List I) : insertSign q n r0 (r.eraseIdx n) = insertSign q n r0 r := by
  simp only [insertSign]
  congr 1
  rw [take_eraseIdx_same]

lemma insertSign_zero {I : Type} (q : I → Fin 2) (r0 : I) (r : List I) :
    insertSign q 0 r0 r = 1 := by
  simp [insertSign, superCommuteCoef]

lemma insertSign_succ_cons {I : Type} (q : I → Fin 2) (n : ℕ)
    (r0 r1 : I) (r : List I) : insertSign q (n + 1) r0 (r1 :: r) =
    superCommuteCoef q [r0] [r1] * insertSign q n r0 r := by
  simp only [insertSign, List.take_succ_cons]
  rw [superCommuteCoef_cons]

lemma take_insert_gt {I : Type} (i : I) :
    (n m : ℕ) → (h : n < m) → (r : List I) →
    List.take n (List.insertIdx m i r) = List.take n r
  | 0, 0, _, _ => by simp
  | 0, m + 1, _, _ => by simp
  | n+1, m + 1, _, [] => by simp
  | n+1, m + 1, h, a::as => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.cons.injEq, true_and]
    refine take_insert_gt i n m (Nat.succ_lt_succ_iff.mp h) as

lemma insertSign_insert_gt {I : Type} (q : I → Fin 2) (n m : ℕ)
    (r0 r1 : I) (r : List I) (hn : n < m) :
    insertSign q n r0 (List.insertIdx m r1 r) = insertSign q n r0 r := by
  rw [insertSign, insertSign]
  congr 1
  exact take_insert_gt r1 n m hn r

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

lemma insertSign_insert_lt_eq_insertSort {I : Type} (q : I → Fin 2) (n m : ℕ)
    (r0 r1 : I) (r : List I) (hn : m ≤ n) (hm : m ≤ r.length) :
    insertSign q (n + 1) r0 (List.insertIdx m r1 r) = insertSign q (n + 1) r0 (r1 :: r) := by
  rw [insertSign, insertSign]
  apply superCommuteCoef_perm_snd
  simp only [List.take_succ_cons]
  refine take_insert_let r1 n m hn r hm

lemma insertSign_insert_lt {I : Type} (q : I → Fin 2) (n m : ℕ)
    (r0 r1 : I) (r : List I) (hn : m ≤ n) (hm : m ≤ r.length) :
    insertSign q (n + 1) r0 (List.insertIdx m r1 r) = superCommuteCoef q [r0] [r1] *
    insertSign q n r0 r := by
  rw [insertSign_insert_lt_eq_insertSort, insertSign_succ_cons]
  exact hn
  exact hm

end Wick
