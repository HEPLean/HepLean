/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Mathematics.List
/-!
# List lemmas

-/
namespace HepLean.List

open Fin
open HepLean
variable {n : Nat}

lemma insertIdx_map {I J : Type} (f : I → J) : (i : ℕ) → (r : List I) → (r0 : I) →
    (List.insertIdx i r0 r).map f = List.insertIdx i (f r0) (r.map f)
  | 0, [], r0 => by simp
  | n+1, [], r0 => by simp
  | 0, a::as, r0 => by simp
  | n+1, a::as, r0 => by
    simp
    exact insertIdx_map f n as r0

lemma eraseIdx_sorted {I : Type} (le : I → I → Prop) :
    (r : List I) → (n : ℕ) →
    List.Sorted le r → List.Sorted le (r.eraseIdx n)
  | [], _, _ => by simp
  | a::as, 0, h => by
    simp [List.eraseIdx]
    simp at h
    exact h.2
  | a::as, n+1, h => by
    simp
    simp at h
    refine And.intro ?_ (eraseIdx_sorted le as n h.2)
    intro b hb
    refine h.1 _ ?_
    exact List.mem_of_mem_eraseIdx hb

lemma mem_eraseIdx_nodup {I : Type} (i : I) :
    (l : List I) → (n : ℕ) → (hn : n < l.length) → (h : List.Nodup l) →
    i ∈ l.eraseIdx n ↔ i ∈ l ∧ i ≠ l[n]
  | [], _, _, _ => by simp
  | a1 :: as, 0, _, h => by
    simp
    by_cases hi : i = a1
    · subst hi
      simp at h
      simp [h]
    · simp [hi]
  | a1 :: as, n+1, hn, h => by
    simp
    simp at h
    rw [mem_eraseIdx_nodup i as n (Nat.succ_lt_succ_iff.mp hn) h.2]
    simp_all only [ne_eq]
    obtain ⟨left, right⟩ := h
    apply Iff.intro
    · intro a
      cases a with
      | inl h =>
        subst h
        simp_all only [or_false, true_and]
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [List.getElem_mem, not_true_eq_false]
      | inr h_1 => simp_all only [or_true, not_false_eq_true, and_self]
    · intro a
      simp_all only [not_false_eq_true, and_true]

lemma insertIdx_eq_take_drop {I : Type} (i : I) : (r : List I) → (n : Fin r.length.succ) →
    List.insertIdx n i r = List.take n r ++ i :: r.drop n
  | [], 0 => by simp
  | a :: as, 0 => by
    simp
  | a :: as, ⟨n + 1, h⟩ => by
    simp
    exact insertIdx_eq_take_drop i as ⟨n, Nat.succ_lt_succ_iff.mp h⟩

@[simp]
lemma insertIdx_length_fin {I : Type} (i : I) :
    (r : List I) → (n : Fin r.length.succ) →
    (List.insertIdx n i r).length = r.length.succ
  | [], 0 => by simp
  | a :: as, 0 => by simp
  | a :: as, ⟨n + 1, h⟩ => by
    simp
    exact insertIdx_length_fin i as ⟨n, Nat.succ_lt_succ_iff.mp h⟩

@[simp]
lemma insertIdx_getElem_fin {I : Type} (i : I) :
    (r : List I) → (k : Fin r.length.succ) → (m : Fin r.length) →
    (List.insertIdx k i r)[(k.succAbove m).val] = r[m.val]
  | [], 0, m => by exact Fin.elim0 m
  | a :: as, 0, m => by simp
  | a :: as, ⟨n + 1, h⟩, ⟨0, h0⟩ => by
    simp [Fin.succAbove, Fin.lt_def]
  | a :: as, ⟨n + 1, h⟩, ⟨m+1, hm⟩ => by
    simp
    conv_rhs => rw [← insertIdx_getElem_fin i as ⟨n, Nat.succ_lt_succ_iff.mp h⟩
      ⟨m, Nat.lt_of_succ_lt_succ hm⟩]
    simp [Fin.succAbove, Fin.lt_def]
    split
    · simp_all only [List.getElem_cons_succ]
    · simp_all only [List.getElem_cons_succ]

@[simp]
lemma insertIdx_getElem_self {I : Type} (i : I) :
    (r : List I) → (k : Fin r.length.succ) →
    (List.insertIdx k i r)[k.val] = i
  | [], 0 => by simp
  | a :: as, 0 => by simp
  | a :: as, ⟨n + 1, h⟩ => by
    simp

@[simp]
lemma insertIdx_eraseIdx_fin {I : Type} :
    (r : List I) → (k : Fin r.length) →
    (List.eraseIdx r k).insertIdx k r[k] = r
  | [], k => by exact Fin.elim0 k
  | a :: as, ⟨0, h⟩ => by simp
  | a :: as, ⟨n + 1, h⟩ => by
    simp
    exact insertIdx_eraseIdx_fin as ⟨n, Nat.lt_of_succ_lt_succ h⟩

lemma get_eq_insertIdx_succAbove {I : Type} (i : I) (r : List I) (k : Fin r.length.succ) :
    r.get = (List.insertIdx k i r).get ∘
    (finCongr (insertIdx_length_fin i r k).symm) ∘ k.succAbove := by
  funext i
  simp

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

lemma drop_eraseIdx_succ {I : Type} :
    (n : ℕ) → (r : List I) → (hn : n < r.length) →
    r[n] :: List.drop n (List.eraseIdx r n) = List.drop n r
  | 0, _, _=> by
    simp
    rw [@List.getElem_zero]
    exact List.head_cons_tail _ _
  | n+1, [], hn => by simp at hn
  | n+1, a::as, hn => by
    simp [List.eraseIdx_cons_succ, List.drop_succ_cons, List.cons.injEq, true_and]
    refine drop_eraseIdx_succ n as _

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

end HepLean.List
