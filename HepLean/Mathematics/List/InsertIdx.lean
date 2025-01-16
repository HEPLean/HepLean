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

lemma insertIdx_map {I J : Type} (f : I → J) : (i : ℕ) →  (r : List I) →  (r0 : I) →
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
    (l : List I) →  (n : ℕ) →  (hn : n < l.length) →  (h : List.Nodup l) →
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

lemma insertIdx_eq_take_drop {I : Type} (i : I) :
     (r : List I) → (n : Fin r.length.succ) →
    List.insertIdx n i r = List.take n r ++ i ::  r.drop n
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
  | a :: as, ⟨n + 1, h⟩, ⟨0, h0⟩  => by
    simp [Fin.succAbove, Fin.lt_def]
  | a :: as, ⟨n + 1, h⟩, ⟨m+1, hm⟩  => by
    simp
    conv_rhs => rw [← insertIdx_getElem_fin i as ⟨n, Nat.succ_lt_succ_iff.mp h⟩ ⟨m, Nat.lt_of_succ_lt_succ hm⟩]
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
    rw [insertIdx_getElem_self i as ⟨n, Nat.succ_lt_succ_iff.mp h⟩]


@[simp]
lemma insertIdx_eraseIdx_fin {I : Type} :
    (r : List I) → (k : Fin r.length) →
    (List.eraseIdx r k).insertIdx k r[k] = r
  | [], k => by exact Fin.elim0 k
  | a :: as, ⟨0, h⟩ => by simp
  | a :: as, ⟨n + 1, h⟩ => by
    simp
    exact insertIdx_eraseIdx_fin  as ⟨n, Nat.lt_of_succ_lt_succ h⟩

lemma get_eq_insertIdx_succAbove {I : Type} (i : I) (r : List I) (k : Fin r.length.succ) :
    r.get = (List.insertIdx k i r).get ∘
    (finCongr (insertIdx_length_fin i r k).symm) ∘ k.succAbove := by
  funext i
  simp



end HepLean.List
