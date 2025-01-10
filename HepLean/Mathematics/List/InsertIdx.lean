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



end HepLean.List
