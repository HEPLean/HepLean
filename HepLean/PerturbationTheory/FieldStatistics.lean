/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic
/-!

# Field statistics

Basic properties related to whether a field, or list of fields, is bosonic or fermionic.

-/

/-- A field can either be bosonic or fermionic in nature.
  That is to say, they can either have Bose-Einstein statistics or
  Fermi-Dirac statistics. -/
inductive FieldStatistic : Type where
  | bosonic : FieldStatistic
  | fermionic : FieldStatistic
deriving DecidableEq

namespace FieldStatistic

variable {𝓕 : Type}

/-- Field statics form a finite type. -/
instance : Fintype FieldStatistic where
  elems := {bosonic, fermionic}
  complete := by
    intro c
    cases c
    · exact Finset.mem_insert_self bosonic {fermionic}
    · refine Finset.insert_eq_self.mp ?_
      exact rfl

@[simp]
lemma fermionic_not_eq_bonsic : ¬ fermionic = bosonic := by
  intro h
  exact FieldStatistic.noConfusion h

lemma bonsic_eq_fermionic_false : bosonic = fermionic ↔ false := by
  simp only [reduceCtorEq, Bool.false_eq_true]

@[simp]
lemma neq_fermionic_iff_eq_bosonic (a : FieldStatistic) : ¬ a = fermionic ↔ a = bosonic := by
  fin_cases a
  · simp
  · simp

@[simp]
lemma bosonic_neq_iff_fermionic_eq (a : FieldStatistic) : ¬ bosonic = a ↔ fermionic = a := by
  fin_cases a
  · simp
  · simp

@[simp]
lemma fermionic_neq_iff_bosonic_eq (a : FieldStatistic) : ¬ fermionic = a ↔ bosonic = a := by
  fin_cases a
  · simp
  · simp

lemma eq_self_if_eq_bosonic {a : FieldStatistic} :
    (if a = bosonic then bosonic else fermionic) = a := by
  fin_cases a <;> rfl

lemma eq_self_if_bosonic_eq {a : FieldStatistic} :
    (if bosonic = a then bosonic else fermionic) = a := by
  fin_cases a <;> rfl

/-- The field statistics of a list of fields is fermionic if ther is an odd number of fermions,
  otherwise it is bosonic. -/
def ofList (s : 𝓕 → FieldStatistic) : (φs : List 𝓕) → FieldStatistic
  | [] => bosonic
  | φ :: φs => if s φ = ofList s φs then bosonic else fermionic

@[simp]
lemma ofList_singleton (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s [φ] = s φ := by
  simp only [ofList, Fin.isValue]
  rw [eq_self_if_eq_bosonic]

@[simp]
lemma ofList_freeMonoid (s : 𝓕 → FieldStatistic) (φ : 𝓕) : ofList s (FreeMonoid.of φ) = s φ :=
  ofList_singleton s φ

@[simp]
lemma ofList_empty (s : 𝓕 → FieldStatistic) : ofList s [] = bosonic := rfl

@[simp]
lemma ofList_append (s : 𝓕 → FieldStatistic) (φs φs' : List 𝓕) :
    ofList s (φs ++ φs') = if ofList s φs = ofList s φs' then bosonic else fermionic := by
  induction φs with
  | nil =>
    simp only [List.nil_append, ofList_empty, Fin.isValue, eq_self_if_bosonic_eq]
  | cons a l ih =>
    have hab (a b c : FieldStatistic) :
        (if a = (if b = c then bosonic else fermionic) then bosonic else fermionic) =
        if (if a = b then bosonic else fermionic) = c then bosonic else fermionic := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
    simp only [ofList, List.append_eq, Fin.isValue, ih, hab]

lemma ofList_eq_countP (s : 𝓕 → FieldStatistic) (φs : List 𝓕) :
    ofList s φs = if Nat.mod (List.countP (fun i => decide (s i = fermionic)) φs) 2 = 0 then
      bosonic else fermionic := by
  induction φs with
  | nil => simp
  | cons r0 r ih =>
    simp only [ofList]
    rw [List.countP_cons]
    simp only [decide_eq_true_eq]
    by_cases hr : s r0 = fermionic
    · simp only [hr, ↓reduceIte]
      simp_all only
      split
      next h =>
        simp_all only [↓reduceIte, fermionic_not_eq_bonsic]
        split
        next h_1 =>
          simp_all only [fermionic_not_eq_bonsic]
          have ha (a : ℕ) (ha : a % 2 = 0) : (a + 1) % 2 ≠ 0 := by
            omega
          exact ha (List.countP (fun i => decide (s i = fermionic)) r) h h_1
        next h_1 => simp_all only
      next h =>
        simp_all only [↓reduceIte]
        split
        next h_1 => rfl
        next h_1 =>
          simp_all only [reduceCtorEq]
          have ha (a : ℕ) (ha : ¬ a % 2 = 0) : (a + 1) % 2 = 0 := by
            omega
          exact h_1 (ha (List.countP (fun i => decide (s i = fermionic)) r) h)
    · simp only [neq_fermionic_iff_eq_bosonic] at hr
      by_cases hx : (List.countP (fun i => decide (s i = fermionic)) r).mod 2 = 0
      · simpa [hx, hr] using ih.symm
      · simpa [hx, hr] using ih.symm

lemma ofList_perm (s : 𝓕 → FieldStatistic) {l l' : List 𝓕} (h : l.Perm l') :
    ofList s l = ofList s l' := by
  rw [ofList_eq_countP, ofList_eq_countP, h.countP_eq]

lemma ofList_orderedInsert (s : 𝓕 → FieldStatistic) (le1 : 𝓕 → 𝓕 → Prop) [DecidableRel le1]
    (φs : List 𝓕) (φ : 𝓕) : ofList s (List.orderedInsert le1 φ φs) = ofList s (φ :: φs) :=
  ofList_perm s (List.perm_orderedInsert le1 φ φs)

@[simp]
lemma ofList_insertionSort (s : 𝓕 → FieldStatistic) (le1 : 𝓕 → 𝓕 → Prop) [DecidableRel le1]
    (φs : List 𝓕) : ofList s (List.insertionSort le1 φs) = ofList s φs :=
  ofList_perm s (List.perm_insertionSort le1 φs)

end FieldStatistic
