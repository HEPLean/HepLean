/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Species
import HepLean.Lorentz.RealVector.Basic
import HepLean.Mathematics.Fin
import HepLean.SpaceTime.Basic
import HepLean.Mathematics.SuperAlgebra.Basic
import HepLean.Mathematics.List
import HepLean.Meta.Notes.Basic
import Init.Data.List.Sort.Basic
import Mathlib.Data.Fin.Tuple.Take
import HepLean.PerturbationTheory.Wick.Koszul.Order
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick
open HepLean.List

def grade {I : Type} (q : I → Fin 2) : (l : List I) → Fin 2
  | [] => 0
  | a :: l => if q a = grade q l then 0 else 1

@[simp]
lemma grade_freeMonoid  {I : Type} (q : I → Fin 2) (i : I) : grade q (FreeMonoid.of i) = q i := by
  simp only [grade, Fin.isValue]
  have ha (a : Fin 2) : (if a = 0 then 0 else 1) = a := by
    fin_cases a <;> rfl
  rw [ha]

@[simp]
lemma grade_empty {I : Type} (q : I → Fin 2) : grade q [] = 0 := by
  simp [grade]

@[simp]
lemma grade_append {I : Type} (q : I → Fin 2) (l r : List I) :
    grade q (l ++ r) = if grade q l = grade q r then 0 else 1 := by
  induction l with
  | nil =>
    simp only [List.nil_append, grade_empty, Fin.isValue]
    have ha (a : Fin 2) : (if 0 = a then 0 else 1) = a := by
      fin_cases a <;> rfl
    exact Eq.symm (Fin.eq_of_val_eq (congrArg Fin.val (ha (grade q r))))
  | cons a l ih =>
    simp only [grade, List.append_eq, Fin.isValue]
    erw [ih]
    have hab (a b c : Fin 2) : (if a = if b = c then 0 else 1 then (0 : Fin 2) else 1) =
         if (if a = b then 0 else 1) = c then 0 else 1 := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
    exact hab (q a) (grade q l) (grade q r)

lemma grade_orderedInsert {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (l : List I) ( i : I ) :
    grade q (List.orderedInsert le1 i l) = grade q (i :: l) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.orderedInsert]
    by_cases hij : le1 i j
    · simp [hij]
    · simp only [hij, ↓reduceIte]
      rw [grade]
      rw [ih]
      simp only [grade, Fin.isValue]
      have h1 (a b c : Fin 2) : (if a = if b = c then 0 else 1 then (0 : Fin 2) else 1) = if b = if a = c then 0 else 1 then 0 else 1 := by
        fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
      exact h1 _ _ _

@[simp]
lemma grade_insertionSort {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (l : List I) :
    grade q (List.insertionSort le1 l) = grade q l := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.insertionSort, grade, Fin.isValue]
    rw [grade_orderedInsert]
    simp only [grade, Fin.isValue]
    rw [ih]

lemma grade_count {I : Type} (q : I → Fin 2) (l : List I) :
    grade q l = if Nat.mod (List.countP (fun i => decide (q i = 1)) l) 2 = 0 then 0 else  1 := by
  induction l with
  | nil => simp
  | cons r0 r ih =>
    simp only [grade, Fin.isValue]
    rw [List.countP_cons]
    simp only [Fin.isValue, decide_eq_true_eq]
    rw [ih]
    by_cases h: q r0 = 1
    · simp only [h, Fin.isValue, ↓reduceIte]
      split
      next h1 =>
        simp_all only [Fin.isValue, ↓reduceIte, one_ne_zero]
        split
        next h2 =>
          simp_all only [Fin.isValue, one_ne_zero]
          have ha (a : ℕ) (ha : a % 2 = 0) : (a + 1) % 2 ≠ 0 := by
            omega
          exact ha (List.countP (fun i => decide (q i = 1)) r) h1 h2
        next h2 => simp_all only [Fin.isValue]
      next h1 =>
        simp_all only [Fin.isValue, ↓reduceIte]
        split
        next h2 => simp_all only [Fin.isValue]
        next h2 =>
          simp_all only [Fin.isValue, zero_ne_one]
          have ha (a : ℕ) (ha : ¬  a % 2 = 0) : (a + 1) % 2 = 0 := by
            omega
          exact h2 (ha (List.countP (fun i => decide (q i = 1)) r) h1)
    · have h0 : q r0 = 0 := by omega
      simp only [h0, Fin.isValue, zero_ne_one, ↓reduceIte, add_zero]
      by_cases hn : (List.countP (fun i => decide (q i = 1)) r).mod 2 = 0
      · simp [hn]
      · simp [hn]

lemma grade_perm {I : Type} (q : I → Fin 2) {l l' : List I} (h : l.Perm l') :
    grade q l = grade q l' := by
  rw [grade_count, grade_count, h.countP_eq]

def superCommuteCoef {I : Type} (q : I → Fin 2) (la lb : List I) : ℂ :=
  if grade q la = 1 ∧ grade q lb = 1 then - 1 else  1

lemma superCommuteCoef_comm  {I : Type} (q : I → Fin 2) (la lb : List I) :
    superCommuteCoef q la lb = superCommuteCoef q lb la := by
  simp only [superCommuteCoef, Fin.isValue]
  congr 1
  exact Eq.propIntro (fun a => id (And.symm a)) fun a => id (And.symm a)

lemma superCommuteCoef_perm_snd {I : Type} (q : I → Fin 2) (la lb lb' : List I)
    (h : lb.Perm lb') :
    superCommuteCoef q la lb = superCommuteCoef q la lb' := by
  rw [superCommuteCoef, superCommuteCoef, grade_perm q h ]

lemma superCommuteCoef_mul_self {I : Type} (q : I → Fin 2) (l lb : List I) :
    superCommuteCoef q l lb * superCommuteCoef q l lb  = 1 := by
  simp only [superCommuteCoef, Fin.isValue, mul_ite, mul_neg, mul_one]
  have ha (a b : Fin 2) :  (if a = 1 ∧ b = 1 then -if a = 1 ∧ b = 1 then -1 else 1
    else if a = 1 ∧ b = 1 then -1 else 1)  = (1 : ℂ) := by
      fin_cases a <;> fin_cases b
      any_goals rfl
      simp
  exact ha (grade q l) (grade q lb)

lemma superCommuteCoef_empty {I : Type} (q : I → Fin 2) (la : List I) :
    superCommuteCoef q la [] = 1 := by
  simp only [superCommuteCoef, Fin.isValue, grade_empty, zero_ne_one, and_false, ↓reduceIte]

lemma superCommuteCoef_append {I : Type} (q : I → Fin 2) (la lb lc  : List I) :
    superCommuteCoef q la (lb ++ lc) = superCommuteCoef q la lb * superCommuteCoef q la lc := by
  simp only [superCommuteCoef, Fin.isValue, grade_append, ite_eq_right_iff, zero_ne_one, imp_false,
    mul_ite, mul_neg, mul_one]
  by_cases hla : grade q la = 1
  · by_cases hlb : grade q lb = 1
    · by_cases hlc : grade q lc = 1
      · simp [hlc, hlb, hla]
      · have hc : grade q lc = 0 := by
          omega
        simp [hc, hlb, hla]
    · have hb : grade q lb = 0 := by
        omega
      by_cases hlc : grade q lc = 1
      · simp [hlc, hb]
      · have hc : grade q lc = 0 := by
          omega
        simp [hc, hb]
  · have ha : grade q la = 0 := by
      omega
    simp [ha]

lemma superCommuteCoef_cons {I : Type} (q : I → Fin 2) (i : I) (la lb  : List I) :
    superCommuteCoef q la (i :: lb) = superCommuteCoef q la [i] * superCommuteCoef q la lb := by
  trans superCommuteCoef q la ([i] ++ lb)
  simp only [List.singleton_append]
  rw [superCommuteCoef_append]

def superCommuteCoefM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) : ℂ :=
    (if grade (fun i => q i.fst) l = 1 ∧ grade q r = 1 then -1 else 1)

lemma superCommuteCoefM_empty  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)):
    superCommuteCoefM q l [] = 1 := by
  simp [superCommuteCoefM]

def superCommuteCoefLE  {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (n : Fin r.length) : ℂ  :=
  koszulSign le1 q r *
  superCommuteCoef q [i] (List.take (↑((HepLean.List.insertionSortEquiv le1 r) n))
    (List.insertionSort le1 r)) *
  koszulSign le1 q (r.eraseIdx ↑n)

lemma superCommuteCoefLE_eq_q {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (n : Fin r.length)
    (hq : q i = q (r.get n)) :
    superCommuteCoefLE q le1 r i n =
    koszulSign le1 q r *
    superCommuteCoef q [r.get n] (List.take (↑(insertionSortEquiv le1 r n))
      (List.insertionSort le1 r)) *
    koszulSign le1 q (r.eraseIdx ↑n) := by
  simp [superCommuteCoefLE, superCommuteCoef, grade, hq]


lemma koszulSignInsert_eq_filter {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (r0 : I)
     :  (r : List I) →
    koszulSignInsert le1 q r0 r = koszulSignInsert le1 q r0 (List.filter (fun i => decide (¬ le1 r0 i)) r)
  | [] => by
    simp [koszulSignInsert]
  | r1 :: r => by
    dsimp only [koszulSignInsert, Fin.isValue]
    simp only [Fin.isValue, List.filter, decide_not]
    by_cases h : le1 r0 r1
    · simp only [h, ↓reduceIte, decide_True, Bool.not_true]
      rw [koszulSignInsert_eq_filter]
      congr
      simp
    · simp only [h, ↓reduceIte, Fin.isValue, decide_False, Bool.not_false]
      dsimp only [Fin.isValue, koszulSignInsert]
      simp only [Fin.isValue, h, ↓reduceIte]
      rw [koszulSignInsert_eq_filter]
      congr
      simp only [decide_not]
      simp

lemma koszulSignInsert_eq_grade {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (r0 : I)
     (r : List I)  :
    koszulSignInsert le1 q r0 r = if grade q [r0] = 1 ∧
      grade q (List.filter (fun i => decide (¬ le1 r0 i)) r) = 1 then -1 else 1 := by
  induction r with
  | nil =>
    simp [koszulSignInsert]
  | cons r1 r ih =>
    rw [koszulSignInsert_eq_filter]
    by_cases hr1 : ¬ le1 r0 r1
    · rw [List.filter_cons_of_pos]
      · dsimp only [koszulSignInsert, Fin.isValue, decide_not]
        rw [if_neg hr1]
        dsimp only [Fin.isValue, grade, ite_eq_right_iff, zero_ne_one, imp_false, decide_not]
        simp only [Fin.isValue, decide_not, ite_eq_right_iff, zero_ne_one, imp_false]
        have ha (a b c : Fin 2) : (if a = 1 ∧ b = 1 then -if ¬a = 0 ∧
          c = 1 then -1 else (1 : ℂ)
          else if ¬a = 0 ∧ c = 1 then -1 else 1) =
         if ¬a = 0 ∧ ¬b = c then -1 else 1:= by
          fin_cases a <;> fin_cases b <;> fin_cases c
          any_goals rfl
          simp
        rw [← ha (q r0) (q r1) (grade q (List.filter (fun a => !decide (le1 r0 a)) r) )]
        congr
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [grade] using ih
        · rw [koszulSignInsert_eq_filter] at ih
          simpa [grade] using ih
      · simp [hr1]
    · rw [List.filter_cons_of_neg]
      simp only [decide_not, Fin.isValue]
      rw [koszulSignInsert_eq_filter] at ih
      simpa [grade] using ih
      simpa using hr1

lemma koszulSignInsert_eq_perm  {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) (r r' : List I)
    (a : I) [DecidableRel le1] (h : r.Perm r') :
    koszulSignInsert le1 q a r = koszulSignInsert le1 q a r' := by
  rw [koszulSignInsert_eq_grade]
  rw [koszulSignInsert_eq_grade]
  congr 1
  simp only [Fin.isValue, decide_not, eq_iff_iff, and_congr_right_iff]
  intro h'
  have hg : grade q (List.filter (fun i => !decide (le1 a i)) r)  =
      grade q (List.filter (fun i => !decide (le1 a i)) r') := by
    rw [grade_count, grade_count]
    rw [List.countP_filter, List.countP_filter]
    rw [h.countP_eq]
  rw [hg]

lemma koszulSignInsert_eq_sort {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) (r : List I)
    (a : I) [DecidableRel le1] :
    koszulSignInsert le1 q a r = koszulSignInsert le1 q a (List.insertionSort le1 r) := by
  apply koszulSignInsert_eq_perm
  exact List.Perm.symm (List.perm_insertionSort le1 r)


lemma koszulSignInsert_eq_cons {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
  [IsTotal I le1] [IsTrans I le1] (r0 : I)
     (r : List I)  :
    koszulSignInsert le1 q r0 r = koszulSignInsert le1 q r0 (r0 :: r):= by
  simp only [koszulSignInsert, Fin.isValue, and_self]
  have h1 : le1 r0 r0 := by
    simpa using IsTotal.total (r := le1) r0 r0
  simp [h1]

def insertSign {I : Type} (q : I → Fin 2) (n : ℕ)
    (r0 : I) (r : List I)  : ℂ :=
  superCommuteCoef q [r0] (List.take n r)

lemma take_insert_same {I : Type} (i : I) :
    (n : ℕ) → (r : List I)   →
    List.take n (List.insertIdx n i r) = List.take n r
  | 0,   _     => by simp
  | _+1, []    => by simp
  | n+1, a::as => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.cons.injEq, true_and]
    exact take_insert_same i n as

lemma insertSign_insert {I : Type} (q : I → Fin 2) (n : ℕ)
    (r0 : I) (r : List I) : insertSign q n r0 r = insertSign q n r0 (List.insertIdx n r0 r) := by
  simp only [insertSign]
  congr 1
  rw [take_insert_same]

lemma take_eraseIdx_same {I : Type} :
    (n : ℕ) → (r : List I)   →
    List.take n (List.eraseIdx r n) = List.take n r
  | 0,   _     => by simp
  | _+1, []    => by simp
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
    (n m : ℕ) → (h : n < m) → (r : List I)   →
    List.take n (List.insertIdx m i r) =  List.take n r
  | 0,  0, _,  _     => by simp
  | 0,  m + 1, _,  _     => by simp
  | n+1, m + 1, _, []    => by simp
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
    (n m : ℕ) → (h : m ≤  n) → (r : List I) → (hm : m ≤ r.length)   →
    (List.take (n + 1) (List.insertIdx m i r)).Perm (i :: List.take n r)
  | 0,  0, h,  _, _    => by simp
  | m + 1,  0, h,  r, _     => by simp
  | n + 1,  m + 1, h,  [], hm    => by
    simp at hm
  | n + 1,  m + 1, h,  a::as, hm    => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons]
    have hp : (i :: a :: List.take n as).Perm (a :: i :: List.take n as) := by
      exact List.Perm.swap a i (List.take n as)
    refine List.Perm.trans ?_ hp.symm
    refine List.Perm.cons a ?_
    exact take_insert_let i n m (Nat.le_of_succ_le_succ h) as (Nat.le_of_succ_le_succ hm)

lemma insertSign_insert_lt_eq_insertSort {I : Type} (q : I → Fin 2) (n m : ℕ)
    (r0 r1 : I) (r : List I) (hn :  m ≤  n) (hm : m ≤ r.length):
    insertSign q (n + 1) r0 (List.insertIdx m r1 r) = insertSign q (n + 1) r0 (r1 :: r) := by
  rw [insertSign, insertSign]
  apply superCommuteCoef_perm_snd
  simp only [List.take_succ_cons]
  refine take_insert_let r1 n m hn r hm

lemma insertSign_insert_lt {I : Type} (q : I → Fin 2) (n m : ℕ)
    (r0 r1 : I) (r : List I) (hn :  m ≤  n) (hm : m ≤ r.length):
    insertSign q (n + 1) r0 (List.insertIdx m r1 r) = superCommuteCoef q [r0] [r1] * insertSign q n r0 r := by
  rw [insertSign_insert_lt_eq_insertSort, insertSign_succ_cons]
  exact hn
  exact hm




def koszulSignCons {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (r0 r1 : I) :
    ℂ :=
  if le1 r0 r1 then 1 else
  if q r0 = 1 ∧ q r1 = 1 then -1 else 1

lemma koszulSignCons_eq_superComuteCoef {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (r0 r1 : I) : koszulSignCons q le1 r0 r1 =
    if le1 r0 r1 then 1 else superCommuteCoef q [r0] [r1]  := by
  simp only [koszulSignCons, Fin.isValue, superCommuteCoef, grade, ite_eq_right_iff, zero_ne_one,
    imp_false]
  congr 1
  by_cases h0 : q r0 = 1
  · by_cases h1 : q r1 = 1
    · simp [h0, h1]
    · have h1 : q r1 = 0 := by omega
      simp [h0, h1]
  · have h0 : q r0 = 0 := by omega
    by_cases h1 : q r1 = 1
    · simp [h0, h1]
    · have h1 : q r1 = 0 := by omega
      simp [h0, h1]

lemma koszulSignInsert_cons {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    [IsTotal I le1] [IsTrans I le1] (r0 r1 : I) (r : List I) :
    koszulSignInsert le1 q r0 (r1 :: r) = koszulSignCons q le1 r0 r1 * koszulSignInsert le1 q r0 r := by
  simp [koszulSignInsert, koszulSignCons]

lemma koszulSignInsert_eq_insertSign {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    [IsTotal I le1] [IsTrans I le1] (r0 : I) (r : List I)  :
    koszulSignInsert le1 q r0 r = insertSign q (orderedInsertPos le1 (List.insertionSort le1 r) r0)
      r0 (List.insertionSort le1 r) := by
  rw [koszulSignInsert_eq_cons, koszulSignInsert_eq_sort, koszulSignInsert_eq_filter,
    koszulSignInsert_eq_grade, insertSign, superCommuteCoef]
  congr
  simp only [List.filter_filter, Bool.and_self]
  rw [List.insertionSort]
  nth_rewrite 1 [List.orderedInsert_eq_take_drop]
  rw [List.filter_append]
  have h1 : List.filter (fun a => decide ¬le1 r0 a) (List.takeWhile (fun b => decide ¬le1 r0 b) (List.insertionSort le1 r))
    =  (List.takeWhile (fun b => decide ¬le1 r0 b) (List.insertionSort le1 r)) := by
    induction r with
    | nil => simp
    | cons r1 r ih =>
      simp only [decide_not, List.insertionSort, List.filter_eq_self, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not]
      intro a ha
      have ha' := List.mem_takeWhile_imp ha
      simp_all
  rw [h1]
  rw [List.filter_cons]
  simp only [decide_not, (IsTotal.to_isRefl le1).refl r0, not_true_eq_false, decide_False,
    Bool.false_eq_true, ↓reduceIte]
  rw [orderedInsertPos_take]
  simp only [decide_not, List.append_right_eq_self, List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, Decidable.not_not]
  intro a ha
  refine List.Sorted.rel_of_mem_take_of_mem_drop
    (k := (orderedInsertPos le1 (List.insertionSort le1 r) r0).1 + 1 )
    (List.sorted_insertionSort le1 (r0 :: r)) ?_ ?_
  · simp only [List.insertionSort, List.orderedInsert_eq_take_drop, decide_not]
    rw [List.take_append_eq_append_take]
    rw [List.take_of_length_le]
    · simp [orderedInsertPos]
    · simp [orderedInsertPos]
  · simp only [List.insertionSort, List.orderedInsert_eq_take_drop, decide_not]
    rw [List.drop_append_eq_append_drop]
    rw [List.drop_of_length_le]
    · simpa [orderedInsertPos] using ha
    · simp [orderedInsertPos]

lemma koszulSignInsert_insertIdx {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (i j : I) [IsTotal I le1] [IsTrans I le1] (r : List I)  (n : ℕ) (hn : n ≤ r.length) :
    koszulSignInsert le1 q j (List.insertIdx  n i r) = koszulSignInsert le1 q j (i :: r) := by
  apply koszulSignInsert_eq_perm
  exact List.perm_insertIdx i r hn

lemma take_insertIdx {I : Type} (i : I) : (r : List I) →  (n : ℕ) → (hn : n ≤ r.length) →
    List.take n (List.insertIdx n i r) = List.take n r
  | [], 0, h => by
    simp
  | [], n + 1, h => by
    simp at h
  | r0 :: r, 0, h => by
    simp
  | r0 :: r, n + 1, h => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.cons.injEq, true_and]
    exact take_insertIdx i r n (Nat.le_of_lt_succ h)


lemma koszulSign_insertIdx {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (i : I) [IsTotal I le1] [IsTrans I le1] : (r : List I) →  (n : ℕ) → (hn : n ≤ r.length) →
    koszulSign le1 q (List.insertIdx n i r) = insertSign q n i r
       * koszulSign le1 q r
       *  insertSign q (insertionSortEquiv le1 (List.insertIdx n i r) ⟨n, by
        rw [List.length_insertIdx _ _ hn]
        omega⟩) i
        (List.insertionSort le1 (List.insertIdx n i r))
  | [], 0, h => by
    simp [koszulSign, insertSign, superCommuteCoef, koszulSignInsert]
  | [], n + 1, h => by
    simp at h
  | r0 :: r, 0, h => by
    simp only [List.insertIdx_zero, List.insertionSort, List.length_cons, Fin.zero_eta]
    rw [koszulSign]
    trans koszulSign le1 q (r0 :: r)  * koszulSignInsert le1 q i (r0 :: r)
    ring
    simp only [insertionSortEquiv, List.length_cons, Nat.succ_eq_add_one, List.insertionSort,
      orderedInsertEquiv, OrderIso.toEquiv_symm, Fin.symm_castOrderIso, HepLean.Fin.equivCons_trans,
      Equiv.trans_apply, HepLean.Fin.equivCons_zero, HepLean.Fin.finExtractOne_apply_eq,
      Fin.isValue, HepLean.Fin.finExtractOne_symm_inl_apply, RelIso.coe_fn_toEquiv,
      Fin.castOrderIso_apply, Fin.cast_mk, Fin.eta]
    conv_rhs =>
      rhs
      rhs
      rw [orderedInsert_eq_insertIdx_orderedInsertPos]
    conv_rhs =>
      rhs
      rw [← insertSign_insert]
      change insertSign q (↑(orderedInsertPos le1 ((List.insertionSort le1 (r0 :: r))) i)) i
        (List.insertionSort le1 (r0 :: r))
      rw [← koszulSignInsert_eq_insertSign q le1]
    rw [insertSign_zero]
    simp
  | r0 :: r, n + 1, h => by
    conv_lhs =>
      rw [List.insertIdx_succ_cons]
      rw [koszulSign]
    rw [koszulSign_insertIdx]
    conv_rhs =>
      rhs
      simp only [List.insertIdx_succ_cons]
      simp only [List.insertionSort, List.length_cons, insertionSortEquiv, Nat.succ_eq_add_one,
        Equiv.trans_apply, HepLean.Fin.equivCons_succ]
      erw [orderedInsertEquiv_fin_succ]
      simp only [Fin.eta, Fin.coe_cast]
      rhs
      rw [orderedInsert_eq_insertIdx_orderedInsertPos]
    conv_rhs =>
      lhs
      rw [insertSign_succ_cons, koszulSign]
    ring_nf
    conv_lhs =>
      lhs
      rw [mul_assoc, mul_comm]
    rw [mul_assoc]
    conv_rhs =>
      rw [mul_assoc, mul_assoc]
    congr 1
    let rs := (List.insertionSort le1 (List.insertIdx n i r))
    have hnsL : n < (List.insertIdx n i r).length := by
      rw [List.length_insertIdx _ _]
      simp only [List.length_cons, add_le_add_iff_right] at h
      omega
      exact Nat.le_of_lt_succ h
    let ni : Fin rs.length := (insertionSortEquiv le1 (List.insertIdx n i r))
      ⟨n,  hnsL⟩
    let nro : Fin (rs.length + 1) := ⟨↑(orderedInsertPos le1 rs r0), orderedInsertPos_lt_length le1 rs r0⟩
    rw [koszulSignInsert_insertIdx, koszulSignInsert_cons]
    trans koszulSignInsert le1 q r0 r * (koszulSignCons q le1 r0 i  *insertSign q ni i rs)
    · simp only [rs, ni]
      ring
    trans koszulSignInsert le1 q r0 r  * (superCommuteCoef q [i] [r0] *
          insertSign q (nro.succAbove ni) i (List.insertIdx nro r0 rs))
    swap
    · simp only [rs, nro, ni]
      ring
    congr 1
    simp only [Fin.succAbove]
    have hns : rs.get ni = i := by
      simp only [Fin.eta, rs]
      rw [← insertionSortEquiv_get]
      simp only [Function.comp_apply, Equiv.symm_apply_apply, List.get_eq_getElem, ni]
      simp_all only [List.length_cons, add_le_add_iff_right, List.getElem_insertIdx_self]
    have hms : (List.orderedInsert le1 r0 rs).get ⟨nro, by simp⟩ = r0 := by
      simp [nro]
    have hc1 : ni.castSucc < nro → ¬ le1 r0 i := by
      intro hninro
      rw [← hns]
      exact lt_orderedInsertPos_rel le1 r0 rs ni hninro
    have hc2 : ¬ ni.castSucc < nro → le1 r0 i := by
      intro hninro
      rw [← hns]
      refine gt_orderedInsertPos_rel le1 r0 rs ?_ ni hninro
      exact List.sorted_insertionSort le1 (List.insertIdx n i r)
    by_cases hn : ni.castSucc < nro
    · simp only [hn, ↓reduceIte, Fin.coe_castSucc]
      rw [insertSign_insert_gt]
      swap
      · exact hn
      congr 1
      rw [koszulSignCons_eq_superComuteCoef]
      simp only [hc1 hn, ↓reduceIte]
      rw [superCommuteCoef_comm]
    · simp only [hn, ↓reduceIte, Fin.val_succ]
      rw [insertSign_insert_lt]
      rw [← mul_assoc]
      congr 1
      rw [superCommuteCoef_mul_self]
      rw [koszulSignCons]
      simp only [hc2 hn, ↓reduceIte]
      exact Nat.le_of_not_lt hn
      exact Nat.le_of_lt_succ (orderedInsertPos_lt_length le1 rs r0)
    · exact Nat.le_of_lt_succ h
    · exact Nat.le_of_lt_succ h

lemma insertIdx_eraseIdx {I : Type} :
    (n : ℕ) → (r : List I) → (hn : n < r.length) →
    List.insertIdx n (r.get ⟨n, hn⟩) (r.eraseIdx n) = r
  | n, [], hn => by
    simp at hn
  | 0, r0 :: r, hn => by
    simp
  | n + 1, r0 :: r, hn => by
    simp only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ,
      List.eraseIdx_cons_succ, List.insertIdx_succ_cons, List.cons.injEq, true_and]
    exact insertIdx_eraseIdx n r _

lemma superCommuteCoefLE_eq_get {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] [IsTotal I le1] [IsTrans I le1] (i : I) (n : Fin r.length) (heq : q i = q (r.get n)) :
    superCommuteCoefLE q le1 r i n = superCommuteCoef q [r.get n] (r.take n) := by
  rw [superCommuteCoefLE_eq_q]
  let r' := r.eraseIdx ↑n
  have hr : List.insertIdx n (r.get n) (r.eraseIdx n) = r := by
    exact insertIdx_eraseIdx n.1 r n.prop
  conv_lhs =>
    lhs
    lhs
    rw [← hr]
    rw [koszulSign_insertIdx q le1 (r.get n) ((r.eraseIdx ↑n)) n (by
      rw [List.length_eraseIdx]
      simp only [Fin.is_lt, ↓reduceIte]
      omega)]
    rhs
    rhs
    rw [hr]
  conv_lhs =>
    lhs
    lhs
    rhs
    enter [2, 1, 1]
    rw [insertionSortEquiv_congr _ _ hr]
  simp only [List.get_eq_getElem, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
    Fin.cast_mk, Fin.eta, Fin.coe_cast]
  conv_lhs =>
    lhs
    rw [mul_assoc]
    rhs
    rw [insertSign]
    rw [superCommuteCoef_mul_self]
  simp only [mul_one]
  rw [mul_assoc]
  rw [koszulSign_mul_self]
  simp only [mul_one]
  rw [insertSign_eraseIdx]
  rfl
  exact heq

end Wick
