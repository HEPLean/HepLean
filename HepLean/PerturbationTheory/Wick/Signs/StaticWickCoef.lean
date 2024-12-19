/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Complex.Basic
import HepLean.PerturbationTheory.Wick.Signs.KoszulSign
/-!

# Koszul sign insert

-/

namespace Wick

open HepLean.List

/-- The sign that appears in the static version of Wicks theorem.
  This is actually equal to `superCommuteCoef q [r.get n] (r.take n)`, something
  which will be proved in a lemma. -/
def staticWickCoef {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (n : Fin r.length) : ℂ :=
  koszulSign le1 q r *
  superCommuteCoef q [i] (List.take (↑((HepLean.List.insertionSortEquiv le1 r) n))
    (List.insertionSort le1 r)) *
  koszulSign le1 q (r.eraseIdx ↑n)

lemma staticWickCoef_eq_q {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] (i : I) (n : Fin r.length)
    (hq : q i = q (r.get n)) :
    staticWickCoef q le1 r i n =
    koszulSign le1 q r *
    superCommuteCoef q [r.get n] (List.take (↑(insertionSortEquiv le1 r n))
      (List.insertionSort le1 r)) *
    koszulSign le1 q (r.eraseIdx ↑n) := by
  simp [staticWickCoef, superCommuteCoef, grade, hq]

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

lemma staticWickCoef_eq_get {I : Type} (q : I → Fin 2) (le1 :I → I → Prop) (r : List I)
    [DecidableRel le1] [IsTotal I le1] [IsTrans I le1] (i : I) (n : Fin r.length)
    (heq : q i = q (r.get n)) :
    staticWickCoef q le1 r i n = superCommuteCoef q [r.get n] (r.take n) := by
  rw [staticWickCoef_eq_q]
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
