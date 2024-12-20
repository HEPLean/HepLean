/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Signs.KoszulSign
/-!

# Static wick coefficent

-/

namespace Wick

open HepLean.List

open FieldStatistic

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le :𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- The sign that appears in the static version of Wicks theorem.
  This is actually equal to `superCommuteCoef q [r.get n] (r.take n)`, something
  which will be proved in a lemma. -/
def staticWickCoef (r : List 𝓕) (i : 𝓕) (n : Fin r.length) : ℂ :=
  koszulSign q le r *
  superCommuteCoef q [i] (List.take (↑((HepLean.List.insertionSortEquiv le r) n))
    (List.insertionSort le r)) *
  koszulSign q le (r.eraseIdx ↑n)

lemma staticWickCoef_eq_q (r : List 𝓕) (i : 𝓕) (n : Fin r.length)
    (hq : q i = q (r.get n)) :
    staticWickCoef q le r i n =
    koszulSign q le r *
    superCommuteCoef q [r.get n] (List.take (↑(insertionSortEquiv le r n))
      (List.insertionSort le r)) *
    koszulSign q le (r.eraseIdx ↑n) := by
  simp [staticWickCoef, superCommuteCoef, ofList, hq]

lemma insertIdx_eraseIdx {I : Type} : (n : ℕ) → (r : List I) → (hn : n < r.length) →
    List.insertIdx n (r.get ⟨n, hn⟩) (r.eraseIdx n) = r
  | n, [], hn => by
    simp at hn
  | 0, r0 :: r, hn => by
    simp
  | n + 1, r0 :: r, hn => by
    simp only [List.length_cons, List.get_eq_getElem, List.getElem_cons_succ,
      List.eraseIdx_cons_succ, List.insertIdx_succ_cons, List.cons.injEq, true_and]
    exact insertIdx_eraseIdx n r _

lemma staticWickCoef_eq_get [IsTotal 𝓕 le] [IsTrans 𝓕 le] (r : List 𝓕) (i : 𝓕) (n : Fin r.length)
    (heq : q i = q (r.get n)) :
    staticWickCoef q le r i n = superCommuteCoef q [r.get n] (r.take n) := by
  rw [staticWickCoef_eq_q]
  let r' := r.eraseIdx ↑n
  have hr : List.insertIdx n (r.get n) (r.eraseIdx n) = r := by
    exact insertIdx_eraseIdx n.1 r n.prop
  conv_lhs =>
    lhs
    lhs
    rw [← hr]
    rw [koszulSign_insertIdx q le (r.get n) ((r.eraseIdx ↑n)) n (by
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
