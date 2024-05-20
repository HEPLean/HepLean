/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.PureU1.Basic
import HepLean.AnomalyCancellation.PureU1.Permutations
import HepLean.AnomalyCancellation.PureU1.VectorLike
import HepLean.AnomalyCancellation.PureU1.ConstAbs
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic
/-!
# Line in plane condition

We say a `LinSol` satisfies the `line in plane` condition if for all distinct `i1`, `i2`, `i3` in
`Fin n`, we have
`S i1 = S i2`  or  `S i1 = - S i2` or  `2 S i3 + S i1 + S i2 = 0`.

We look at various consequences of this.
The main reference for this material is

- https://arxiv.org/pdf/1912.04804.pdf

We will show that `n ≥ 4` the `line in plane` condition on solutions implies the
`constAbs` condition.

-/


namespace PureU1

open BigOperators

variable {n : ℕ}

/-- The proposition on three rationals to satisfy the `linInPlane` condition. -/
def lineInPlaneProp : ℚ × ℚ × ℚ → Prop := fun s =>
  s.1 = s.2.1 ∨ s.1 = - s.2.1 ∨ 2 * s.2.2 + s.1 + s.2.1 = 0

/-- The proposition on a `LinSol` to satisfy the `linInPlane` condition. -/
def lineInPlaneCond (S : (PureU1 (n)).LinSols) : Prop :=
  ∀ (i1 i2 i3 : Fin (n)) (_ : i1 ≠ i2) (_ : i2 ≠ i3) (_ : i1 ≠ i3),
  lineInPlaneProp (S.val i1, (S.val i2, S.val i3))

lemma lineInPlaneCond_perm {S : (PureU1 (n)).LinSols} (hS : lineInPlaneCond S)
    (M : (FamilyPermutations n).group) :
    lineInPlaneCond ((FamilyPermutations n).linSolRep M S) := by
  intro i1 i2 i3 h1 h2 h3
  rw [FamilyPermutations_anomalyFreeLinear_apply, FamilyPermutations_anomalyFreeLinear_apply,
    FamilyPermutations_anomalyFreeLinear_apply]
  refine hS (M.invFun i1) (M.invFun i2) (M.invFun i3) ?_ ?_ ?_
  all_goals simp_all only [ne_eq, Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq,
    not_false_eq_true]


lemma lineInPlaneCond_eq_last' {S : (PureU1 (n.succ.succ)).LinSols} (hS : lineInPlaneCond S)
    (h : ¬ (S.val ((Fin.last n).castSucc))^2 = (S.val ((Fin.last n).succ))^2 ) :
    (2 - n) * S.val (Fin.last (n + 1)) =
    - (2 - n)* S.val (Fin.castSucc (Fin.last n)) := by
  erw [sq_eq_sq_iff_eq_or_eq_neg] at h
  rw [lineInPlaneCond] at hS
  simp only [lineInPlaneProp] at hS
  simp [not_or] at h
  have h1 (i : Fin n) : S.val i.castSucc.castSucc =
      - (S.val ((Fin.last n).castSucc) +  (S.val ((Fin.last n).succ))) / 2 := by
    have h1S := hS (Fin.last n).castSucc ((Fin.last n).succ) i.castSucc.castSucc
      (by simp; rw [Fin.ext_iff]; simp)
      (by simp; rw [Fin.ext_iff]; simp; omega)
      (by simp; rw [Fin.ext_iff]; simp; omega)
    simp_all
    field_simp
    linear_combination h1S
  have h2 := pureU1_last S
  rw [Fin.sum_univ_castSucc] at h2
  simp [h1] at h2
  field_simp at h2
  linear_combination h2

lemma lineInPlaneCond_eq_last {S : (PureU1 (n.succ.succ.succ.succ.succ)).LinSols}
    (hS : lineInPlaneCond S) : constAbsProp ((S.val ((Fin.last n.succ.succ.succ).castSucc)),
    (S.val ((Fin.last n.succ.succ.succ).succ))) := by
  rw [constAbsProp]
  by_contra hn
  have h := lineInPlaneCond_eq_last' hS hn
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hn
  simp [or_not] at hn
  have hx : ((2 : ℚ) - ↑(n + 3))  ≠ 0 := by
    rw [Nat.cast_add]
    simp only [Nat.cast_ofNat, ne_eq]
    apply Not.intro
    intro a
    linarith
  have ht : S.val ((Fin.last n.succ.succ.succ).succ)  =
   - S.val  ((Fin.last n.succ.succ.succ).castSucc) := by
    rw [← mul_right_inj' hx]
    simp [Nat.succ_eq_add_one]
    simp at h
    rw [h]
    ring
  simp_all

lemma linesInPlane_eq_sq {S : (PureU1 (n.succ.succ.succ.succ.succ)).LinSols}
    (hS : lineInPlaneCond S) : ∀ (i j : Fin n.succ.succ.succ.succ.succ) (_ : i ≠ j),
    constAbsProp (S.val i, S.val j) := by
  have hneq : ((Fin.last n.succ.succ.succ).castSucc) ≠ ((Fin.last n.succ.succ.succ).succ) := by
    simp [Fin.ext_iff]
  refine Prop_two constAbsProp hneq ?_
  intro M
  exact lineInPlaneCond_eq_last (lineInPlaneCond_perm hS M)

theorem linesInPlane_constAbs {S : (PureU1 (n.succ.succ.succ.succ.succ)).LinSols}
    (hS : lineInPlaneCond S) : constAbs S.val := by
  intro i j
  by_cases hij : i ≠ j
  exact linesInPlane_eq_sq hS i j hij
  simp at hij
  rw [hij]

lemma linesInPlane_four (S : (PureU1 4).Sols) (hS : lineInPlaneCond S.1.1) :
    constAbsProp (S.val (0 : Fin 4), S.val (1 : Fin 4))  := by
  simp [constAbsProp]
  by_contra hn
  have hLin := pureU1_linear S.1.1
  have hcube := pureU1_cube S
  simp at hLin hcube
  rw [Fin.sum_univ_four] at hLin hcube
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hn
  simp [not_or] at hn
  have l012 := hS 0 1 2 (by simp) (by simp) (by simp)
  have l013 := hS 0 1 3 (by simp) (by simp) (by simp)
  have l023 := hS 0 2 3 (by simp) (by simp) (by simp)
  simp_all [lineInPlaneProp]
  have h1 : S.val (2 : Fin 4) = S.val (3 : Fin 4)  := by
    linear_combination l012 / 2 + -1 * l013 / 2
  by_cases h2 : S.val (0 : Fin 4) = S.val (2 : Fin 4)
  simp_all
  have h3 : S.val (1 : Fin 4) = - 3 * S.val (2 : Fin 4) := by
    linear_combination l012 + 3 * h1
  rw [← h1, h3] at hcube
  have h4 : S.val (2 : Fin 4) ^ 3 = 0 := by
    linear_combination -1 * hcube / 24
  simp at h4
  simp_all
  by_cases h3 : S.val (0 : Fin 4) = - S.val (2 : Fin 4)
  simp_all
  have h4 : S.val (1 : Fin 4) = - S.val (2 : Fin 4) := by
    linear_combination l012 + h1
  simp_all
  simp_all
  have h4 : S.val (0 : Fin 4) = - 3 * S.val (3 : Fin 4) := by
    linear_combination l023
  have h5 : S.val (1 : Fin 4) = S.val (3 : Fin 4) := by
    linear_combination l013 - 1 * h4
  rw [h4, h5] at hcube
  have h6 : S.val (3 : Fin 4) ^ 3 = 0 := by
    linear_combination -1 * hcube / 24
  simp at h6
  simp_all


lemma linesInPlane_eq_sq_four {S : (PureU1 4).Sols}
    (hS : lineInPlaneCond S.1.1) : ∀ (i j : Fin 4) (_ : i ≠ j),
    constAbsProp (S.val i, S.val j) := by
  refine Prop_two constAbsProp (by simp : (0 : Fin 4) ≠ 1) ?_
  intro M
  let S' := (FamilyPermutations 4).solAction.toFun S M
  have hS' :  lineInPlaneCond S'.1.1 :=
    (lineInPlaneCond_perm hS M)
  exact linesInPlane_four S' hS'


lemma linesInPlane_constAbs_four (S : (PureU1 4).Sols)
    (hS : lineInPlaneCond S.1.1) : constAbs S.val := by
  intro i j
  by_cases hij : i ≠ j
  exact linesInPlane_eq_sq_four hS i j hij
  simp at hij
  rw [hij]

theorem linesInPlane_constAbs_AF (S : (PureU1 (n.succ.succ.succ.succ)).Sols)
    (hS : lineInPlaneCond S.1.1) : constAbs S.val := by
  induction n
  exact linesInPlane_constAbs_four S hS
  exact linesInPlane_constAbs hS


end PureU1
