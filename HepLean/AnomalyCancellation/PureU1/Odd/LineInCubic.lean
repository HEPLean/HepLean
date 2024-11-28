/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.PureU1.Basic
import HepLean.AnomalyCancellation.PureU1.Permutations
import HepLean.AnomalyCancellation.PureU1.VectorLike
import HepLean.AnomalyCancellation.PureU1.ConstAbs
import HepLean.AnomalyCancellation.PureU1.LineInPlaneCond
import HepLean.AnomalyCancellation.PureU1.Odd.BasisLinear
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic
/-!

# Line In Cubic Odd case

We say that a linear solution satisfies the `lineInCubic` property
if the line through that point and through the two different planes formed by the basis of
`LinSols` lies in the cubic.

We show that for a solution all its permutations satisfy this property,
then the charge must be zero.

The main reference for this file is:

- https://arxiv.org/pdf/1912.04804.pdf
-/
namespace PureU1
namespace Odd

open BigOperators

variable {n : ℕ}
open VectorLikeOddPlane

/-- A property on `LinSols`, satisfied if every point on the line between the two planes
in the basis through that point is in the cubic. -/
def LineInCubic (S : (PureU1 (2 * n + 1)).LinSols) : Prop :=
  ∀ (g f : Fin n → ℚ) (_ : S.val = Pa g f) (a b : ℚ),
  accCube (2 * n + 1) (a • P g + b • P! f) = 0

/-- The condition that a linear solution sits on a line between the two planes
  within the cubic expands into a on `accCubeTriLinSymm` applied to the points
  within the planes. -/
lemma lineInCubic_expand {S : (PureU1 (2 * n + 1)).LinSols} (h : LineInCubic S) :
    ∀ (g : Fin n → ℚ) (f : Fin n → ℚ) (_ : S.val = P g + P! f) (a b : ℚ),
    3 * a * b * (a * accCubeTriLinSymm (P g) (P g) (P! f)
    + b * accCubeTriLinSymm (P! f) (P! f) (P g)) = 0 := by
  intro g f hS a b
  have h1 := h g f hS a b
  change accCubeTriLinSymm.toCubic (a • P g + b • P! f) = 0 at h1
  simp only [TriLinearSymm.toCubic_add] at h1
  simp only [HomogeneousCubic.map_smul,
    accCubeTriLinSymm.map_smul₁, accCubeTriLinSymm.map_smul₂, accCubeTriLinSymm.map_smul₃] at h1
  erw [P_accCube, P!_accCube] at h1
  rw [← h1]
  ring

lemma line_in_cubic_P_P_P! {S : (PureU1 (2 * n + 1)).LinSols} (h : LineInCubic S) :
    ∀ (g : Fin n → ℚ) (f : Fin n → ℚ) (_ : S.val = P g + P! f),
    accCubeTriLinSymm (P g) (P g) (P! f) = 0 := by
  intro g f hS
  linear_combination 2 / 3 * (lineInCubic_expand h g f hS 1 1) -
      (lineInCubic_expand h g f hS 1 2) / 6

/-- A `LinSol` satisfies `lineInCubicPerm` if all its permutations satisfy `lineInCubic`. -/
def LineInCubicPerm (S : (PureU1 (2 * n + 1)).LinSols) : Prop :=
  ∀ (M : (FamilyPermutations (2 * n + 1)).group),
    LineInCubic ((FamilyPermutations (2 * n + 1)).linSolRep M S)

/-- If `lineInCubicPerm S`, then `lineInCubic S`. -/
lemma lineInCubicPerm_self {S : (PureU1 (2 * n + 1)).LinSols} (hS : LineInCubicPerm S) :
    LineInCubic S := hS 1

/-- If `lineInCubicPerm S`, then `lineInCubicPerm (M S)` for all permutations `M`. -/
lemma lineInCubicPerm_permute {S : (PureU1 (2 * n + 1)).LinSols}
    (hS : LineInCubicPerm S) (M' : (FamilyPermutations (2 * n + 1)).group) :
    LineInCubicPerm ((FamilyPermutations (2 * n + 1)).linSolRep M' S) :=
  fun M => hS (M * M')

lemma lineInCubicPerm_swap {S : (PureU1 (2 * n.succ + 1)).LinSols}
    (LIC : LineInCubicPerm S) :
    ∀ (j : Fin n.succ) (g f : Fin n.succ → ℚ) (_ : S.val = Pa g f),
      (S.val (δ!₂ j) - S.val (δ!₁ j))
      * accCubeTriLinSymm (P g) (P g) (basis!AsCharges j) = 0 := by
  intro j g f h
  let S' := (FamilyPermutations (2 * n.succ + 1)).linSolRep
    (pairSwap (δ!₁ j) (δ!₂ j)) S
  have hSS' : ((FamilyPermutations (2 * n.succ + 1)).linSolRep
    (pairSwap (δ!₁ j) (δ!₂ j))) S = S' := rfl
  obtain ⟨g', f', hall⟩ := span_basis_swap! j hSS' g f h
  have h1 := line_in_cubic_P_P_P! (lineInCubicPerm_self LIC) g f h
  have h2 := line_in_cubic_P_P_P!
    (lineInCubicPerm_self (lineInCubicPerm_permute LIC (pairSwap (δ!₁ j) (δ!₂ j)))) g' f' hall.1
  rw [hall.2.1, hall.2.2] at h2
  rw [accCubeTriLinSymm.map_add₃, h1, accCubeTriLinSymm.map_smul₃] at h2
  simpa using h2

lemma P_P_P!_accCube' {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (f g : Fin n.succ.succ → ℚ) (hS : S.val = Pa f g) :
    accCubeTriLinSymm (P f) (P f) (basis!AsCharges 0) =
    (S.val (δ!₁ 0) + S.val (δ!₂ 0)) * (2 * S.val δ!₃ + S.val (δ!₁ 0) + S.val (δ!₂ 0)) := by
  rw [P_P_P!_accCube f 0]
  rw [← Pa_δa₁ f g]
  rw [← hS]
  have ht : δ!₁ (0 : Fin n.succ.succ) = δ₁ 1 := rfl
  nth_rewrite 1 [ht]
  rw [P_δ₁]
  have h1 := Pa_δa₁ f g
  have h4 := Pa_δa₄ f g 0
  have h2 := Pa_δa₂ f g 0
  rw [← hS] at h1 h2 h4
  simp only [Nat.succ_eq_add_one, Fin.succ_zero_eq_one, Fin.castSucc_zero] at h2
  have h5 : f 1 = S.val (δa₂ 0) + S.val δa₁ + S.val (δa₄ 0) := by
    linear_combination -(1 * h1) - 1 * h4 - 1 * h2
  rw [h5, δa₄_δ!₂, show (δa₂ (0 : Fin n.succ)) = δ!₁ 0 from rfl, δa₁_δ!₃]
  ring

lemma lineInCubicPerm_last_cond {S : (PureU1 (2 * n.succ.succ+1)).LinSols}
    (LIC : LineInCubicPerm S) :
    LineInPlaneProp ((S.val (δ!₂ 0)), ((S.val (δ!₁ 0)), (S.val δ!₃))) := by
  obtain ⟨g, f, hfg⟩ := span_basis S
  have h1 := lineInCubicPerm_swap LIC 0 g f hfg
  rw [P_P_P!_accCube' g f hfg] at h1
  simp only [Nat.succ_eq_add_one, mul_eq_zero] at h1
  cases h1 <;> rename_i h1
  · apply Or.inl
    linear_combination h1
  · cases h1 <;> rename_i h1
    · refine Or.inr (Or.inl ?_)
      linear_combination h1
    · refine Or.inr (Or.inr ?_)
      linear_combination h1

lemma lineInCubicPerm_last_perm {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (LIC : LineInCubicPerm S) : LineInPlaneCond S := by
  refine @Prop_three (2 * n.succ.succ + 1) LineInPlaneProp S (δ!₂ 0) (δ!₁ 0)
    δ!₃ ?_ ?_ ?_ ?_
  · exact ne_of_beq_false rfl
  · exact ne_of_beq_false rfl
  · exact ne_of_beq_false rfl
  · exact fun M => lineInCubicPerm_last_cond (lineInCubicPerm_permute LIC M)

lemma lineInCubicPerm_constAbs {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (LIC : LineInCubicPerm S) : ConstAbs S.val :=
  linesInPlane_constAbs (lineInCubicPerm_last_perm LIC)

theorem lineInCubicPerm_zero {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (LIC : LineInCubicPerm S) : S = 0 :=
  ConstAbs.boundary_value_odd S (lineInCubicPerm_constAbs LIC)

end Odd
end PureU1
