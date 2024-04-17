/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.MSSMNu.Basic
import HepLean.AnomalyCancellation.MSSMNu.LineY3B3
import HepLean.AnomalyCancellation.MSSMNu.PlaneY3B3Orthog
import Mathlib.Tactic.Polyrith
/-!
# Parameterization of solutions to the MSSM anomaly cancellation equations

This file uses planes through $Y_3$ and $B_3$ to form solutions to the anomaly cancellation
conditions.

Split into four cases:
- The generic case.
- `case₁`: The case when the quadratic and cubic lines agree (if they exist uniquely).
- `case₂`: The case where the plane lies entirely within the quadratic.
- `case₃`: The case where the plane lies entirely within the cubic and quadratic.

# References

The main reference for the material in this file is:

- https://arxiv.org/pdf/2107.07926.pdf

-/

universe v u

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

/-- Given a `R ∈ LinSols` perpendicular to $Y_3$, and $B_3$, a solution to the quadratic. -/
def genericQuad (R : MSSMACC.AnomalyFreePerp) : MSSMACC.QuadSols :=
  lineQuad R
    (3 * cubeTriLin (R.val, R.val, Y₃.val))
    (3 * cubeTriLin (R.val, R.val, B₃.val))
    (cubeTriLin (R.val, R.val, R.val))

lemma genericQuad_cube (R : MSSMACC.AnomalyFreePerp) :
    accCube (genericQuad R).val = 0 := by
  rw [genericQuad]
  rw [lineQuad_val]
  rw [planeY₃B₃_cubic]
  ring

/-- Given a `R ∈ LinSols` perpendicular to $Y_3$, and $B_3$, a element of `Sols`. -/
def generic (R : MSSMACC.AnomalyFreePerp) : MSSMACC.Sols :=
  AnomalyFreeMk'' (genericQuad R) (genericQuad_cube R)

lemma generic_eq_planeY₃B₃_on_α (R : MSSMACC.AnomalyFreePerp) :
    (generic R).1.1 = planeY₃B₃ R (α₁ R) (α₂ R) (α₃ R) := by
  change (planeY₃B₃ _ _ _ _) = _
  apply planeY₃B₃_eq
  rw [α₁, α₂, α₃]
  ring_nf
  simp

/-- Case₁ is when the quadratic and cubic lines in the plane agree, which occurs when
  `α₁ R = 0`, `α₂ R = 0` and `α₃ R = 0` (if they exist uniquely).  -/
def case₁prop (R : MSSMACC.AnomalyFreePerp) : Prop :=
    α₁ R = 0 ∧ α₂ R = 0 ∧ α₃ R = 0

/-- Case₂ is defined when the plane lies entirely within the quadratic. -/
def case₂prop (R : MSSMACC.AnomalyFreePerp) : Prop :=
    quadBiLin (R.val, R.val) = 0 ∧ quadBiLin (Y₃.val, R.val) = 0 ∧ quadBiLin (B₃.val, R.val) = 0

/-- Case₃ is defined when the plane lies entirely within the quadratic and cubic. -/
def case₃prop (R : MSSMACC.AnomalyFreePerp) : Prop :=
    quadBiLin (R.val, R.val) = 0 ∧ quadBiLin (Y₃.val, R.val) = 0 ∧ quadBiLin (B₃.val, R.val) = 0 ∧
    cubeTriLin (R.val, R.val, R.val) = 0 ∧ cubeTriLin (R.val, R.val, B₃.val) = 0 ∧
    cubeTriLin (R.val, R.val, Y₃.val) = 0

instance (R : MSSMACC.AnomalyFreePerp) : Decidable (case₁prop R) := by
  apply And.decidable

instance (R : MSSMACC.AnomalyFreePerp) : Decidable (case₂prop R) := by
  apply And.decidable

instance (R : MSSMACC.AnomalyFreePerp) : Decidable (case₃prop R) := by
  apply And.decidable

section proj

/-- On elements of `Sols`, `generic (proj _)` is equivalent to multiplying
by `genericProjCoeff`.  -/
def genericProjCoeff (T : MSSMACC.Sols) : ℚ :=
    dot (Y₃.val, B₃.val) * α₃ (proj T.1.1)

lemma generic_proj (T : MSSMACC.Sols) :
    generic (proj T.1.1) = (genericProjCoeff T) • T := by
  apply ACCSystem.Sols.ext
  erw [generic_eq_planeY₃B₃_on_α]
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [α₁_proj, α₂_proj]
  simp
  rfl

lemma genericProjCoeff_ne_zero (T : MSSMACC.Sols) (hT : genericProjCoeff T ≠ 0 ) :
    (genericProjCoeff T)⁻¹ • generic (proj T.1.1) = T := by
  rw [generic_proj, ← MulAction.mul_smul, mul_comm, mul_inv_cancel hT]
  simp

lemma genericProjCoeff_zero_α₃ (T : MSSMACC.Sols) (hT : genericProjCoeff T = 0) :
    α₃ (proj T.1.1) = 0 := by
  rw [genericProjCoeff, mul_eq_zero] at hT
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at hT
  simp at hT
  exact hT

lemma genericProjCoeff_zero_α₂ (T : MSSMACC.Sols) (hT : genericProjCoeff T = 0) :
    α₂ (proj T.1.1) = 0 := by
  rw [α₂_proj, genericProjCoeff_zero_α₃ T hT]
  simp

lemma genericProjCoeff_zero_α₁ (T : MSSMACC.Sols) (hT : genericProjCoeff T = 0) :
    α₁ (proj T.1.1) = 0 := by
  rw [α₁_proj, genericProjCoeff_zero_α₃ T hT]
  simp

lemma genericProjCoeff_zero (T : MSSMACC.Sols) :
    genericProjCoeff T = 0 ↔ case₁prop (proj T.1.1) := by
  apply Iff.intro
  intro hT
  rw [case₁prop]
  rw [genericProjCoeff_zero_α₁ T hT, genericProjCoeff_zero_α₂ T hT, genericProjCoeff_zero_α₃ T hT]
  simp only [and_self]
  intro h
  rw [case₁prop] at h
  rw [genericProjCoeff]
  rw [h.2.2]
  simp

lemma genericProjCoeff_neq_zero_case₁ (T : MSSMACC.Sols) (hT : genericProjCoeff T ≠ 0) :
    ¬ case₁prop (proj T.1.1) :=
  (genericProjCoeff_zero T).mpr.mt hT

lemma genericProjCoeff_neq_zero_case₂ (T : MSSMACC.Sols) (hT : genericProjCoeff T ≠ 0) :
    ¬ case₂prop (proj T.1.1) := by
  by_contra hn
  rw [case₂prop] at hn
  rw [genericProjCoeff, α₃] at hT
  simp_all

lemma genericProjCoeff_neq_zero_case₃ (T : MSSMACC.Sols) (hT : genericProjCoeff T ≠ 0) :
    ¬ case₃prop (proj T.1.1) := by
  by_contra hn
  rw [case₃prop] at hn
  rw [genericProjCoeff, α₃] at hT
  simp_all

end proj

/-- The case when the quadratic and cubic lines agree (if they exist uniquely). -/
def case₁ (R : MSSMACC.AnomalyFreePerp) (c₁ c₂ c₃ : ℚ)
    (h : case₁prop R) : MSSMACC.Sols :=
  AnomalyFreeMk'' (lineQuad R c₁ c₂ c₃)
    (by
      rw [lineQuad_cube]
      rw [h.1, h.2.1, h.2.2]
      simp)

lemma case₁_smul (R : MSSMACC.AnomalyFreePerp) (c₁ c₂ c₃ d : ℚ)
    (h : case₁prop R) : case₁ R (d * c₁) (d * c₂) (d * c₃) h = d • case₁ R c₁ c₂ c₃ h := by
  apply ACCSystem.Sols.ext
  change (lineQuad _ _ _ _).val = _
  rw [lineQuad_smul]
  rfl

section proj

/-- The coefficent which multiplies a solution on passing through `case₁`. -/
def case₁ProjCoeff (T : MSSMACC.Sols) : ℚ :=
    2 * (quadBiLin (Y₃.val, (proj T.1.1).val) ^ 2  +
    quadBiLin (B₃.val, (proj T.1.1).val) ^ 2)

/-- The first parameter in case₁ needed to form an inverse on Proj. -/
def case₁ProjC₁ (T : MSSMACC.Sols) : ℚ := (quadBiLin (B₃.val, T.val))

/-- The second parameter in case₁ needed to form an inverse on Proj. -/
def case₁ProjC₂ (T : MSSMACC.Sols) : ℚ := (- quadBiLin (Y₃.val, T.val))

/-- The third parameter in case₁ needed to form an inverse on Proj. -/
def case₁ProjC₃ (T : MSSMACC.Sols) : ℚ :=
  - quadBiLin (B₃.val, T.val) * ( dot (Y₃.val, T.val)- dot (B₃.val, T.val) )
  - quadBiLin (Y₃.val, T.val) * ( dot (Y₃.val, T.val) - 2 * dot (B₃.val, T.val) )

lemma case₁_proj (T : MSSMACC.Sols) (h1 : genericProjCoeff T = 0) :
    case₁ (proj T.1.1)
       (case₁ProjC₁ T)
       (case₁ProjC₂ T)
       (case₁ProjC₃ T)
       ((genericProjCoeff_zero T).mp h1)
       = (case₁ProjCoeff T) • T := by
  apply ACCSystem.Sols.ext
  change (lineQuad _ _ _ _).val = _
  rw [lineQuad_val]
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [case₁ProjCoeff, case₁ProjC₁, case₁ProjC₂, case₁ProjC₃, quad_proj, quad_Y₃_proj, quad_B₃_proj]
  ring_nf
  simp
  rfl

lemma case₁ProjCoeff_ne_zero (T : MSSMACC.Sols) (h1 : genericProjCoeff T = 0)
    (hT : case₁ProjCoeff T ≠ 0 ) :
    (case₁ProjCoeff T)⁻¹ • case₁ (proj T.1.1)
       (case₁ProjC₁ T)
       (case₁ProjC₂ T)
       (case₁ProjC₃ T)
       ((genericProjCoeff_zero T).mp h1) = T := by
  rw [case₁_proj T h1, ← MulAction.mul_smul, mul_comm, mul_inv_cancel hT]
  simp

lemma case₁ProjCoeff_zero_Y₃_B₃ (T : MSSMACC.Sols) (h1 : case₁ProjCoeff T = 0) :
    quadBiLin (Y₃.val, (proj T.1.1).val) = 0 ∧
    quadBiLin (B₃.val, (proj T.1.1).val) = 0 := by
  rw [case₁ProjCoeff, mul_eq_zero] at h1
  simp only [OfNat.ofNat_ne_zero,  Fin.isValue, Fin.reduceFinMk, false_or] at h1
  have h : quadBiLin (Y₃.val, (proj T.1.1).val) ^ 2 = 0 ∧
     quadBiLin (B₃.val, (proj T.1.1).val) ^ 2  = 0 :=
    (add_eq_zero_iff' (sq_nonneg _) (sq_nonneg _)).mp h1
  simp only [ Fin.isValue, Fin.reduceFinMk, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff] at h
  exact h

lemma case₁ProjCoeff_zero_Y₃ (T : MSSMACC.Sols) (h1 : case₁ProjCoeff T = 0) :
    quadBiLin (Y₃.val, (proj T.1.1).val) = 0 :=
  (case₁ProjCoeff_zero_Y₃_B₃ T h1).left

lemma case₁ProjCoeff_zero_B₃ (T : MSSMACC.Sols) (h1 : case₁ProjCoeff T = 0) :
    quadBiLin (B₃.val, (proj T.1.1).val) = 0 :=
  (case₁ProjCoeff_zero_Y₃_B₃ T h1).right

lemma case₁ProjCoeff_zero_T (T : MSSMACC.Sols) (h1 : case₁ProjCoeff T = 0) :
    quadBiLin (T.val, (proj T.1.1).val) = 0 := by
  have hY3 : quadBiLin (T.val, Y₃.val) = 0 := by
    have h11 := case₁ProjCoeff_zero_Y₃ T h1
    rw [quad_Y₃_proj] at h11
    rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h11
    simp only [ Fin.isValue, Fin.reduceFinMk, mul_eq_zero, OfNat.ofNat_ne_zero,
      false_or] at h11
    erw [quadBiLin.swap] at h11
    exact h11
  have hB3 : quadBiLin (T.val, B₃.val) = 0 := by
    have h11 := case₁ProjCoeff_zero_B₃ T h1
    rw [quad_B₃_proj] at h11
    rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h11
    simp only [ Fin.isValue, Fin.reduceFinMk, mul_eq_zero, OfNat.ofNat_ne_zero,
      false_or] at h11
    erw [quadBiLin.swap] at h11
    exact h11
  rw [proj_val]
  rw [quadBiLin.map_add₂, quadBiLin.map_add₂]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  rw [hY3, hB3]
  erw [quadSol T.1]
  simp

lemma case₁ProjCoeff_zero_self (T : MSSMACC.Sols) (h1 : case₁ProjCoeff T = 0)  :
    quadBiLin ((proj T.1.1).val, (proj T.1.1).val) = 0 := by
  nth_rewrite 1 [proj_val]
  rw [quadBiLin.map_add₁, quadBiLin.map_add₁]
  rw [quadBiLin.map_smul₁, quadBiLin.map_smul₁, quadBiLin.map_smul₁]
  rw [case₁ProjCoeff_zero_Y₃ T h1, case₁ProjCoeff_zero_B₃ T h1, case₁ProjCoeff_zero_T T h1]
  simp

lemma case₁ProjCoeff_zero (T : MSSMACC.Sols) :
    case₁ProjCoeff T = 0 ↔ case₂prop (proj T.1.1) := by
  apply Iff.intro
  intro h1
  rw [case₂prop]
  rw [case₁ProjCoeff_zero_self T h1, case₁ProjCoeff_zero_Y₃ T h1, case₁ProjCoeff_zero_B₃ T h1]
  simp only [and_self]
  intro h
  rw [case₂prop] at h
  rw [case₁ProjCoeff]
  rw [h.2.1, h.2.2]
  simp

lemma case₁ProjCoeff_ne_zero_case₂ (T : MSSMACC.Sols) (h1 : case₁ProjCoeff T ≠ 0) :
    ¬ case₂prop (proj T.1.1) :=
  (case₁ProjCoeff_zero T).mpr.mt h1

lemma case₁ProjCoeff_ne_zero_case₃ (T : MSSMACC.Sols) (h1 : case₁ProjCoeff T ≠ 0) :
    ¬ case₃prop (proj T.1.1) := by
  by_contra hn
  rw [case₃prop] at hn
  rw [case₁ProjCoeff] at h1
  simp_all


end proj

/-- The case where the plane lies entirely within the quadratic. -/
def case₂ (R : MSSMACC.AnomalyFreePerp) (a₁ a₂ a₃ : ℚ)
    (h : case₂prop R) : MSSMACC.Sols :=
  AnomalyFreeMk' (lineCube R a₁ a₂ a₃)
    (by
      erw [planeY₃B₃_quad]
      rw [h.1, h.2.1, h.2.2]
      simp)
    (lineCube_cube R a₁ a₂ a₃)

lemma case₂_smul (R : MSSMACC.AnomalyFreePerp) (c₁ c₂ c₃ d : ℚ)
    (h : case₂prop R) : case₂ R (d * c₁) (d * c₂) (d * c₃) h = d • case₂ R c₁ c₂ c₃ h := by
  apply ACCSystem.Sols.ext
  change (lineCube _ _ _ _).val = _
  rw [lineCube_smul]
  rfl

section proj

/-- The coefficent which multiplies a solution on passing through `case₂`. -/
def case₂ProjCoeff (T : MSSMACC.Sols) : ℚ :=
    3 * dot (Y₃.val, B₃.val) ^ 3 * (cubeTriLin (T.val, T.val, Y₃.val) ^ 2  +
    cubeTriLin (T.val, T.val, B₃.val) ^ 2 )

/-- The first parameter in `case₂` needed to form an inverse on `Proj`. -/
def case₂ProjC₁ (T : MSSMACC.Sols) : ℚ := cubeTriLin (T.val, T.val, B₃.val)

/-- The second parameter in `case₂` needed to form an inverse on `Proj`. -/
def case₂ProjC₂ (T : MSSMACC.Sols) : ℚ := - cubeTriLin (T.val, T.val, Y₃.val)

/-- The third parameter in `case₂` needed to form an inverse on `Proj`. -/
def case₂ProjC₃ (T : MSSMACC.Sols) : ℚ :=
  (- cubeTriLin (T.val, T.val, B₃.val) * (dot (Y₃.val, T.val) - dot (B₃.val, T.val))
  - cubeTriLin (T.val, T.val, Y₃.val) * (dot (Y₃.val, T.val) - 2 * dot (B₃.val, T.val)))

lemma case₂_proj (T : MSSMACC.Sols) (h1 : case₁ProjCoeff T = 0) :
    case₂ (proj T.1.1)
       (case₂ProjC₁ T)
       (case₂ProjC₂ T)
       (case₂ProjC₃ T)
       ((case₁ProjCoeff_zero T).mp h1)  = (case₂ProjCoeff T) • T := by
  apply ACCSystem.Sols.ext
  change (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [case₂ProjCoeff, case₂ProjC₁, case₂ProjC₂, case₂ProjC₃, cube_proj, cube_proj_proj_B₃,
    cube_proj_proj_Y₃]
  ring_nf
  simp
  rfl

lemma case₂ProjCoeff_ne_zero (T : MSSMACC.Sols) (h1 : case₁ProjCoeff T = 0)
    (hT : case₂ProjCoeff T ≠ 0 ) :
    (case₂ProjCoeff T)⁻¹ • case₂ (proj T.1.1)
      (case₂ProjC₁ T)
      (case₂ProjC₂ T)
      (case₂ProjC₃ T)
      ((case₁ProjCoeff_zero T).mp h1) = T := by
  rw [case₂_proj T h1, ← MulAction.mul_smul, mul_comm, mul_inv_cancel hT]
  simp

lemma case₂ProjCoeff_zero_Y₃_B₃ (T : MSSMACC.Sols) (h1 : case₂ProjCoeff T = 0) :
    cubeTriLin ((proj T.1.1).val, (proj T.1.1).val, Y₃.val) = 0 ∧
    cubeTriLin ((proj T.1.1).val, (proj T.1.1).val, B₃.val) = 0 := by
  rw [case₂ProjCoeff, mul_eq_zero] at h1
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h1
  simp at h1
  have h : cubeTriLin (T.val, T.val, Y₃.val) ^ 2 = 0 ∧
         cubeTriLin (T.val, T.val, B₃.val) ^ 2  = 0 :=
    (add_eq_zero_iff' (sq_nonneg _) (sq_nonneg _)).mp h1
  simp at h
  have h1 := cube_proj_proj_B₃ T.1.1
  erw [h.2] at h1
  have h2 := cube_proj_proj_Y₃ T.1.1
  erw [h.1] at h2
  simp_all


lemma case₂ProjCoeff_zero_Y₃ (T : MSSMACC.Sols) (h1 : case₂ProjCoeff T = 0) :
    cubeTriLin ((proj T.1.1).val, (proj T.1.1).val, Y₃.val)  = 0 :=
  (case₂ProjCoeff_zero_Y₃_B₃ T h1).left

lemma case₂ProjCoeff_zero_B₃ (T : MSSMACC.Sols) (h1 : case₂ProjCoeff T = 0) :
    cubeTriLin ((proj T.1.1).val, (proj T.1.1).val, B₃.val) = 0 :=
  (case₂ProjCoeff_zero_Y₃_B₃ T h1).right


lemma case₂ProjCoeff_zero_T (T : MSSMACC.Sols) (h1 : case₂ProjCoeff T = 0) :
    cubeTriLin ((proj T.1.1).val, (proj T.1.1).val, T.val) = 0 := by
  rw [cube_proj_proj_self]
  have hr : cubeTriLin (T.val, T.val, Y₃.val) = 0 := by
    have h11 := case₂ProjCoeff_zero_Y₃ T h1
    rw [cube_proj_proj_Y₃] at h11
    rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h11
    simp at h11
    exact h11
  have h2 : cubeTriLin (T.val, T.val, B₃.val) = 0 := by
    have h11 := case₂ProjCoeff_zero_B₃ T h1
    rw [cube_proj_proj_B₃] at h11
    rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h11
    simp at h11
    exact h11
  rw [hr, h2]
  simp

lemma case₂ProjCoeff_zero_self (T : MSSMACC.Sols) (h1 : case₂ProjCoeff T = 0)  :
    cubeTriLin ((proj T.1.1).val, (proj T.1.1).val, (proj T.1.1).val) = 0 := by
  nth_rewrite 3 [proj_val]
  rw [cubeTriLin.map_add₃, cubeTriLin.map_add₃]
  rw [cubeTriLin.map_smul₃, cubeTriLin.map_smul₃, cubeTriLin.map_smul₃]
  rw [case₂ProjCoeff_zero_Y₃ T h1, case₂ProjCoeff_zero_B₃ T h1, case₂ProjCoeff_zero_T T h1]
  simp


lemma case₂ProjCoeff_zero (T : MSSMACC.Sols) :
    (case₁ProjCoeff T = 0 ∧ case₂ProjCoeff T = 0) ↔ case₃prop (proj T.1.1) := by
  apply Iff.intro
  intro h1
  rw [case₃prop]
  rw [case₂ProjCoeff_zero_self T h1.2, case₂ProjCoeff_zero_Y₃ T h1.2, case₂ProjCoeff_zero_B₃ T h1.2]
  rw [case₁ProjCoeff_zero_self T h1.1, case₁ProjCoeff_zero_Y₃ T h1.1, case₁ProjCoeff_zero_B₃ T h1.1]
  simp only [and_self]
  intro h
  rw [case₃prop] at h
  rw [case₁ProjCoeff, case₂ProjCoeff]
  simp_all only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    mul_zero,  mul_eq_zero, pow_eq_zero_iff, false_or, true_and]
  erw [show dot (Y₃.val, B₃.val) = 108 by rfl]
  simp only [OfNat.ofNat_ne_zero, false_or]
  have h1' := cube_proj_proj_B₃ T.1.1
  have h2' := cube_proj_proj_Y₃ T.1.1
  erw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h1' h2'
  simp_all

lemma case₂ProjCoeff_ne_zero_case₃ (T : MSSMACC.Sols) (h1 : case₂ProjCoeff T ≠ 0) :
    ¬ case₃prop (proj T.1.1) := by
  have h1 : ¬ (case₁ProjCoeff T = 0 ∧ case₂ProjCoeff T = 0) := by
    simp_all
  exact (case₂ProjCoeff_zero T).mpr.mt h1

end proj

/-- The case where the plane lies entirely within the quadratic and cubic. -/
def case₃ (R : MSSMACC.AnomalyFreePerp) (b₁ b₂ b₃ : ℚ)
    (h₃ : case₃prop R)  :
    MSSMACC.Sols :=
  AnomalyFreeMk' (planeY₃B₃ R b₁ b₂ b₃)
  (by
    rw [planeY₃B₃_quad]
    rw [h₃.1, h₃.2.1, h₃.2.2.1]
    simp)
  (by
    rw [planeY₃B₃_cubic]
    rw [h₃.2.2.2.1, h₃.2.2.2.2.1, h₃.2.2.2.2.2]
    simp)

lemma case₃_smul (R : MSSMACC.AnomalyFreePerp) (c₁ c₂ c₃ d : ℚ)
    (h : case₃prop R) : case₃ R (d * c₁) (d * c₂) (d * c₃) h = d • case₃ R c₁ c₂ c₃ h := by
  apply ACCSystem.Sols.ext
  change (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_smul]
  rfl


section proj

/-- The coefficent which multiplies a solution on passing through `case₃`. -/
def case₃ProjCoeff : ℚ :=  dot (Y₃.val, B₃.val)

/-- The first parameter in `case₃` needed to form an inverse on `Proj`. -/
def case₃ProjC₁ (T : MSSMACC.Sols) : ℚ := (dot (Y₃.val, T.val) - dot (B₃.val, T.val))

/-- The second parameter in `case₃` needed to form an inverse on `Proj`. -/
def case₃ProjC₂ (T : MSSMACC.Sols) : ℚ := (2 * dot (B₃.val, T.val) - dot (Y₃.val, T.val))

lemma case₃_proj (T : MSSMACC.Sols) (h0 : case₁ProjCoeff T = 0) (h1 : case₂ProjCoeff T = 0) :
    case₃ (proj T.1.1)
       (case₃ProjC₁ T)
       (case₃ProjC₂ T)
       1
       ((case₂ProjCoeff_zero T).mp (And.intro h0 h1))  =  case₃ProjCoeff • T := by
  apply ACCSystem.Sols.ext
  change (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [case₃ProjC₁, case₃ProjC₂]
  ring_nf
  simp
  rfl

lemma case₃_smul_coeff (T : MSSMACC.Sols) (h0 : case₁ProjCoeff T = 0) (h1 : case₂ProjCoeff T = 0) :
    case₃ProjCoeff⁻¹ • case₃ (proj T.1.1)
       (case₃ProjC₁ T)
       (case₃ProjC₂ T)
       1
       ((case₂ProjCoeff_zero T).mp (And.intro h0 h1)) = T := by
  rw [case₃_proj T h0 h1]
  rw [← MulAction.mul_smul, mul_comm, mul_inv_cancel]
  simp only [one_smul]
  rw [case₃ProjCoeff]
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]

end proj

/-- A map from `MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ ` to `MSSMACC.Sols`.
This allows generation of solutions given elements of `MSSMACC.AnomalyFreePerp` and
three rational numbers. -/
def parameterization :
    MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ  →  MSSMACC.Sols := fun A =>
  if h₃ : case₃prop A.1 then
    case₃ A.1 A.2.1 A.2.2.1 A.2.2.2 h₃
  else
    if h₂ : case₂prop A.1 then
      case₂  A.1 A.2.1 A.2.2.1 A.2.2.2 h₂
    else
      if h₁ : case₁prop A.1 then
        case₁ A.1 A.2.1 A.2.2.1 A.2.2.2 h₁
      else
        A.2.1 • generic A.1

lemma parameterization_smul (R : MSSMACC.AnomalyFreePerp) (a b c d : ℚ) :
    parameterization (R, d * a, d * b, d * c) = d • parameterization (R, a, b, c) := by
  rw [parameterization, parameterization]
  by_cases h₃ : case₃prop R
  rw [dif_pos h₃, dif_pos h₃]
  rw [case₃_smul]
  rw [dif_neg h₃, dif_neg h₃]
  by_cases h₂ : case₂prop R
  rw [dif_pos h₂, dif_pos h₂]
  rw [case₂_smul]
  rw [dif_neg h₂, dif_neg h₂]
  by_cases h₁ : case₁prop R
  rw [dif_pos h₁, dif_pos h₁]
  rw [case₁_smul]
  rw [dif_neg h₁, dif_neg h₁]
  rw [mul_smul]

lemma parameterization_not₁₂₃ (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ)
    (h1 : ¬ case₁prop R) (h2 : ¬ case₂prop R) (h3 : ¬ case₃prop R) :
    parameterization (R, a, b, c) = a • generic R := by
  rw [parameterization]
  rw [dif_neg h3]
  rw [dif_neg h2]
  rw [dif_neg h1]

lemma parameterization_is₁_not₂₃ (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ)
    (h1 : case₁prop R) (h2 : ¬ case₂prop R) (h3 : ¬ case₃prop R) :
    parameterization (R, a, b, c) = case₁ R a b c h1:= by
  rw [parameterization]
  rw [dif_neg h3]
  rw [dif_neg h2]
  rw [dif_pos h1]

lemma parameterization_is₁₂_not₃ (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) (h2 : case₂prop R)
    (h3 : ¬ case₃prop R) : parameterization (R, a, b, c) = case₂ R a b c h2 := by
  rw [parameterization]
  rw [dif_neg h3]
  rw [dif_pos h2]

lemma parameterization_is₃ (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) (h3 : case₃prop R) :
    parameterization (R, a, b, c) = case₃ R a b c h3 := by
  rw [parameterization]
  rw [dif_pos h3]

/-- A right inverse of `parameterizaiton`. -/
def inverse (R : MSSMACC.Sols) : MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ :=
  if genericProjCoeff R ≠ 0 then
    (proj R.1.1, (genericProjCoeff R)⁻¹, 0, 0)
  else
    if case₁ProjCoeff R ≠ 0 then
      (proj R.1.1, (case₁ProjCoeff R)⁻¹ * case₁ProjC₁ R, (case₁ProjCoeff R)⁻¹ * case₁ProjC₂ R,
        (case₁ProjCoeff R)⁻¹ * case₁ProjC₃ R)
    else
      if case₂ProjCoeff R ≠ 0 then
        (proj R.1.1, (case₂ProjCoeff R)⁻¹ * case₂ProjC₁ R, (case₂ProjCoeff R)⁻¹ * case₂ProjC₂ R,
          (case₂ProjCoeff R)⁻¹ * case₂ProjC₃ R)
      else
        (proj R.1.1, (case₃ProjCoeff)⁻¹ * case₃ProjC₁ R, (case₃ProjCoeff)⁻¹ * case₃ProjC₂ R,
          (case₃ProjCoeff)⁻¹ * 1)

lemma inverse_generic (R : MSSMACC.Sols) (h : genericProjCoeff R ≠ 0) :
    inverse R = (proj R.1.1, (genericProjCoeff R)⁻¹, 0, 0) := by
  rw [inverse, if_pos h]

lemma inverse_case₁ (R : MSSMACC.Sols) (h0 : genericProjCoeff R = 0)
    (h1 : case₁ProjCoeff R ≠ 0) : inverse R = (proj R.1.1, (case₁ProjCoeff R)⁻¹ * case₁ProjC₁ R,
    (case₁ProjCoeff R)⁻¹ * case₁ProjC₂ R, (case₁ProjCoeff R)⁻¹ * case₁ProjC₃ R) := by
  rw [inverse]
  simp_all

lemma inverse_case₂ (R : MSSMACC.Sols) (h0 : genericProjCoeff R = 0)
    (h1 : case₁ProjCoeff R = 0) (h2 : case₂ProjCoeff R ≠ 0) : inverse R = (proj R.1.1,
    (case₂ProjCoeff R)⁻¹ * case₂ProjC₁ R,
    (case₂ProjCoeff R)⁻¹ * case₂ProjC₂ R, (case₂ProjCoeff R)⁻¹ * case₂ProjC₃ R) := by
  rw [inverse]
  simp_all

lemma inverse_case₃ (R : MSSMACC.Sols) (h0 : genericProjCoeff R = 0)
    (h1 : case₁ProjCoeff R = 0) (h2 : case₂ProjCoeff R = 0)  :
    inverse R =  (proj R.1.1, (case₃ProjCoeff)⁻¹ * case₃ProjC₁ R,
    (case₃ProjCoeff)⁻¹ * case₃ProjC₂ R,
    (case₃ProjCoeff)⁻¹ * 1) := by
  rw [inverse]
  simp_all

lemma inverse_parameterization (R : MSSMACC.Sols) :
    parameterization (inverse R) = R := by
  by_cases h0 : genericProjCoeff R ≠ 0
  rw [inverse_generic R h0]
  rw [parameterization_not₁₂₃ _ _ _ _ (genericProjCoeff_neq_zero_case₁ R h0)
   (genericProjCoeff_neq_zero_case₂ R h0) (genericProjCoeff_neq_zero_case₃ R h0)]
  rw [genericProjCoeff_ne_zero R h0]
  by_cases h1 : case₁ProjCoeff R ≠ 0
  simp at h0
  rw [inverse_case₁ R h0 h1]
  rw [parameterization_smul]
  rw [parameterization_is₁_not₂₃ _ _ _ _ ((genericProjCoeff_zero R).mp h0)
    (case₁ProjCoeff_ne_zero_case₂ R h1) (case₁ProjCoeff_ne_zero_case₃ R h1)]
  rw [case₁ProjCoeff_ne_zero R h0 h1]
  simp at h0 h1
  by_cases h2 : case₂ProjCoeff R ≠ 0
  rw [inverse_case₂ R h0 h1 h2]
  rw [parameterization_smul]
  rw [parameterization_is₁₂_not₃ _ _ _ _ ((case₁ProjCoeff_zero R).mp h1)
    (case₂ProjCoeff_ne_zero_case₃ R h2)]
  rw [case₂ProjCoeff_ne_zero R h1 h2]
  simp at h2
  rw [inverse_case₃ R h0 h1 h2]
  rw [parameterization_smul]
  rw [parameterization_is₃ _ _ _ _ ((case₂ProjCoeff_zero R).mp (And.intro h1 h2))]
  rw [case₃_smul_coeff R h1 h2]

theorem parameterization_surjective : Function.Surjective parameterization := by
  intro T
  use inverse T
  exact inverse_parameterization T


end MSSMACC
