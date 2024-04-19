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

namespace AnomalyFreePerp

def lineEqProp (R : MSSMACC.AnomalyFreePerp) : Prop :=
  α₁ R = 0 ∧ α₂ R = 0 ∧ α₃ R = 0


instance (R : MSSMACC.AnomalyFreePerp) : Decidable (lineEqProp R) := by
  apply And.decidable


def lineEqPropSol (R : MSSMACC.Sols) : Prop :=
  cubeTriLin (R.val, R.val, Y₃.val) * quadBiLin (B₃.val, R.val) -
  cubeTriLin (R.val, R.val, B₃.val) * quadBiLin (Y₃.val, R.val) = 0

def lineEqCoeff (T : MSSMACC.Sols) : ℚ := dot (Y₃.val, B₃.val) * α₃ (proj T.1.1)

lemma lineEqPropSol_iff_lineEqCoeff_zero (T : MSSMACC.Sols) :
    lineEqPropSol T ↔ lineEqCoeff T = 0 := by
  rw [lineEqPropSol, lineEqCoeff, α₃]
  simp only [Fin.isValue, Fin.reduceFinMk, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or]
  rw [cube_proj_proj_B₃, cube_proj_proj_Y₃, quad_B₃_proj, quad_Y₃_proj]
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl]
  simp only [Fin.isValue, Fin.reduceFinMk, OfNat.ofNat_ne_zero, false_or]
  have h1 : 108 ^ 2 * cubeTriLin (T.val, T.val, Y₃.val) * (108 * quadBiLin (B₃.val, T.val)) -
      108 ^ 2 * cubeTriLin (T.val, T.val, B₃.val) * (108 * quadBiLin (Y₃.val, T.val)) =
      108 ^ 3 * (cubeTriLin (T.val, T.val, Y₃.val) * quadBiLin (B₃.val, T.val) -
      cubeTriLin (T.val, T.val, B₃.val) * quadBiLin (Y₃.val, T.val) ) := by
    ring
  rw [h1]
  simp

lemma linEqPropSol_iff_proj_linEqProp (R : MSSMACC.Sols) :
    lineEqPropSol R ↔ lineEqProp (proj R.1.1) := by
  rw [lineEqPropSol_iff_lineEqCoeff_zero, lineEqCoeff, lineEqProp]
  apply Iff.intro
  intro h
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h
  simp at h
  rw [α₁_proj, α₂_proj, h]
  simp
  intro h
  rw [h.2.2]
  simp


/-- Case₂ is defined when the plane lies entirely within the quadratic. -/
def inQuadProp (R : MSSMACC.AnomalyFreePerp) : Prop :=
    quadBiLin (R.val, R.val) = 0 ∧ quadBiLin (Y₃.val, R.val) = 0 ∧ quadBiLin (B₃.val, R.val) = 0

instance (R : MSSMACC.AnomalyFreePerp) : Decidable (inQuadProp R) := by
  apply And.decidable

def inQuadSolProp (R : MSSMACC.Sols) : Prop :=
    quadBiLin (Y₃.val, R.val) = 0 ∧ quadBiLin (B₃.val, R.val) = 0

/-- The coefficent which multiplies a solution on passing through `case₁`. -/
def quadCoeff (T : MSSMACC.Sols) : ℚ :=
    2 * dot (Y₃.val, B₃.val) ^ 2 *
    (quadBiLin (Y₃.val, T.val) ^ 2 + quadBiLin (B₃.val, T.val) ^ 2)

lemma inQuadSolProp_iff_quadCoeff_zero (T : MSSMACC.Sols) : inQuadSolProp T ↔ quadCoeff T = 0 := by
  apply Iff.intro
  intro h
  rw [quadCoeff, h.1, h.2]
  simp
  intro h
  rw [quadCoeff] at h
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h
  simp only [ Fin.isValue, Fin.reduceFinMk, mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq,
    not_false_eq_true, pow_eq_zero_iff, or_self, false_or] at h
  apply (add_eq_zero_iff' (sq_nonneg _) (sq_nonneg _)).mp at h
  simp only [Fin.isValue, Fin.reduceFinMk, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff] at h
  exact h

lemma inQuadSolProp_iff_proj_inQuadProp (R : MSSMACC.Sols) :
    inQuadSolProp R ↔ inQuadProp (proj R.1.1) := by
  rw [inQuadSolProp, inQuadProp]
  rw [quad_proj, quad_Y₃_proj, quad_B₃_proj]
  apply Iff.intro
  intro h
  rw [h.1, h.2]
  simp
  intro h
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h
  simp only [dot_toFun, Fin.isValue, Fin.reduceFinMk , mul_eq_zero,
    OfNat.ofNat_ne_zero, or_self, false_or] at h
  rw [h.2.1, h.2.2]
  simp

/-- Case₃ is defined when the plane lies entirely within the quadratic and cubic. -/
def inCubeProp (R : MSSMACC.AnomalyFreePerp) : Prop :=
    cubeTriLin (R.val, R.val, R.val) = 0 ∧ cubeTriLin (R.val, R.val, B₃.val) = 0 ∧
    cubeTriLin (R.val, R.val, Y₃.val) = 0


instance (R : MSSMACC.AnomalyFreePerp) : Decidable (inCubeProp R) := by
  apply And.decidable

def inCubeSolProp (R : MSSMACC.Sols) : Prop :=
    cubeTriLin (R.val, R.val, B₃.val) = 0 ∧ cubeTriLin (R.val, R.val, Y₃.val) = 0

def cubicCoeff (T : MSSMACC.Sols) : ℚ :=
    3 * dot (Y₃.val, B₃.val) ^ 3 * (cubeTriLin (T.val, T.val, Y₃.val) ^ 2  +
    cubeTriLin (T.val, T.val, B₃.val) ^ 2 )

lemma inCubeSolProp_iff_cubicCoeff_zero (T : MSSMACC.Sols) :
    inCubeSolProp T ↔ cubicCoeff T = 0 := by
  apply Iff.intro
  intro h
  rw [cubicCoeff, h.1, h.2]
  simp
  intro h
  rw [cubicCoeff] at h
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h
  simp only [ Fin.isValue, Fin.reduceFinMk, mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq,
    not_false_eq_true, pow_eq_zero_iff, or_self, false_or] at h
  apply (add_eq_zero_iff' (sq_nonneg _) (sq_nonneg _)).mp at h
  simp only [Fin.isValue, Fin.reduceFinMk, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, pow_eq_zero_iff] at h
  exact h.symm

lemma inCubeSolProp_iff_proj_inCubeProp (R : MSSMACC.Sols) :
    inCubeSolProp R ↔ inCubeProp (proj R.1.1) := by
  rw [inCubeSolProp, inCubeProp]
  rw [cube_proj, cube_proj_proj_Y₃, cube_proj_proj_B₃]
  apply Iff.intro
  intro h
  rw [h.1, h.2]
  simp
  intro h
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl] at h
  simp only [dot_toFun, Fin.isValue, Fin.reduceFinMk, mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq,
    not_false_eq_true, pow_eq_zero_iff, or_self, false_or] at h
  rw [h.2.1, h.2.2]
  simp


/-- Given a `R ∈ LinSols` perpendicular to $Y_3$, and $B_3$, a solution to the quadratic. -/
def toSolNSQuad (R : MSSMACC.AnomalyFreePerp) : MSSMACC.QuadSols :=
  lineQuad R
    (3 * cubeTriLin (R.val, R.val, Y₃.val))
    (3 * cubeTriLin (R.val, R.val, B₃.val))
    (cubeTriLin (R.val, R.val, R.val))

lemma toSolNSQuad_cube (R : MSSMACC.AnomalyFreePerp) :
    accCube (toSolNSQuad R).val = 0 := by
  rw [toSolNSQuad]
  rw [lineQuad_val]
  rw [planeY₃B₃_cubic]
  ring

lemma toSolNSQuad_eq_planeY₃B₃_on_α (R : MSSMACC.AnomalyFreePerp) :
    (toSolNSQuad R).1 = planeY₃B₃ R (α₁ R) (α₂ R) (α₃ R) := by
  change (planeY₃B₃ _ _ _ _) = _
  apply planeY₃B₃_eq
  rw [α₁, α₂, α₃]
  ring_nf
  simp

/-- Given a `R ∈ LinSols` perpendicular to $Y_3$, and $B_3$, a element of `Sols`. -/
def toSolNS : MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ →  MSSMACC.Sols := fun (R, a, _ , _) =>
  a • AnomalyFreeMk'' (toSolNSQuad R) (toSolNSQuad_cube R)

def toSolNSProj (T : MSSMACC.Sols) : MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ :=
  (proj T.1.1, (lineEqCoeff T)⁻¹, 0, 0)

lemma toSolNS_proj (T : MSSMACC.Sols) (h : lineEqCoeff T ≠ 0) :
    toSolNS (toSolNSProj T) = T := by
  apply ACCSystem.Sols.ext
  rw [toSolNS, toSolNSProj]
  change (lineEqCoeff T)⁻¹ • (toSolNSQuad _).1.1 =  _
  rw [toSolNSQuad_eq_planeY₃B₃_on_α]
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [α₁_proj, α₂_proj]
  ring_nf
  simp only [zero_smul, add_zero, Fin.isValue, Fin.reduceFinMk, zero_add]
  have h1 : α₃ (proj T.toLinSols) * dot (Y₃.val, B₃.val) = lineEqCoeff T := by
    rw [lineEqCoeff]
    ring
  rw [h1]
  rw [← MulAction.mul_smul, mul_comm, mul_inv_cancel h]
  simp

def inLineEq : Type := {R : MSSMACC.AnomalyFreePerp // lineEqProp R}

def inLineEqSol : Type := {R : MSSMACC.Sols // lineEqPropSol R}

def inLineEqProj (T : inLineEqSol) : inLineEq × ℚ × ℚ × ℚ :=
  (⟨proj T.val.1.1, (linEqPropSol_iff_proj_linEqProp T.val).mp T.prop ⟩,
  (quadCoeff T.val)⁻¹ * quadBiLin (B₃.val, T.val.val),
  (quadCoeff T.val)⁻¹ * (- quadBiLin (Y₃.val, T.val.val)),
  (quadCoeff T.val)⁻¹ * (- quadBiLin (B₃.val, T.val.val) * ( dot (Y₃.val, T.val.val)
  - dot (B₃.val, T.val.val))
  - quadBiLin (Y₃.val, T.val.val) * ( dot (Y₃.val, T.val.val) - 2 * dot (B₃.val, T.val.val))))

def inLineEqToSol : inLineEq × ℚ × ℚ × ℚ → MSSMACC.Sols := fun (R, c₁, c₂, c₃) =>
  AnomalyFreeMk'' (lineQuad R.val c₁ c₂ c₃)
    (by
      rw [lineQuad_cube]
      rw [R.prop.1, R.prop.2.1, R.prop.2.2]
      simp)

lemma inLineEqTo_smul (R : inLineEq) (c₁ c₂ c₃ d : ℚ) :
    inLineEqToSol (R, (d * c₁), (d * c₂), (d * c₃)) = d • inLineEqToSol (R, c₁, c₂, c₃) := by
  apply ACCSystem.Sols.ext
  change (lineQuad _ _ _ _).val = _
  rw [lineQuad_smul]
  rfl

lemma inLineEqToSol_proj (T : inLineEqSol) (h : quadCoeff T.val ≠ 0) :
    inLineEqToSol (inLineEqProj T) = T.val := by
  rw [inLineEqProj, inLineEqTo_smul]
  apply ACCSystem.Sols.ext
  change _ • (lineQuad _ _ _ _).val = _
  rw [lineQuad_val]
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [quad_proj, quad_Y₃_proj, quad_B₃_proj]
  ring_nf
  simp only [zero_smul, add_zero, Fin.isValue, Fin.reduceFinMk, zero_add]
  have h1 : (quadBiLin (Y₃.val, (T).val.val) ^ 2 * dot (Y₃.val, B₃.val) ^ 2 * 2 +
      dot (Y₃.val, B₃.val) ^ 2 * quadBiLin (B₃.val, (T).val.val) ^ 2 * 2) = quadCoeff T.val := by
    rw [quadCoeff]
    ring
  rw [h1]
  rw [← MulAction.mul_smul, mul_comm, mul_inv_cancel h]
  simp


def inQuad : Type := {R : inLineEq // inQuadProp R.val}

def inQuadSol : Type := {R : inLineEqSol // inQuadSolProp R.val}

def inQuadToSol : inQuad × ℚ × ℚ × ℚ →  MSSMACC.Sols := fun (R, a₁, a₂, a₃) =>
  AnomalyFreeMk' (lineCube R.val.val a₁ a₂ a₃)
    (by
      erw [planeY₃B₃_quad]
      rw [R.prop.1, R.prop.2.1, R.prop.2.2]
      simp)
    (lineCube_cube R.val.val a₁ a₂ a₃)

lemma inQuadToSol_smul (R : inQuad) (c₁ c₂ c₃ d : ℚ) :
    inQuadToSol (R, (d * c₁), (d * c₂), (d * c₃)) = d • inQuadToSol (R, c₁, c₂, c₃) := by
  apply ACCSystem.Sols.ext
  change (lineCube _ _ _ _).val = _
  rw [lineCube_smul]
  rfl

def inQuadProj (T : inQuadSol) : inQuad × ℚ × ℚ × ℚ :=
  (⟨⟨proj T.val.val.1.1, (linEqPropSol_iff_proj_linEqProp T.val.val).mp T.val.prop ⟩,
    (inQuadSolProp_iff_proj_inQuadProp T.val.val).mp T.prop⟩,
  (cubicCoeff T.val.val)⁻¹ * (cubeTriLin (T.val.val.val, T.val.val.val, B₃.val)),
  (cubicCoeff T.val.val)⁻¹ * (- cubeTriLin (T.val.val.val, T.val.val.val, Y₃.val)),
  (cubicCoeff T.val.val)⁻¹ * (- cubeTriLin (T.val.val.val, T.val.val.val, B₃.val)
    * (dot (Y₃.val, T.val.val.val) - dot (B₃.val, T.val.val.val))
    - cubeTriLin (T.val.val.val, T.val.val.val, Y₃.val)
    * (dot (Y₃.val, T.val.val.val) - 2 * dot (B₃.val, T.val.val.val))))


lemma inQuadToSol_proj (T : inQuadSol) (h : cubicCoeff T.val.val ≠ 0) :
    inQuadToSol (inQuadProj T) = T.val.val := by
  rw [inQuadProj, inQuadToSol_smul]
  apply ACCSystem.Sols.ext
  change _ • (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [cube_proj, cube_proj_proj_B₃, cube_proj_proj_Y₃]
  ring_nf
  simp only [zero_smul, add_zero, Fin.isValue, Fin.reduceFinMk, zero_add]
  have h1 : (cubeTriLin (T.val.val.val, T.val.val.val, Y₃.val) ^ 2 * dot (Y₃.val, B₃.val) ^ 3 * 3 +
      dot (Y₃.val, B₃.val) ^ 3 * cubeTriLin (T.val.val.val, T.val.val.val, B₃.val) ^ 2
       * 3) = cubicCoeff T.val.val := by
    rw [cubicCoeff]
    ring
  rw [h1]
  rw [← MulAction.mul_smul, mul_comm, mul_inv_cancel h]
  simp

def inQuadCube : Type := {R : inQuad // inCubeProp R.val.val}

def inQuadCubeSol : Type := {R : inQuadSol // inCubeSolProp R.val.val}

/-- The case where the plane lies entirely within the quadratic and cubic. -/
def inQuadCubeToSol : inQuadCube × ℚ × ℚ × ℚ → MSSMACC.Sols := fun (R, b₁, b₂, b₃) =>
  AnomalyFreeMk' (planeY₃B₃ R.val.val.val b₁ b₂ b₃)
  (by
    rw [planeY₃B₃_quad]
    rw [R.val.prop.1, R.val.prop.2.1, R.val.prop.2.2]
    simp)
  (by
    rw [planeY₃B₃_cubic]
    rw [R.prop.1, R.prop.2.1, R.prop.2.2]
    simp)

lemma inQuadCubeToSol_smul (R : inQuadCube) (c₁ c₂ c₃ d : ℚ) :
    inQuadCubeToSol (R, (d * c₁), (d * c₂), (d * c₃)) = d • inQuadCubeToSol (R, c₁, c₂, c₃):= by
  apply ACCSystem.Sols.ext
  change (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_smul]
  rfl


def inQuadCubeProj (T : inQuadCubeSol) : inQuadCube × ℚ × ℚ × ℚ :=
  (⟨⟨⟨proj T.val.val.val.1.1, (linEqPropSol_iff_proj_linEqProp T.val.val.val).mp T.val.val.prop ⟩,
    (inQuadSolProp_iff_proj_inQuadProp T.val.val.val).mp T.val.prop⟩,
    (inCubeSolProp_iff_proj_inCubeProp T.val.val.val).mp T.prop⟩,
  (dot (Y₃.val, B₃.val)) ⁻¹  * (dot (Y₃.val, T.val.val.val.val) - dot (B₃.val, T.val.val.val.val)),
  (dot (Y₃.val, B₃.val)) ⁻¹  * (2 * dot (B₃.val, T.val.val.val.val) -
  dot (Y₃.val, T.val.val.val.val)), (dot (Y₃.val, B₃.val)) ⁻¹ * 1)

lemma inQuadCubeToSol_proj (T : inQuadCubeSol) :
    inQuadCubeToSol (inQuadCubeProj T) = T.val.val.val := by
  rw [inQuadCubeProj, inQuadCubeToSol_smul]
  apply ACCSystem.Sols.ext
  change _ • (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  ring_nf
  simp only [Fin.isValue, Fin.reduceFinMk, zero_smul, add_zero, zero_add]
  rw [← MulAction.mul_smul, mul_comm, mul_inv_cancel]
  simp only [one_smul]
  rw [show dot (Y₃.val, B₃.val) = 108 by rfl]
  simp

def toSol :
    MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ  →  MSSMACC.Sols := fun (R, a, b, c) =>
  if h₃ : lineEqProp R ∧ inQuadProp R ∧ inCubeProp R  then
    inQuadCubeToSol (⟨⟨⟨R, h₃.1⟩, h₃.2.1⟩, h₃.2.2⟩, a, b, c)
  else
    if h₂ : lineEqProp R ∧ inQuadProp R then
      inQuadToSol (⟨⟨R, h₂.1⟩, h₂.2⟩, a, b, c)
    else
      if h₁ : lineEqProp R then
        inLineEqToSol (⟨R, h₁⟩, a, b, c)
      else
        toSolNS ⟨R, a, b, c⟩

lemma toSol_toSolNSProj (T : MSSMACC.Sols) (h₁ : ¬ lineEqPropSol T) :
    toSol (toSolNSProj T) = T := by
  have h1 : ¬ lineEqProp (toSolNSProj T).1 := (linEqPropSol_iff_proj_linEqProp T).mpr.mt h₁
  rw [toSol]
  simp_all
  exact toSolNS_proj T (mt (lineEqPropSol_iff_lineEqCoeff_zero T).mpr h₁)

lemma toSol_inLineEq (T : MSSMACC.Sols) (h₁ : lineEqPropSol T) (h₂ : ¬ inQuadSolProp T) :
    ∃ X, toSol X = T := by
  let X := inLineEqProj ⟨T, h₁⟩
  use ⟨X.1.val, X.2.1, X.2.2⟩
  have ha₁ : ¬ inQuadProp X.1.val := (inQuadSolProp_iff_proj_inQuadProp T).mpr.mt h₂
  have ha₂ : lineEqProp X.1.val := (linEqPropSol_iff_proj_linEqProp T).mp h₁
  rw [toSol]
  simp_all
  exact inLineEqToSol_proj ⟨T, h₁⟩ (mt (inQuadSolProp_iff_quadCoeff_zero T).mpr h₂)

lemma toSol_inQuad (T : MSSMACC.Sols) (h₁ : lineEqPropSol T) (h₂ : inQuadSolProp T)
    (h₃ : ¬ inCubeSolProp T) : ∃ X, toSol X = T := by
  let X := inQuadProj ⟨⟨T, h₁⟩, h₂⟩
  use ⟨X.1.val.val, X.2.1, X.2.2⟩
  have ha₁ : ¬ inCubeProp X.1.val.val := (inCubeSolProp_iff_proj_inCubeProp T).mpr.mt h₃
  have ha₂ : inQuadProp X.1.val.val := (inQuadSolProp_iff_proj_inQuadProp T).mp h₂
  have ha₃ : lineEqProp X.1.val.val := (linEqPropSol_iff_proj_linEqProp T).mp h₁
  rw [toSol]
  simp_all
  exact inQuadToSol_proj ⟨⟨T, h₁⟩, h₂⟩ (mt (inCubeSolProp_iff_cubicCoeff_zero T).mpr h₃)

lemma toSol_inQuadCube (T : MSSMACC.Sols) (h₁ : lineEqPropSol T) (h₂ : inQuadSolProp T)
    (h₃ : inCubeSolProp T) : ∃ X, toSol X = T := by
  let X := inQuadCubeProj ⟨⟨⟨T, h₁⟩, h₂⟩, h₃⟩
  use ⟨X.1.val.val.val, X.2.1, X.2.2⟩
  have ha₁ : inCubeProp X.1.val.val.val := (inCubeSolProp_iff_proj_inCubeProp T).mp h₃
  have ha₂ : inQuadProp X.1.val.val.val := (inQuadSolProp_iff_proj_inQuadProp T).mp h₂
  have ha₃ : lineEqProp X.1.val.val.val := (linEqPropSol_iff_proj_linEqProp T).mp h₁
  rw [toSol]
  simp_all
  exact inQuadCubeToSol_proj ⟨⟨⟨T, h₁⟩, h₂⟩, h₃⟩

theorem toSol_surjective : Function.Surjective toSol := by
  intro T
  by_cases h₁ : ¬ lineEqPropSol T
  use toSolNSProj T
  exact toSol_toSolNSProj T h₁
  simp at h₁
  by_cases h₂ : ¬ inQuadSolProp T
  exact toSol_inLineEq T h₁ h₂
  simp at h₂
  by_cases h₃ : ¬ inCubeSolProp T
  exact toSol_inQuad T h₁ h₂ h₃
  simp at h₃
  exact toSol_inQuadCube T h₁ h₂ h₃


end AnomalyFreePerp

end MSSMACC
