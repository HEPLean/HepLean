/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.SMNu.Ordinary.Basic
/-!
# Dimension 7 plane

We work here in the three family case.
We give an example of a 7 dimensional plane on which every point satisfies the ACCs.

The main result of this file is `seven_dim_plane_exists` which states that there exists a
7 dimensional plane of charges on which every point satisfies the ACCs.
-/

namespace SMRHN
namespace SM
open SMνCharges
open SMνACCs
open BigOperators

namespace PlaneSeven

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₀ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 0, 0 => 1
  | 0, 1 => - 1
  | _, _ => 0)

lemma B₀_cubic (S T : (SM 3).Charges) : cubeTriLin B₀ S T =
    6 * (S (0 : Fin 18) * T (0 : Fin 18) - S (1 : Fin 18) * T (1 : Fin 18)) := by
  simp [Fin.sum_univ_three, B₀, Fin.divNat, Fin.modNat, finProdFinEquiv]
  ring

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₁ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 1, 0 => 1
  | 1, 1 => - 1
  | _, _ => 0)

lemma B₁_cubic (S T : (SM 3).Charges) : cubeTriLin B₁ S T =
    3 * (S (3 : Fin 18) * T (3 : Fin 18) - S (4 : Fin 18) * T (4 : Fin 18)) := by
  simp [Fin.sum_univ_three, B₁, Fin.divNat, Fin.modNat, finProdFinEquiv]
  ring

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₂ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 2, 0 => 1
  | 2, 1 => - 1
  | _, _ => 0)

lemma B₂_cubic (S T : (SM 3).Charges) : cubeTriLin B₂ S T =
    3 * (S (6 : Fin 18) * T (6 : Fin 18) - S (7 : Fin 18) * T (7 : Fin 18)) := by
  simp [Fin.sum_univ_three, B₂, Fin.divNat, Fin.modNat, finProdFinEquiv]
  ring

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₃ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 3, 0 => 1
  | 3, 1 => - 1
  | _, _ => 0)

lemma B₃_cubic (S T : (SM 3).Charges) : cubeTriLin B₃ S T =
    2 * (S (9 : Fin 18) * T (9 : Fin 18) - S (10 : Fin 18) * T (10 : Fin 18)) := by
  simp [Fin.sum_univ_three, B₃, Fin.divNat, Fin.modNat, finProdFinEquiv]
  ring_nf
  rfl

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₄ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 4, 0 => 1
  | 4, 1 => - 1
  | _, _ => 0)

lemma B₄_cubic (S T : (SM 3).Charges) : cubeTriLin B₄ S T =
    (S (12 : Fin 18) * T (12 : Fin 18) - S (13 : Fin 18) * T (13 : Fin 18)) := by
  simp [Fin.sum_univ_three, B₄, Fin.divNat, Fin.modNat, finProdFinEquiv]
  ring_nf
  rfl

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₅ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 5, 0 => 1
  | 5, 1 => - 1
  | _, _ => 0)

lemma B₅_cubic (S T : (SM 3).Charges) : cubeTriLin B₅ S T =
    (S (15 : Fin 18) * T (15 : Fin 18) - S (16 : Fin 18) * T (16 : Fin 18)) := by
  simp [Fin.sum_univ_three, B₅, Fin.divNat, Fin.modNat, finProdFinEquiv]
  ring_nf
  rfl

/-- A charge assignment forming one of the basis elements of the plane. -/
def B₆ : (SM 3).Charges := toSpeciesEquiv.invFun (fun s => fun i =>
  match s, i with
  | 1, 2 => 1
  | 2, 2 => -1
  | _, _ => 0)

lemma B₆_cubic (S T : (SM 3).Charges) : cubeTriLin B₆ S T =
    3 * (S (5 : Fin 18) * T (5 : Fin 18) - S (8 : Fin 18) * T (8 : Fin 18)) := by
  simp [Fin.sum_univ_three, B₆, Fin.divNat, Fin.modNat, finProdFinEquiv]
  ring_nf

/-- The charge assignments forming a basis of the plane. -/
@[simp]
def B : Fin 7 → (SM 3).Charges := fun i =>
  match i with
  | 0 => B₀
  | 1 => B₁
  | 2 => B₂
  | 3 => B₃
  | 4 => B₄
  | 5 => B₅
  | 6 => B₆

lemma B₀_Bi_cubic {i : Fin 7} (hi : 0 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 0) (B i) S = 0 := by
  change cubeTriLin B₀ (B i) S = 0
  rw [B₀_cubic]
  fin_cases i <;>
    simp at hi <;>
    simp [B₀, B₁, B₂, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat, finProdFinEquiv]

lemma B₁_Bi_cubic {i : Fin 7} (hi : 1 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 1) (B i) S = 0 := by
  change cubeTriLin B₁ (B i) S = 0
  rw [B₁_cubic]
  fin_cases i <;>
    simp at hi <;>
    simp [B₀, B₁, B₂, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat, finProdFinEquiv]

lemma B₂_Bi_cubic {i : Fin 7} (hi : 2 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 2) (B i) S = 0 := by
  change cubeTriLin B₂ (B i) S = 0
  rw [B₂_cubic]
  fin_cases i <;>
    simp at hi <;>
    simp [B₀, B₁, B₂, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat, finProdFinEquiv]

lemma B₃_Bi_cubic {i : Fin 7} (hi : 3 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 3) (B i) S = 0 := by
  change cubeTriLin (B₃) (B i) S = 0
  rw [B₃_cubic]
  fin_cases i <;>
  simp at hi <;>
  simp [B₀, B₁, B₂, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat, finProdFinEquiv]

lemma B₄_Bi_cubic {i : Fin 7} (hi : 4 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 4) (B i) S = 0 := by
  change cubeTriLin (B₄) (B i) S = 0
  rw [B₄_cubic]
  fin_cases i <;>
  simp at hi <;>
  simp [B₀, B₁, B₂, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat, finProdFinEquiv]

lemma B₅_Bi_cubic {i : Fin 7} (hi : 5 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 5) (B i) S = 0 := by
  change cubeTriLin (B₅) (B i) S = 0
  rw [B₅_cubic]
  fin_cases i <;>
  simp at hi <;>
  simp [B₀, B₁, B₂, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat, finProdFinEquiv]

lemma B₆_Bi_cubic {i : Fin 7} (hi : 6 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 6) (B i) S = 0 := by
  change cubeTriLin (B₆) (B i) S = 0
  rw [B₆_cubic]
  fin_cases i <;>
  simp at hi <;>
  simp [B₀, B₁, B₂, B₃, B₄, B₅, B₆, Fin.divNat, Fin.modNat, finProdFinEquiv]

lemma Bi_Bj_ne_cubic {i j : Fin 7} (h : i ≠ j) (S : (SM 3).Charges) :
    cubeTriLin (B i) (B j) S = 0 := by
  fin_cases i
  · exact B₀_Bi_cubic h S
  · exact B₁_Bi_cubic h S
  · exact B₂_Bi_cubic h S
  · exact B₃_Bi_cubic h S
  · exact B₄_Bi_cubic h S
  · exact B₅_Bi_cubic h S
  · exact B₆_Bi_cubic h S

lemma B₀_B₀_Bi_cubic {i : Fin 7} :
    cubeTriLin (B 0) (B 0) (B i) = 0 := by
  change cubeTriLin (B₀) (B₀) (B i) = 0
  rw [B₀_cubic]
  fin_cases i <;> rfl

lemma B₁_B₁_Bi_cubic {i : Fin 7} :
    cubeTriLin (B 1) (B 1) (B i) = 0 := by
  change cubeTriLin (B₁) (B₁) (B i) = 0
  rw [B₁_cubic]
  fin_cases i <;> rfl

lemma B₂_B₂_Bi_cubic {i : Fin 7} :
    cubeTriLin (B 2) (B 2) (B i) = 0 := by
  change cubeTriLin (B₂) (B₂) (B i) = 0
  rw [B₂_cubic]
  fin_cases i <;> rfl

lemma B₃_B₃_Bi_cubic {i : Fin 7} :
    cubeTriLin (B 3) (B 3) (B i) = 0 := by
  change cubeTriLin (B₃) (B₃) (B i) = 0
  rw [B₃_cubic]
  fin_cases i <;> rfl

lemma B₄_B₄_Bi_cubic {i : Fin 7} :
    cubeTriLin (B 4) (B 4) (B i) = 0 := by
  change cubeTriLin (B₄) (B₄) (B i) = 0
  rw [B₄_cubic]
  fin_cases i <;> rfl

lemma B₅_B₅_Bi_cubic {i : Fin 7} :
    cubeTriLin (B 5) (B 5) (B i) = 0 := by
  change cubeTriLin (B₅) (B₅) (B i) = 0
  rw [B₅_cubic]
  fin_cases i <;> rfl

lemma B₆_B₆_Bi_cubic {i : Fin 7} :
    cubeTriLin (B 6) (B 6) (B i) = 0 := by
  change cubeTriLin (B₆) (B₆) (B i) = 0
  rw [B₆_cubic]
  fin_cases i <;> rfl

lemma Bi_Bi_Bj_cubic (i j : Fin 7) :
    cubeTriLin (B i) (B i) (B j) = 0 := by
  fin_cases i
  · exact B₀_B₀_Bi_cubic
  · exact B₁_B₁_Bi_cubic
  · exact B₂_B₂_Bi_cubic
  · exact B₃_B₃_Bi_cubic
  · exact B₄_B₄_Bi_cubic
  · exact B₅_B₅_Bi_cubic
  · exact B₆_B₆_Bi_cubic

lemma Bi_Bj_Bk_cubic (i j k : Fin 7) :
    cubeTriLin (B i) (B j) (B k) = 0 := by
  by_cases hij : i ≠ j
  · exact Bi_Bj_ne_cubic hij (B k)
  · simp at hij
    rw [hij]
    exact Bi_Bi_Bj_cubic j k

theorem B_in_accCube (f : Fin 7 → ℚ) : accCube (∑ i, f i • B i) = 0 := by
  change cubeTriLin _ _ _ = 0
  rw [cubeTriLin.map_sum₁₂₃]
  apply Fintype.sum_eq_zero _ fun i ↦ Fintype.sum_eq_zero _ fun k ↦ Fintype.sum_eq_zero _ fun l ↦ ?_
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃, Bi_Bj_Bk_cubic]
  simp

lemma B_sum_is_sol (f : Fin 7 → ℚ) : (SM 3).IsSolution (∑ i, f i • B i) := by
  let X := chargeToAF (∑ i, f i • B i) (by
    rw [map_sum]
    apply Fintype.sum_eq_zero _ fun i ↦ ?_
    rw [map_smul]
    have h : accGrav (B i) = 0 := by
      fin_cases i <;> rfl
    rw [h]
    exact DistribMulAction.smul_zero (f i))
    (by
      rw [map_sum]
      apply Fintype.sum_eq_zero _ fun i ↦ ?_
      rw [map_smul]
      have h : accSU2 (B i) = 0 := by fin_cases i <;> rfl
      rw [h]
      exact DistribMulAction.smul_zero (f i))
    (by
      rw [map_sum]
      apply Fintype.sum_eq_zero _ fun i ↦ ?_
      rw [map_smul]
      have h : accSU3 (B i) = 0 := by fin_cases i <;> rfl
      rw [h]
      exact DistribMulAction.smul_zero (f i))
    (B_in_accCube f)
  use X
  rfl

theorem basis_linear_independent : LinearIndependent ℚ B := by
  refine Fintype.linearIndependent_iff.mpr fun f h ↦ ?_
  have h0 := congrFun h (0 : Fin 18)
  have h1 := congrFun h (3 : Fin 18)
  have h2 := congrFun h (6 : Fin 18)
  have h3 := congrFun h (9 : Fin 18)
  have h4 := congrFun h (12 : Fin 18)
  have h5 := congrFun h (15 : Fin 18)
  have h6 := congrFun h (5 : Fin 18)
  rw [@Fin.sum_univ_seven] at h0 h1 h2 h3 h4 h5 h6
  simp [HSMul.hSMul] at h0 h1 h2 h3 h4 h5 h6
  rw [B₀, B₁, B₂, B₃, B₄, B₅, B₆] at h0 h1 h2 h3 h4 h5 h6
  simp [Fin.divNat, Fin.modNat] at h0 h1 h2 h3 h4 h5 h6
  intro i
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | 6 => exact h6

end PlaneSeven

theorem seven_dim_plane_exists : ∃ (B : Fin 7 → (SM 3).Charges),
    LinearIndependent ℚ B ∧ ∀ (f : Fin 7 → ℚ), (SM 3).IsSolution (∑ i, f i • B i) :=
  ⟨PlaneSeven.B, And.intro PlaneSeven.basis_linear_independent PlaneSeven.B_sum_is_sol⟩

end SM
end SMRHN
