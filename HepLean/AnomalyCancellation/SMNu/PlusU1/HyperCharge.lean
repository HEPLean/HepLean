/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.SMNu.PlusU1.Basic
import HepLean.AnomalyCancellation.SMNu.PlusU1.FamilyMaps
/-!
# Hypercharge in SM with RHN.

Relavent definitions for the SM hypercharge.

-/
universe v u

namespace SMRHN
namespace PlusU1

open SMνCharges
open SMνACCs
open BigOperators

/-- The hypercharge for 1 family. -/
@[simps!]
def Y₁ : (PlusU1 1).Sols where
  val := fun i =>
    match i with
    | (0 : Fin 6) => 1
    | (1 : Fin 6)  => -4
    | (2 : Fin 6)  => 2
    | (3 : Fin 6)  => -3
    | (4 : Fin 6)  => 6
    | (5 : Fin 6)  => 0
  linearSol := by
    intro i
    simp at i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
  quadSol := by
    intro i
    simp at i
    match i with
    | 0 => rfl
  cubicSol := by rfl

/-- The hypercharge for `n` family. -/
@[simps!]
def Y (n : ℕ) : (PlusU1 n).Sols :=
  familyUniversalAF n Y₁

namespace Y

variable {n : ℕ}

lemma on_quadBiLin (S : (PlusU1 n).charges) :
    quadBiLin (Y n).val S = accYY S := by
  erw [familyUniversal_quadBiLin]
  rw [accYY_decomp]
  simp only [Fin.isValue, Y₁_val, SMνSpecies_numberCharges, toSpecies_apply, one_mul, mul_neg,
    neg_mul, sub_neg_eq_add, add_left_inj, add_right_inj, mul_eq_mul_right_iff]
  ring_nf
  simp

lemma on_quadBiLin_AFL (S : (PlusU1 n).LinSols) : quadBiLin (Y n).val S.val = 0 := by
  rw [on_quadBiLin]
  rw [YYsol S]


lemma add_AFL_quad (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accQuad (a • S.val + b • (Y n).val) = a ^ 2 * accQuad S.val := by
  erw [BiLinearSymm.toHomogeneousQuad_add, quadSol (b • (Y n)).1]
  rw [quadBiLin.map_smul₁, quadBiLin.map_smul₂, quadBiLin.swap, on_quadBiLin_AFL]
  erw [accQuad.map_smul]
  simp

lemma add_quad (S : (PlusU1 n).QuadSols) (a b : ℚ) :
    accQuad (a • S.val + b • (Y n).val) = 0 := by
  rw [add_AFL_quad, quadSol S]
  simp

/-- The `QuadSol` obtained by adding hypercharge to a `QuadSol`. -/
def addQuad (S : (PlusU1 n).QuadSols) (a b : ℚ) : (PlusU1 n).QuadSols :=
  linearToQuad (a • S.1 + b • (Y n).1.1) (add_quad S a b)

lemma addQuad_zero (S : (PlusU1 n).QuadSols) (a : ℚ): addQuad S a 0 = a • S := by
  simp [addQuad, linearToQuad]
  rfl

lemma on_cubeTriLin (S : (PlusU1 n).charges) :
    cubeTriLin (Y n).val (Y n).val S =  6 * accYY S := by
  erw [familyUniversal_cubeTriLin']
  rw [accYY_decomp]
  simp only [Fin.isValue, Y₁_val, mul_one, SMνSpecies_numberCharges, toSpecies_apply, mul_neg,
    neg_mul, neg_neg, mul_zero, zero_mul, add_zero]
  ring

lemma on_cubeTriLin_AFL (S : (PlusU1 n).LinSols) :
    cubeTriLin (Y n).val (Y n).val S.val = 0 := by
  rw [on_cubeTriLin]
  rw [YYsol S]
  simp

lemma on_cubeTriLin' (S : (PlusU1 n).charges) :
    cubeTriLin (Y n).val S S =  6 * accQuad S := by
  erw [familyUniversal_cubeTriLin]
  rw [accQuad_decomp]
  simp only [Fin.isValue, Y₁_val, mul_one, SMνSpecies_numberCharges, toSpecies_apply, mul_neg,
    neg_mul, zero_mul, add_zero]
  ring_nf

lemma on_cubeTriLin'_ALQ (S : (PlusU1 n).QuadSols) :
    cubeTriLin (Y n).val S.val S.val = 0 := by
  rw [on_cubeTriLin']
  rw [quadSol S]
  simp

lemma add_AFL_cube (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accCube (a • S.val + b • (Y n).val) =
    a ^ 2 * (a * accCube S.val + 3 * b * cubeTriLin S.val S.val (Y n).val) := by
  erw [TriLinearSymm.toCubic_add, cubeSol (b • (Y n)), accCube.map_smul]
  repeat rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  rw [on_cubeTriLin_AFL]
  simp only [HomogeneousCubic, accCube, TriLinearSymm.toCubic_apply, Fin.isValue,
    add_zero, Y_val, mul_zero]
  ring

lemma add_AFQ_cube (S : (PlusU1 n).QuadSols) (a b : ℚ) :
    accCube (a • S.val + b • (Y n).val) = a ^ 3 *  accCube S.val := by
  rw [add_AFL_cube]
  rw [cubeTriLin.swap₃]
  rw [on_cubeTriLin'_ALQ]
  ring

lemma add_AF_cube (S : (PlusU1 n).Sols) (a b : ℚ) :
    accCube (a • S.val + b • (Y n).val) = 0 := by
  rw [add_AFQ_cube]
  rw [cubeSol S]
  simp

/-- The `Sol` obtained by adding hypercharge to a `Sol`. -/
def addCube (S : (PlusU1 n).Sols) (a b : ℚ) : (PlusU1 n).Sols :=
  quadToAF (addQuad S.1 a b) (add_AF_cube S a b)


end Y
end PlusU1
end SMRHN
