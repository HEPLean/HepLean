/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.MSSMNu.Basic
/-!
# The definition of the solution Y₃ and properties thereof

We define $Y_3$ and show that it is a double point of the cubic.

# References

The main reference for the material in this file is:

- https://arxiv.org/pdf/2107.07926.pdf

-/

universe v u

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

/-- $Y_3$ is the charge which is hypercharge in all families, but with the third
family of the opposite sign. -/
def Y₃AsCharge : MSSMACC.charges := toSpecies.symm
  ⟨fun s => fun i =>
    match s, i with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => - 1
    | 1, 0 => -4
    | 1, 1 => -4
    | 1, 2 => 4
    | 2, 0 => 2
    | 2, 1 => 2
    | 2, 2 => - 2
    | 3, 0 => -3
    | 3, 1 => -3
    | 3, 2 => 3
    | 4, 0 => 6
    | 4, 1 => 6
    | 4, 2 => - 6
    | 5, 0 => 0
    | 5, 1 => 0
    | 5, 2 => 0,
  fun s =>
    match s with
    | 0 => -3
    | 1 => 3⟩

/-- $Y_3$ as a solution. -/
def Y₃ : MSSMACC.Sols :=
  MSSMACC.AnomalyFreeMk Y₃AsCharge (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

lemma Y₃_val : Y₃.val = Y₃AsCharge := by
  rfl

lemma doublePoint_Y₃_Y₃ (R : MSSMACC.LinSols) :
    cubeTriLin (Y₃.val, Y₃.val, R.val) = 0 := by
  rw [← TriLinearSymm.toFun_eq_coe]
  simp only [cubeTriLin, cubeTriLinToFun, MSSMSpecies_numberCharges]
  rw [Fin.sum_univ_three]
  rw [Y₃_val]
  rw [Y₃AsCharge]
  repeat rw [toSMSpecies_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv]
  simp
  have hLin := R.linearSol
  simp at hLin
  have h3 := hLin 3
  simp [Fin.sum_univ_three] at h3
  linear_combination 6 * h3

end MSSMACC
