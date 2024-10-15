/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.WeylFermion.Basic
import HepLean.SpaceTime.WeylFermion.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Matrix
/-!

# Tensor product of two Weyl fermion

-/

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-!

## Equivalences to matrices.

-/

/-- Equivalence of `leftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def leftLeftToMatrix : (leftHanded ⊗ leftHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis leftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Equivalence of `altLeftHanded ⊗ altLeftHanded` to `2 x 2` complex matrices. -/
def altLeftaltLeftToMatrix : (altLeftHanded ⊗ altLeftHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct altLeftBasis altLeftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Equivalence of `leftHanded ⊗ altLeftHanded` to `2 x 2` complex matrices. -/
def leftAltLeftToMatrix : (leftHanded ⊗ altLeftHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct leftBasis altLeftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Equivalence of `altLeftHanded ⊗ leftHanded` to `2 x 2` complex matrices. -/
def altLeftLeftToMatrix : (altLeftHanded ⊗ leftHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct altLeftBasis leftBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Equivalence of `rightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def rightRightToMatrix : (rightHanded ⊗ rightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct rightBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Equivalence of `altRightHanded ⊗ altRightHanded` to `2 x 2` complex matrices. -/
def altRightAltRightToMatrix : (altRightHanded ⊗ altRightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct altRightBasis altRightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Equivalence of `rightHanded ⊗ altRightHanded` to `2 x 2` complex matrices. -/
def rightAltRightToMatrix : (rightHanded ⊗ altRightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct rightBasis altRightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-- Equivalence of `altRightHanded ⊗ rightHanded` to `2 x 2` complex matrices. -/
def altRightRightToMatrix : (altRightHanded ⊗ rightHanded).V ≃ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (Basis.tensorProduct altRightBasis rightBasis).repr ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) ≪≫ₗ
  LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)

/-!

## Group actions

-/

/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ leftHanded` is equivalent to
  `M.1 * leftLeftToMatrix v * (M.1)ᵀ`. -/
lemma leftLeftToMatrix_ρ (v : (leftHanded ⊗ leftHanded).V) (M : SL(2,ℂ)) :
    leftLeftToMatrix (TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M) v) =
    M.1 * leftLeftToMatrix v * (M.1)ᵀ := by
  nth_rewrite 1 [leftLeftToMatrix]
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (leftBasis.tensorProduct leftBasis) (leftBasis.tensorProduct leftBasis)
      (TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((leftBasis.tensorProduct leftBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (leftBasis.tensorProduct leftBasis)
      (leftBasis.tensorProduct leftBasis) (TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M))
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M)) (i, j) k)
        * leftLeftToMatrix v k.1 k.2) = _
  erw [Finset.sum_product]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ j : Fin 2, M.1 i j * leftLeftToMatrix v j x) * M.1 j x
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftLeftToMatrix v x1 x) * M.1 j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [leftBasis_ρ_apply, Finsupp.linearEquivFunOnFinite_apply,
    Action.instMonoidalCategory_tensorObj_V]
  rw [mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [← mul_assoc]

/-- The group action of `SL(2,ℂ)` on `altLeftHanded ⊗ altLeftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftLeftToMatrix v * (M.1⁻¹)`. -/
lemma altLeftaltLeftToMatrix_ρ (v : (altLeftHanded ⊗ altLeftHanded).V) (M : SL(2,ℂ)) :
    altLeftaltLeftToMatrix (TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M) v) =
    (M.1⁻¹)ᵀ * altLeftaltLeftToMatrix v * (M.1⁻¹) := by
  nth_rewrite 1 [altLeftaltLeftToMatrix]
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (altLeftBasis.tensorProduct altLeftBasis) (altLeftBasis.tensorProduct altLeftBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((altLeftBasis.tensorProduct altLeftBasis).repr v)))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (altLeftBasis.tensorProduct altLeftBasis)
      (altLeftBasis.tensorProduct altLeftBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M))
        ((LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M)) (i, j) k)
        * altLeftaltLeftToMatrix v k.1 k.2) = _
  erw [Finset.sum_product]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i * altLeftaltLeftToMatrix v x1 x) * (M.1)⁻¹ x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, ((M.1)⁻¹ x1 i * altLeftaltLeftToMatrix v x1 x) * (M.1)⁻¹ x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [altLeftBasis_ρ_apply, transpose_apply, Action.instMonoidalCategory_tensorObj_V]
  ring

/-- The group action of `SL(2,ℂ)` on `leftHanded ⊗ altLeftHanded` is equivalent to
  `M.1 * leftAltLeftToMatrix v * (M.1⁻¹)`. -/
lemma leftAltLeftToMatrix_ρ (v : (leftHanded ⊗ altLeftHanded).V) (M : SL(2,ℂ)) :
    leftAltLeftToMatrix (TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M) v) =
    M.1 * leftAltLeftToMatrix v * (M.1⁻¹) := by
  nth_rewrite 1 [leftAltLeftToMatrix]
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (leftBasis.tensorProduct altLeftBasis) (leftBasis.tensorProduct altLeftBasis)
      (TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((leftBasis.tensorProduct altLeftBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (leftBasis.tensorProduct altLeftBasis)
      (leftBasis.tensorProduct altLeftBasis)
      (TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M))
        ((LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M)) (i, j) k)
        * leftAltLeftToMatrix v k.1 k.2) = _
  erw [Finset.sum_product]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, M.1 i x1 * leftAltLeftToMatrix v x1 x) * (M.1⁻¹) x j
    = ∑ x : Fin 2, ∑ x1 : Fin 2, (M.1 i x1 * leftAltLeftToMatrix v x1 x) * (M.1⁻¹) x j := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [leftBasis_ρ_apply, altLeftBasis_ρ_apply, transpose_apply,
    Action.instMonoidalCategory_tensorObj_V]
  ring

/-- The group action of `SL(2,ℂ)` on `altLeftHanded ⊗ leftHanded` is equivalent to
  `(M.1⁻¹)ᵀ * leftAltLeftToMatrix v * (M.1)ᵀ`. -/
lemma altLeftLeftToMatrix_ρ (v : (altLeftHanded ⊗ leftHanded).V) (M : SL(2,ℂ)) :
    altLeftLeftToMatrix (TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M) v) =
    (M.1⁻¹)ᵀ * altLeftLeftToMatrix v * (M.1)ᵀ := by
  nth_rewrite 1 [altLeftLeftToMatrix]
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (altLeftBasis.tensorProduct leftBasis) (altLeftBasis.tensorProduct leftBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((altLeftBasis.tensorProduct leftBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (altLeftBasis.tensorProduct leftBasis)
      (altLeftBasis.tensorProduct leftBasis)
      (TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix altLeftBasis altLeftBasis) (altLeftHanded.ρ M))
        ((LinearMap.toMatrix leftBasis leftBasis) (leftHanded.ρ M)) (i, j) k)
        * altLeftLeftToMatrix v k.1 k.2) = _
  erw [Finset.sum_product]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1)⁻¹ x1 i * altLeftLeftToMatrix v x1 x) * M.1 j x
    = ∑ x : Fin 2, ∑ x1 : Fin 2, ((M.1)⁻¹ x1 i * altLeftLeftToMatrix v x1 x) * M.1 j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [altLeftBasis_ρ_apply, leftBasis_ρ_apply, transpose_apply,
    Action.instMonoidalCategory_tensorObj_V]
  ring

/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ rightHanded` is equivalent to
  `(M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ`. -/
lemma rightRightToMatrix_ρ (v : (rightHanded ⊗ rightHanded).V) (M : SL(2,ℂ)) :
    rightRightToMatrix (TensorProduct.map (rightHanded.ρ M) (rightHanded.ρ M) v) =
    (M.1.map star) * rightRightToMatrix v * ((M.1.map star))ᵀ := by
  nth_rewrite 1 [rightRightToMatrix]
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (rightBasis.tensorProduct rightBasis) (rightBasis.tensorProduct rightBasis)
      (TensorProduct.map (rightHanded.ρ M) (rightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((rightBasis.tensorProduct rightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (rightBasis.tensorProduct rightBasis)
      (rightBasis.tensorProduct rightBasis)
      (TensorProduct.map (rightHanded.ρ M) (rightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M))
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M)) (i, j) k)
        * rightRightToMatrix v k.1 k.2) = _
  erw [Finset.sum_product]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1.map star) i x1 * rightRightToMatrix v x1 x) *
      (M.1.map star) j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1.map star) i x1 * rightRightToMatrix v x1 x) * (M.1.map star) j x:= by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [rightBasis_ρ_apply, Finsupp.linearEquivFunOnFinite_apply,
    Action.instMonoidalCategory_tensorObj_V]
  ring

/-- The group action of `SL(2,ℂ)` on `altRightHanded ⊗ altRightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma altRightAltRightToMatrix_ρ (v : (altRightHanded ⊗ altRightHanded).V) (M : SL(2,ℂ)) :
    altRightAltRightToMatrix (TensorProduct.map (altRightHanded.ρ M) (altRightHanded.ρ M) v) =
    ((M.1⁻¹).conjTranspose) * altRightAltRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  nth_rewrite 1 [altRightAltRightToMatrix]
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (altRightBasis.tensorProduct altRightBasis) (altRightBasis.tensorProduct altRightBasis)
      (TensorProduct.map (altRightHanded.ρ M) (altRightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((altRightBasis.tensorProduct altRightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (altRightBasis.tensorProduct altRightBasis)
      (altRightBasis.tensorProduct altRightBasis)
      (TensorProduct.map (altRightHanded.ρ M) (altRightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M))
        ((LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M)) (i, j) k)
        * altRightAltRightToMatrix v k.1 k.2) = _
  erw [Finset.sum_product]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (↑M)⁻¹ᴴ i x1 * altRightAltRightToMatrix v x1 x) *
      (↑M)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((↑M)⁻¹ᴴ i x1 * altRightAltRightToMatrix v x1 x) * (↑M)⁻¹ᴴ j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [altRightBasis_ρ_apply, transpose_apply, Action.instMonoidalCategory_tensorObj_V]
  ring

/-- The group action of `SL(2,ℂ)` on `rightHanded ⊗ altRightHanded` is equivalent to
  `(M.1.map star) * rightAltRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ`. -/
lemma rightAltRightToMatrix_ρ (v : (rightHanded ⊗ altRightHanded).V) (M : SL(2,ℂ)) :
    rightAltRightToMatrix (TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M) v) =
    (M.1.map star) * rightAltRightToMatrix v * (((M.1⁻¹).conjTranspose)ᵀ) := by
  nth_rewrite 1 [rightAltRightToMatrix]
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (rightBasis.tensorProduct altRightBasis) (rightBasis.tensorProduct altRightBasis)
      (TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((rightBasis.tensorProduct altRightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (rightBasis.tensorProduct altRightBasis)
    (rightBasis.tensorProduct altRightBasis)
    (TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M))
        ((LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M)) (i, j) k)
        * rightAltRightToMatrix v k.1 k.2) = _
  erw [Finset.sum_product]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2, (M.1.map star) i x1 * rightAltRightToMatrix v x1 x)
      * (↑M)⁻¹ᴴ j x = ∑ x : Fin 2, ∑ x1 : Fin 2,
      ((M.1.map star) i x1 * rightAltRightToMatrix v x1 x) * (↑M)⁻¹ᴴ j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [rightBasis_ρ_apply, altRightBasis_ρ_apply, transpose_apply,
    Action.instMonoidalCategory_tensorObj_V]
  ring

/-- The group action of `SL(2,ℂ)` on `altRightHanded ⊗ rightHanded` is equivalent to
  `((M.1⁻¹).conjTranspose * rightAltRightToMatrix v * ((M.1.map star)).ᵀ`. -/
lemma altRightRightToMatrix_ρ (v : (altRightHanded ⊗ rightHanded).V) (M : SL(2,ℂ)) :
    altRightRightToMatrix (TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M) v) =
    ((M.1⁻¹).conjTranspose) * altRightRightToMatrix v * (M.1.map star)ᵀ := by
  nth_rewrite 1 [altRightRightToMatrix]
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.trans_apply]
  trans (LinearEquiv.curry ℂ ℂ (Fin 2) (Fin 2)) ((LinearMap.toMatrix
      (altRightBasis.tensorProduct rightBasis) (altRightBasis.tensorProduct rightBasis)
      (TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M)))
      *ᵥ ((Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2))
      ((altRightBasis.tensorProduct rightBasis).repr (v))))
  · apply congrArg
    have h1 := (LinearMap.toMatrix_mulVec_repr (altRightBasis.tensorProduct rightBasis)
      (altRightBasis.tensorProduct rightBasis)
      (TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M)) v)
    erw [h1]
    rfl
  rw [TensorProduct.toMatrix_map]
  funext i j
  change ∑ k, ((kroneckerMap (fun x1 x2 => x1 * x2)
        ((LinearMap.toMatrix altRightBasis altRightBasis) (altRightHanded.ρ M))
        ((LinearMap.toMatrix rightBasis rightBasis) (rightHanded.ρ M)) (i, j) k)
        * altRightRightToMatrix v k.1 k.2) = _
  erw [Finset.sum_product]
  simp_rw [kroneckerMap_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have h1 : ∑ x : Fin 2, (∑ x1 : Fin 2,
      (↑M)⁻¹ᴴ i x1 * altRightRightToMatrix v x1 x) * (M.1.map star) j x
      = ∑ x : Fin 2, ∑ x1 : Fin 2, ((↑M)⁻¹ᴴ i x1 * altRightRightToMatrix v x1 x) *
      (M.1.map star) j x := by
    congr
    funext x
    rw [Finset.sum_mul]
  erw [h1]
  rw [Finset.sum_comm]
  congr
  funext x
  congr
  funext x1
  simp only [altRightBasis_ρ_apply, rightBasis_ρ_apply, transpose_apply,
    Action.instMonoidalCategory_tensorObj_V]
  ring

/-!

## The symm version of the group actions.

-/

lemma leftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHanded.ρ M) (leftHanded.ρ M) (leftLeftToMatrix.symm v) =
    leftLeftToMatrix.symm (M.1 * v * (M.1)ᵀ) := by
  have h1 := leftLeftToMatrix_ρ (leftLeftToMatrix.symm v) M
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma altLeftaltLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (altLeftHanded.ρ M) (altLeftHanded.ρ M) (altLeftaltLeftToMatrix.symm v) =
    altLeftaltLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1⁻¹)) := by
  have h1 := altLeftaltLeftToMatrix_ρ (altLeftaltLeftToMatrix.symm v) M
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma leftAltLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M) (leftAltLeftToMatrix.symm v) =
    leftAltLeftToMatrix.symm (M.1 * v * (M.1⁻¹)) := by
  have h1 := leftAltLeftToMatrix_ρ (leftAltLeftToMatrix.symm v) M
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma altLeftLeftToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M) (altLeftLeftToMatrix.symm v) =
    altLeftLeftToMatrix.symm ((M.1⁻¹)ᵀ * v * (M.1)ᵀ) := by
  have h1 := altLeftLeftToMatrix_ρ (altLeftLeftToMatrix.symm v) M
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma rightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (rightHanded.ρ M) (rightHanded.ρ M) (rightRightToMatrix.symm v) =
    rightRightToMatrix.symm ((M.1.map star) * v * ((M.1.map star))ᵀ) := by
  have h1 := rightRightToMatrix_ρ (rightRightToMatrix.symm v) M
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma altRightAltRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (altRightHanded.ρ M) (altRightHanded.ρ M) (altRightAltRightToMatrix.symm v) =
    altRightAltRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * ((M.1⁻¹).conjTranspose)ᵀ) := by
  have h1 := altRightAltRightToMatrix_ρ (altRightAltRightToMatrix.symm v) M
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma rightAltRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M) (rightAltRightToMatrix.symm v) =
    rightAltRightToMatrix.symm ((M.1.map star) * v * (((M.1⁻¹).conjTranspose)ᵀ)) := by
  have h1 := rightAltRightToMatrix_ρ (rightAltRightToMatrix.symm v) M
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

lemma altRightRightToMatrix_ρ_symm (v : Matrix (Fin 2) (Fin 2) ℂ) (M : SL(2,ℂ)) :
    TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M) (altRightRightToMatrix.symm v) =
    altRightRightToMatrix.symm (((M.1⁻¹).conjTranspose) * v * (M.1.map star)ᵀ) := by
  have h1 := altRightRightToMatrix_ρ (altRightRightToMatrix.symm v) M
  simp only [Action.instMonoidalCategory_tensorObj_V, LinearEquiv.apply_symm_apply] at h1
  rw [← h1]
  simp

end
end Fermion
