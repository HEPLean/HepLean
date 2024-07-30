/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Basic
import HepLean.SpaceTime.LorentzTensor.MulActionTensor
/-!

# Lorentz tensors indexed by Fin n

In physics, in many (if not all) cases, we index our Lorentz tensors by `Fin n`.

In this file we set up the machinery to deal with Lorentz tensors indexed by `Fin n`
in a way that is convenient for physicists, and general caculation.

## Note

This file is currently a stub.

-/

open TensorProduct

noncomputable section

namespace TensorStructure

variable {n m : ℕ}

variable {R : Type} [CommSemiring R] (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color}
  {cW : W → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}
  {cn : Fin n → 𝓣.Color} {cm : Fin m → 𝓣.Color}

variable {G H : Type} [Group G] [Group H] [MulActionTensor G 𝓣]
local infixl:101 " • " => 𝓣.rep

open MulActionTensor

/-- Casting a tensor defined on `Fin n` to `Fin m` where `n = m`. -/
@[simp]
def finCast (h : n = m) (hc : cn = cm ∘ Fin.castOrderIso h) : 𝓣.Tensor cn ≃ₗ[R] 𝓣.Tensor cm :=
  𝓣.mapIso (Fin.castOrderIso h) hc

/-- An equivalence between `𝓣.Tensor cn ⊗[R] 𝓣.Tensor cm` indexed by `Fin n` and `Fin m`,
  and `𝓣.Tensor (Sum.elim cn cm ∘ finSumFinEquiv.symm)` indexed by `Fin (n + m)`. -/
@[simp]
def finSumEquiv : 𝓣.Tensor cn ⊗[R] 𝓣.Tensor cm ≃ₗ[R]
    𝓣.Tensor (Sum.elim cn cm ∘ finSumFinEquiv.symm) :=
  (𝓣.tensoratorEquiv cn cm).trans (𝓣.mapIso finSumFinEquiv (by funext a; simp))

/-!

## Vectors as tensors & singletons

-/

/-- Tensors on `Fin 1` are equivalent to a constant Pi tensor product. -/
def tensorSingeletonEquiv : 𝓣.Tensor ![μ] ≃ₗ[R] ⨂[R] _ : (Fin 1), 𝓣.ColorModule μ := by
  refine LinearEquiv.ofLinear (PiTensorProduct.map (fun i =>
      match i with
      | 0 => LinearMap.id)) (PiTensorProduct.map (fun i =>
    match i with
    | 0 => LinearMap.id)) ?_ ?_
  all_goals
    apply LinearMap.ext
    refine fun x ↦
      PiTensorProduct.induction_on' x ?_ (by
        intro a b hx a
        simp_all only [Nat.succ_eq_add_one, Matrix.cons_val_zero, LinearMap.coe_comp,
          Function.comp_apply, LinearMap.id_coe, id_eq, map_add])
    intro r x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
      PiTensorProduct.tprodCoeff_eq_smul_tprod, LinearMapClass.map_smul, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.id_coe, id_eq]
    change r •
      (PiTensorProduct.map _) ((PiTensorProduct.map _) ((PiTensorProduct.tprod R) x)) = _
    rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
    repeat apply congrArg
    funext i
    fin_cases i
    rfl

/-- An equivalence between the `ColorModule` for a color and a `Fin 1` tensor with that color. -/
def vecAsTensor : 𝓣.ColorModule μ ≃ₗ[R] 𝓣.Tensor ![μ] :=
  ((PiTensorProduct.subsingletonEquiv 0).symm : _ ≃ₗ[R] ⨂[R] _ : (Fin 1), 𝓣.ColorModule μ)
    ≪≫ₗ 𝓣.tensorSingeletonEquiv.symm

/-- The equivalence `vecAsTensor` is equivariant with respect to `MulActionTensor`-actions. -/
@[simp]
lemma vecAsTensor_equivariant (g : G) (v : 𝓣.ColorModule μ) :
    𝓣.vecAsTensor (repColorModule μ g v) = g • 𝓣.vecAsTensor v := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, vecAsTensor, Fin.isValue, tensorSingeletonEquiv,
    Matrix.cons_val_zero, LinearEquiv.trans_apply, PiTensorProduct.subsingletonEquiv_symm_apply,
    LinearEquiv.ofLinear_symm_apply]
  change (PiTensorProduct.map _) ((PiTensorProduct.tprod R) _) =
    (𝓣.rep g) ((PiTensorProduct.map _) ((PiTensorProduct.tprod R) fun _ => v))
  rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, rep_tprod]
  apply congrArg
  funext i
  fin_cases i
  rfl

end TensorStructure

end
