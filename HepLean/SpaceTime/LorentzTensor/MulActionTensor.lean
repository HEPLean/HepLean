/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Basic
import Mathlib.RepresentationTheory.Basic
/-!

# Group actions on tensor structures

-/

noncomputable section

open TensorProduct

variable {R : Type} [CommSemiring R]

/-! TODO: Add preservation of the unit, and the metric. -/

/-- A multiplicative action on a tensor structure (e.g. the action of the Lorentz
  group on real Lorentz tensors). -/
class MulActionTensor (G : Type) [Monoid G] (𝓣 : TensorStructure R) where
  /-- For each color `μ` a representation of `G` on `ColorModule μ`. -/
  repColorModule : (μ : 𝓣.Color) → Representation R G (𝓣.ColorModule μ)
  /-- The contraction of a vector with its dual is invariant under the group action. -/
  contrDual_inv : ∀ μ g, 𝓣.contrDual μ ∘ₗ
    TensorProduct.map (repColorModule μ g) (repColorModule (𝓣.τ μ) g) = 𝓣.contrDual μ

namespace MulActionTensor

variable {G H : Type} [Group G] [Group H]

variable (𝓣 : TensorStructure R) [MulActionTensor G 𝓣]

variable {d : ℕ} {X Y Y' Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}

/-!

# Instances of `MulActionTensor`

-/

/-- The `MulActionTensor` defined by restriction along a group homomorphism. -/
def compHom (f : H →* G) : MulActionTensor H 𝓣 where
  repColorModule μ := MonoidHom.comp (repColorModule μ) f
  contrDual_inv μ h := by
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [contrDual_inv]

/-- The trivial `MulActionTensor` defined via trivial representations. -/
def trivial : MulActionTensor G 𝓣 where
  repColorModule μ := Representation.trivial R
  contrDual_inv μ g := by
    simp only [Representation.trivial, MonoidHom.one_apply, TensorProduct.map_one]
    rfl

end MulActionTensor

namespace TensorStructure
open TensorStructure
open MulActionTensor

variable {G : Type} [Group G]

variable (𝓣 : TensorStructure R) [MulActionTensor G 𝓣]

variable {d : ℕ} {X Y Y' Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}

/-!

## Representation of tensor products

-/

/-- The representation of the group `G` on the vector space of tensors. -/
def rep : Representation R G (𝓣.Tensor cX) where
  toFun g := PiTensorProduct.map (fun x => repColorModule (cX x) g)
  map_one' := by
    simp_all only [_root_.map_one, PiTensorProduct.map_one]
  map_mul' g g' := by
    simp_all only [_root_.map_mul]
    exact PiTensorProduct.map_mul _ _

local infixl:101 " • " => 𝓣.rep

lemma repColorModule_colorModuleCast_apply (h : μ = ν) (g : G) (x : 𝓣.ColorModule μ) :
    (repColorModule ν g) (𝓣.colorModuleCast h x) =
    (𝓣.colorModuleCast h) (repColorModule μ g x) := by
  subst h
  simp [colorModuleCast]

@[simp]
lemma repColorModule_colorModuleCast (h : μ = ν) (g : G) :
    (repColorModule ν g) ∘ₗ (𝓣.colorModuleCast h).toLinearMap =
    (𝓣.colorModuleCast h).toLinearMap ∘ₗ (repColorModule μ g) := by
  apply LinearMap.ext
  intro x
  simp [repColorModule_colorModuleCast_apply]

@[simp]
lemma rep_mapIso (e : X ≃ Y) (h : cX = cY ∘ e) (g : G) :
    (𝓣.rep g) ∘ₗ (𝓣.mapIso e h).toLinearMap = (𝓣.mapIso e h).toLinearMap ∘ₗ 𝓣.rep g := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  erw [mapIso_tprod]
  simp [rep, repColorModule_colorModuleCast_apply]
  change (PiTensorProduct.map fun x => (repColorModule (cY x)) g)
    ((PiTensorProduct.tprod R) fun i => (𝓣.colorModuleCast _) (x (e.symm i))) =
    (𝓣.mapIso e h) ((PiTensorProduct.map _) ((PiTensorProduct.tprod R) x))
  rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, mapIso_tprod]
  apply congrArg
  funext i
  subst h
  simp [repColorModule_colorModuleCast_apply]

@[simp]
lemma rep_mapIso_apply (e : X ≃ Y) (h : cX = cY ∘ e) (g : G) (x : 𝓣.Tensor cX) :
    (𝓣.mapIso e h) (g • x) = g • (𝓣.mapIso e h x) := by
  trans ((𝓣.rep g) ∘ₗ (𝓣.mapIso e h).toLinearMap) x
  simp
  rfl

@[simp]
lemma rep_tprod (g : G) (f : (i : X) → 𝓣.ColorModule (cX i)) :
    g • (PiTensorProduct.tprod R f) = PiTensorProduct.tprod R (fun x =>
    repColorModule (cX x) g (f x)) := by
  simp [rep]
  change (PiTensorProduct.map _) ((PiTensorProduct.tprod R) f) = _
  rw [PiTensorProduct.map_tprod]

/-!

## Group acting on tensor products

-/

lemma rep_tensoratorEquiv (g : G) :
    (𝓣.tensoratorEquiv cX cY) ∘ₗ (TensorProduct.map (𝓣.rep g) (𝓣.rep g)) = 𝓣.rep g ∘ₗ
    (𝓣.tensoratorEquiv cX cY).toLinearMap := by
  apply tensorProd_piTensorProd_ext
  intro p q
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_tmul, rep_tprod,
    tensoratorEquiv_tmul_tprod]
  apply congrArg
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

lemma rep_tensoratorEquiv_apply (g : G) (x : 𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY) :
    (𝓣.tensoratorEquiv cX cY) ((TensorProduct.map (𝓣.rep g) (𝓣.rep g)) x)
    = (𝓣.rep g) ((𝓣.tensoratorEquiv cX cY) x) := by
  trans ((𝓣.tensoratorEquiv cX cY) ∘ₗ (TensorProduct.map (𝓣.rep g) (𝓣.rep g))) x
  rfl
  rw [rep_tensoratorEquiv]
  rfl

lemma rep_tensoratorEquiv_tmul (g : G) (x : 𝓣.Tensor cX) (y : 𝓣.Tensor cY) :
    (𝓣.tensoratorEquiv cX cY) ((g • x) ⊗ₜ[R] (g • y)) =
    g • ((𝓣.tensoratorEquiv cX cY) (x ⊗ₜ[R] y)) := by
  nth_rewrite 1 [← rep_tensoratorEquiv_apply]
  rfl

lemma rep_tensoratorEquiv_symm (g : G) :
    (𝓣.tensoratorEquiv cX cY).symm ∘ₗ 𝓣.rep g = (TensorProduct.map (𝓣.rep g) (𝓣.rep g)) ∘ₗ
    (𝓣.tensoratorEquiv cX cY).symm.toLinearMap := by
  rw [LinearEquiv.eq_comp_toLinearMap_symm, LinearMap.comp_assoc,
    LinearEquiv.toLinearMap_symm_comp_eq]
  exact Eq.symm (rep_tensoratorEquiv 𝓣 g)

@[simp]
lemma rep_tensoratorEquiv_symm_apply (g : G) (x : 𝓣.Tensor (Sum.elim cX cY)) :
    (𝓣.tensoratorEquiv cX cY).symm ((𝓣.rep g) x) =
    (TensorProduct.map (𝓣.rep g) (𝓣.rep g)) ((𝓣.tensoratorEquiv cX cY).symm x) := by
  trans ((𝓣.tensoratorEquiv cX cY).symm ∘ₗ 𝓣.rep g) x
  rfl
  rw [rep_tensoratorEquiv_symm]
  rfl

@[simp]
lemma rep_lid (g : G) : TensorProduct.lid R (𝓣.Tensor cX) ∘ₗ
    (TensorProduct.map (LinearMap.id) (𝓣.rep g)) = (𝓣.rep g) ∘ₗ
    (TensorProduct.lid R (𝓣.Tensor cX)).toLinearMap := by
  apply TensorProduct.ext'
  intro r y
  simp

@[simp]
lemma rep_lid_apply (g : G) (x : R ⊗[R] 𝓣.Tensor cX) :
    (TensorProduct.lid R (𝓣.Tensor cX)) ((TensorProduct.map (LinearMap.id) (𝓣.rep g)) x) =
    (𝓣.rep g) ((TensorProduct.lid R (𝓣.Tensor cX)).toLinearMap x) := by
  trans ((TensorProduct.lid R (𝓣.Tensor cX)) ∘ₗ (TensorProduct.map (LinearMap.id) (𝓣.rep g))) x
  rfl
  rw [rep_lid]
  rfl

end TensorStructure

end
