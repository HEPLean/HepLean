/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Informal
import HepLean.SpaceTime.SL2C.Basic
import Mathlib.RepresentationTheory.Rep
import HepLean.Tensors.Basic
import Mathlib.Logic.Equiv.TransferInstance
/-!

## Modules associated with Lorentz vectors

These have not yet been fully-implmented.

We define these modules to prevent casting between different types of Lorentz vectors.

-/

namespace Lorentz

noncomputable section
open Matrix
open MatrixGroups
open Complex

structure ContrℂModule where
  val : Fin 1 ⊕ Fin 3 → ℂ

namespace ContrℂModule

/-- The equivalence between `ContrℂModule` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
def toFin13ℂFun : ContrℂModule ≃ (Fin 1 ⊕ Fin 3 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `ContrℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommMonoid ContrℂModule := Equiv.addCommMonoid toFin13ℂFun

/-- The instance of `AddCommGroup` on `ContrℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommGroup ContrℂModule := Equiv.addCommGroup toFin13ℂFun

/-- The instance of `Module` on `ContrℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : Module ℂ ContrℂModule := Equiv.module ℂ toFin13ℂFun

/-- The linear equivalence between `ContrℂModule` and `(Fin 1 ⊕ Fin 3 → ℂ)`. -/
@[simps!]
def toFin13ℂEquiv : ContrℂModule ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) where
  toFun := toFin13ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin13ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 1 ⊕ Fin 3 → ℂ` of a element in `ContrℂModule` defined
  through the linear equivalence `toFin13ℂEquiv`. -/
abbrev toFin13ℂ (ψ : ContrℂModule) := toFin13ℂEquiv ψ

/-- The representation of the Lorentz group on `ContrℂModule`. -/
def lorentzGroupRep : Representation ℂ (LorentzGroup 3) ContrℂModule where
  toFun M := {
      toFun := fun v => toFin13ℂEquiv.symm ((M.1.map ofReal) *ᵥ v.toFin13ℂ),
      map_add' := by
        intro ψ ψ'
        simp [mulVec_add]
      map_smul' := by
        intro r ψ
        simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' M N := by
    ext i
    simp

/-- The representation of the SL(2, ℂ) on `ContrℂModule` induced by the representation of the
  Lorentz group. -/
def SL2CRep : Representation ℂ SL(2, ℂ) ContrℂModule :=
  MonoidHom.comp lorentzGroupRep SpaceTime.SL2C.toLorentzGroup

end ContrℂModule

structure CoℂModule where
  val : Fin 1 ⊕ Fin 3 → ℂ

namespace CoℂModule

/-- The equivalence between `CoℂModule` and `Fin 1 ⊕ Fin 3 → ℂ`. -/
def toFin13ℂFun : CoℂModule ≃ (Fin 1 ⊕ Fin 3 → ℂ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `CoℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommMonoid CoℂModule := Equiv.addCommMonoid toFin13ℂFun

/-- The instance of `AddCommGroup` on `CoℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : AddCommGroup CoℂModule := Equiv.addCommGroup toFin13ℂFun

/-- The instance of `Module` on `CoℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin 3 → ℂ`. -/
instance : Module ℂ CoℂModule := Equiv.module ℂ toFin13ℂFun

/-- The linear equivalence between `CoℂModule` and `(Fin 1 ⊕ Fin 3 → ℂ)`. -/
@[simps!]
def toFin13ℂEquiv : CoℂModule ≃ₗ[ℂ] (Fin 1 ⊕ Fin 3 → ℂ) where
  toFun := toFin13ℂFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin13ℂFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 1 ⊕ Fin 3 → ℂ` of a element in `CoℂModule` defined
  through the linear equivalence `toFin13ℂEquiv`. -/
abbrev toFin13ℂ (ψ : CoℂModule) := toFin13ℂEquiv ψ

/-- The representation of the Lorentz group on `CoℂModule`. -/
def lorentzGroupRep : Representation ℂ (LorentzGroup 3) CoℂModule where
  toFun M := {
      toFun := fun v => toFin13ℂEquiv.symm ((M.1.map ofReal)⁻¹ᵀ *ᵥ v.toFin13ℂ),
      map_add' := by
        intro ψ ψ'
        simp [mulVec_add]
      map_smul' := by
        intro r ψ
        simp [mulVec_smul]}
  map_one' := by
    ext i
    simp
  map_mul' M N := by
    ext1 x
    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mul_apply,
      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
    refine (congrFun (congrArg _ ?_) _)
    simp only [lorentzGroupIsGroup_mul_coe, Matrix.map_mul]
    rw [Matrix.mul_inv_rev]
    exact transpose_mul _ _

/-- The representation of the SL(2, ℂ) on `ContrℂModule` induced by the representation of the
  Lorentz group. -/
def SL2CRep : Representation ℂ SL(2, ℂ) CoℂModule :=
  MonoidHom.comp lorentzGroupRep SpaceTime.SL2C.toLorentzGroup

end CoℂModule

end
end Lorentz
