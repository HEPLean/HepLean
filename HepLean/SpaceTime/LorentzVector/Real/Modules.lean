/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Informal
import HepLean.SpaceTime.SL2C.Basic
import Mathlib.RepresentationTheory.Rep
import Mathlib.Logic.Equiv.TransferInstance
/-!

## Modules associated with Real Lorentz vectors

We define the modules underlying real Lorentz vectors.

-/

namespace Lorentz

noncomputable section
open Matrix
open MatrixGroups
open Complex

/-- The module for contravariant (up-index) real Lorentz vectors. -/
structure ContrℝModule (d : ℕ) where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin d → ℝ`. -/
  val : Fin 1 ⊕ Fin d → ℝ

namespace ContrℝModule

variable {d : ℕ}

/-- The equivalence between `ContrℝModule` and `Fin 1 ⊕ Fin d → ℂ`. -/
def toFin1dℝFun : ContrℝModule d  ≃ (Fin 1 ⊕ Fin d → ℝ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `ContrℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommMonoid (ContrℝModule d) := Equiv.addCommMonoid toFin1dℝFun

/-- The instance of `AddCommGroup` on `ContrℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommGroup (ContrℝModule d) := Equiv.addCommGroup toFin1dℝFun

/-- The instance of `Module` on `ContrℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : Module ℝ (ContrℝModule d) := Equiv.module ℝ toFin1dℝFun

@[ext]
lemma ext (ψ ψ' : ContrℝModule d) (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl

@[simp]
lemma val_add (ψ ψ' : ContrℝModule d) : (ψ + ψ').val = ψ.val + ψ'.val := rfl

@[simp]
lemma val_smul (r : ℝ) (ψ : ContrℝModule d) : (r • ψ).val = r • ψ.val := rfl

/-- The linear equivalence between `ContrℝModule` and `(Fin 1 ⊕ Fin d → ℝ)`. -/
@[simps!]
def toFin1dℝEquiv : ContrℝModule d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) where
  toFun := toFin1dℝFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin1dℝFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 1 ⊕ Fin d → ℝ` of a element in `ContrℝModule` defined
  through the linear equivalence `toFin1dℝEquiv`. -/
abbrev toFin1dℝ (ψ : ContrℝModule d) := toFin1dℝEquiv ψ

end ContrℝModule

/-- The module for covariant (up-index) complex Lorentz vectors. -/
structure CoℝModule (d : ℕ) where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin d → ℝ`. -/
  val : Fin 1 ⊕ Fin d → ℝ

namespace CoℝModule

variable {d : ℕ}

/-- The equivalence between `CoℝModule` and `Fin 1 ⊕ Fin d → ℝ`. -/
def toFin1dℝFun : CoℝModule d ≃ (Fin 1 ⊕ Fin d → ℝ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `CoℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommMonoid (CoℝModule d) := Equiv.addCommMonoid toFin1dℝFun

/-- The instance of `AddCommGroup` on `CoℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommGroup (CoℝModule d) := Equiv.addCommGroup toFin1dℝFun

/-- The instance of `Module` on `CoℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : Module ℝ (CoℝModule d) := Equiv.module ℝ toFin1dℝFun

/-- The linear equivalence between `CoℝModule` and `(Fin 1 ⊕ Fin d → ℝ)`. -/
@[simps!]
def toFin1dℝEquiv : CoℝModule d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) where
  toFun := toFin1dℝFun
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  invFun := toFin1dℝFun.symm
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The underlying element of `Fin 1 ⊕ Fin d → ℝ` of a element in `CoℝModule` defined
  through the linear equivalence `toFin1dℝEquiv`. -/
abbrev toFin13ℂ (ψ : CoℝModule d) := toFin1dℝEquiv ψ

end CoℝModule

end
end Lorentz
