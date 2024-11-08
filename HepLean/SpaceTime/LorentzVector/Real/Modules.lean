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

These definitions are preludes to the definitions of
`Lorentz.contr` and `Lorentz.co`.

-/

namespace Lorentz

noncomputable section
open Matrix
open MatrixGroups
open Complex

/-- The module for contravariant (up-index) real Lorentz vectors. -/
structure ContrMod (d : ℕ) where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin d → ℝ`. -/
  val : Fin 1 ⊕ Fin d → ℝ

namespace ContrMod

variable {d : ℕ}

/-- The equivalence between `ContrℝModule` and `Fin 1 ⊕ Fin d → ℂ`. -/
def toFin1dℝFun : ContrMod d ≃ (Fin 1 ⊕ Fin d → ℝ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `ContrℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommMonoid (ContrMod d) := Equiv.addCommMonoid toFin1dℝFun

/-- The instance of `AddCommGroup` on `ContrℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommGroup (ContrMod d) := Equiv.addCommGroup toFin1dℝFun

/-- The instance of `Module` on `ContrℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : Module ℝ (ContrMod d) := Equiv.module ℝ toFin1dℝFun

@[ext]
lemma ext (ψ ψ' : ContrMod d) (h : ψ.val = ψ'.val) : ψ = ψ' := by
  cases ψ
  cases ψ'
  subst h
  rfl

@[simp]
lemma val_add (ψ ψ' : ContrMod d) : (ψ + ψ').val = ψ.val + ψ'.val := rfl

@[simp]
lemma val_smul (r : ℝ) (ψ : ContrMod d) : (r • ψ).val = r • ψ.val := rfl

/-- The linear equivalence between `ContrℝModule` and `(Fin 1 ⊕ Fin d → ℝ)`. -/
@[simps!]
def toFin1dℝEquiv : ContrMod d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) :=
  Equiv.linearEquiv ℝ toFin1dℝFun

/-- The underlying element of `Fin 1 ⊕ Fin d → ℝ` of a element in `ContrℝModule` defined
  through the linear equivalence `toFin1dℝEquiv`. -/
abbrev toFin1dℝ (ψ : ContrMod d) := toFin1dℝEquiv ψ

/-- The standard basis of `ContrℝModule` indexed by `Fin 1 ⊕ Fin d`. -/
@[simps!]
def stdBasis : Basis (Fin 1 ⊕ Fin d) ℝ (ContrMod d) := Basis.ofEquivFun toFin1dℝEquiv

/-- The representation of the Lorentz group acting on `ContrℝModule d`. -/
def rep : Representation ℝ (LorentzGroup d) (ContrMod d) where
  toFun g := Matrix.toLinAlgEquiv stdBasis g
  map_one' := (MulEquivClass.map_eq_one_iff (Matrix.toLinAlgEquiv stdBasis)).mpr rfl
  map_mul' x y := by
    simp only [lorentzGroupIsGroup_mul_coe, _root_.map_mul]

end ContrMod

/-- The module for covariant (up-index) complex Lorentz vectors. -/
structure CoMod (d : ℕ) where
  /-- The underlying value as a vector `Fin 1 ⊕ Fin d → ℝ`. -/
  val : Fin 1 ⊕ Fin d → ℝ

namespace CoMod

variable {d : ℕ}

/-- The equivalence between `CoℝModule` and `Fin 1 ⊕ Fin d → ℝ`. -/
def toFin1dℝFun : CoMod d ≃ (Fin 1 ⊕ Fin d → ℝ) where
  toFun v := v.val
  invFun f := ⟨f⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The instance of `AddCommMonoid` on `CoℂModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommMonoid (CoMod d) := Equiv.addCommMonoid toFin1dℝFun

/-- The instance of `AddCommGroup` on `CoℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : AddCommGroup (CoMod d) := Equiv.addCommGroup toFin1dℝFun

/-- The instance of `Module` on `CoℝModule` defined via its equivalence
  with `Fin 1 ⊕ Fin d → ℝ`. -/
instance : Module ℝ (CoMod d) := Equiv.module ℝ toFin1dℝFun

/-- The linear equivalence between `CoℝModule` and `(Fin 1 ⊕ Fin d → ℝ)`. -/
@[simps!]
def toFin1dℝEquiv : CoMod d ≃ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) :=
  Equiv.linearEquiv ℝ toFin1dℝFun

/-- The underlying element of `Fin 1 ⊕ Fin d → ℝ` of a element in `CoℝModule` defined
  through the linear equivalence `toFin1dℝEquiv`. -/
abbrev toFin1dℝ (ψ : CoMod d) := toFin1dℝEquiv ψ

/-- The standard basis of `CoℝModule` indexed by `Fin 1 ⊕ Fin d`. -/
@[simps!]
def stdBasis : Basis (Fin 1 ⊕ Fin d) ℝ (CoMod d) := Basis.ofEquivFun toFin1dℝEquiv

/-- The representation of the Lorentz group acting on `CoℝModule d`. -/
def rep : Representation ℝ (LorentzGroup d) (CoMod d) where
  toFun g := Matrix.toLinAlgEquiv stdBasis (LorentzGroup.transpose g⁻¹)
  map_one' := by
    simp only [inv_one, LorentzGroup.transpose_one, lorentzGroupIsGroup_one_coe, _root_.map_one]
  map_mul' x y := by
    simp only [_root_.mul_inv_rev, lorentzGroupIsGroup_inv, LorentzGroup.transpose_mul,
      lorentzGroupIsGroup_mul_coe, _root_.map_mul]

end CoMod

end
end Lorentz
