/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import HepLean.SpaceTime.LorentzGroup.Basic
import HepLean.Meta.Informal
import Mathlib.RepresentationTheory.Rep
import HepLean.SpaceTime.LorentzVector.Real.Modules
/-!

# Real Lorentz vectors

We define real Lorentz vectors in as representations of the Lorentz group.

-/

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

namespace Lorentz
open minkowskiMatrix
/-- The representation of `LorentzGroup d` on real vectors corresponding to contravariant
  Lorentz vectors. In index notation these have an up index `ψⁱ`. -/
def Contr (d : ℕ) : Rep ℝ (LorentzGroup d) := Rep.of ContrMod.rep

instance : TopologicalSpace (Contr d) :=
  haveI : NormedAddCommGroup (Contr d) := ContrMod.norm
  UniformSpace.toTopologicalSpace

/-- The representation of `LorentzGroup d` on real vectors corresponding to covariant
  Lorentz vectors. In index notation these have an up index `ψⁱ`. -/
def Co (d : ℕ) : Rep ℝ (LorentzGroup d) := Rep.of CoMod.rep

open CategoryTheory.MonoidalCategory

def toField (d : ℕ) : (𝟙_ (Rep ℝ ↑(LorentzGroup d))) →ₗ[ℝ] ℝ := LinearMap.id

/-!

## Isomorphism between contravariant and covariant Lorentz vectors

-/

/-- The morphism of representations from `Contr d` to `Co d` defined by multiplication
  with the metric. -/
def Contr.toCo (d : ℕ) : Contr d ⟶ Co d where
  hom := {
    toFun := fun ψ => CoMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ),
    map_add' := by
      intro ψ ψ'
      simp only [map_add, mulVec_add]
    map_smul' := by
      intro r ψ
      simp only [_root_.map_smul, mulVec_smul, RingHom.id_apply]}
  comm g := by
    ext ψ : 2
    simp only [ModuleCat.coe_comp, Function.comp_apply]
    conv_lhs =>
      change CoMod.toFin1dℝEquiv.symm (η *ᵥ (g.1 *ᵥ ψ.toFin1dℝ))
      rw [mulVec_mulVec, LorentzGroup.minkowskiMatrix_comm, ← mulVec_mulVec]
    rfl

/-- The morphism of representations from `Co d` to `Contr d` defined by multiplication
  with the metric. -/
def Co.toContr (d : ℕ) : Co d ⟶ Contr d where
  hom := {
    toFun := fun ψ => ContrMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ),
    map_add' := by
      intro ψ ψ'
      simp only [map_add, mulVec_add]
    map_smul' := by
      intro r ψ
      simp only [_root_.map_smul, mulVec_smul, RingHom.id_apply]}
  comm g := by
    ext ψ : 2
    simp only [ModuleCat.coe_comp, Function.comp_apply]
    conv_lhs =>
      change ContrMod.toFin1dℝEquiv.symm (η *ᵥ ((LorentzGroup.transpose g⁻¹).1 *ᵥ ψ.toFin1dℝ))
      rw [mulVec_mulVec, ← LorentzGroup.comm_minkowskiMatrix, ← mulVec_mulVec]
    rfl

/-- The isomorphism between `Contr d` and `Co d` induced by multiplication with the
  Minkowski metric. -/
def contrIsoCo (d : ℕ) : Contr d ≅ Co d where
  hom := Contr.toCo d
  inv := Co.toContr d
  hom_inv_id := by
    ext ψ
    simp only [Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply, Action.id_hom,
      ModuleCat.id_apply]
    conv_lhs => change ContrMod.toFin1dℝEquiv.symm (η *ᵥ
      CoMod.toFin1dℝEquiv (CoMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ)))
    rw [LinearEquiv.apply_symm_apply, mulVec_mulVec, minkowskiMatrix.sq]
    simp
  inv_hom_id := by
    ext ψ
    simp only [Action.comp_hom, ModuleCat.coe_comp, Function.comp_apply, Action.id_hom,
      ModuleCat.id_apply]
    conv_lhs => change CoMod.toFin1dℝEquiv.symm (η *ᵥ
      ContrMod.toFin1dℝEquiv (ContrMod.toFin1dℝEquiv.symm (η *ᵥ ψ.toFin1dℝ)))
    rw [LinearEquiv.apply_symm_apply, mulVec_mulVec, minkowskiMatrix.sq]
    simp

end Lorentz
end
