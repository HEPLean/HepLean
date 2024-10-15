/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import HepLean.SpaceTime.SL2C.Basic
import HepLean.SpaceTime.LorentzVector.Modules
import HepLean.Meta.Informal
import Mathlib.RepresentationTheory.Rep
import HepLean.Tensors.Basic
/-!

# Complex Lorentz vectors

We define complex Lorentz vectors in 4d space-time as representations of SL(2, C).

-/

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open SpaceTime

namespace Lorentz

/-- The representation of `SL(2, ℂ)` on complex vectors corresponding to contravariant
  Lorentz vectors. In index notation these have an up index `ψⁱ`. -/
def complexContr : Rep ℂ SL(2, ℂ) := Rep.of ContrℂModule.SL2CRep

/-- The representation of `SL(2, ℂ)` on complex vectors corresponding to contravariant
  Lorentz vectors. In index notation these have a down index `ψⁱ`. -/
def complexCo : Rep ℂ SL(2, ℂ) := Rep.of CoℂModule.SL2CRep

/-- The standard basis of complex contravariant Lorentz vectors. -/
def complexContrBasis : Basis (Fin 1 ⊕ Fin 3) ℂ complexContr := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ ContrℂModule.toFin13ℂFun)

@[simp]
lemma complexContrBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (LinearMap.toMatrix complexContrBasis complexContrBasis) (complexContr.ρ M) i j =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M)) i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [complexContrBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply, transpose_apply]
  change (((LorentzGroup.toComplex (SL2C.toLorentzGroup M))) *ᵥ (Pi.single j 1)) i = _
  simp only [mulVec_single, transpose_apply, mul_one]

/-- The standard basis of complex covariant Lorentz vectors. -/
def complexCoBasis : Basis (Fin 1 ⊕ Fin 3) ℂ complexCo := Basis.ofEquivFun
  (Equiv.linearEquiv ℂ CoℂModule.toFin13ℂFun)

@[simp]
lemma complexCoBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (LinearMap.toMatrix complexCoBasis complexCoBasis) (complexCo.ρ M) i j =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [complexCoBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply, transpose_apply]
  change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ (Pi.single j 1)) i = _
  simp only [mulVec_single, transpose_apply, mul_one]

end Lorentz
end
