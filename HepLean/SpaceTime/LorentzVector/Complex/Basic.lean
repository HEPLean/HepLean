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
import HepLean.SpaceTime.PauliMatrices.SelfAdjoint
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

lemma complexContrBasis_ρ_val (M : SL(2,ℂ)) (v : complexContr) :
    ((complexContr.ρ M) v).val =
    LorentzGroup.toComplex (SL2C.toLorentzGroup M) *ᵥ v.val := by
  rfl

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

/-!

## Relation to real

-/

/-- The semilinear map including real Lorentz vectors into complex contravariant
  lorentz vectors. -/
def inclCongrRealLorentz : LorentzVector 3 →ₛₗ[Complex.ofReal] complexContr where
  toFun v := {val := ofReal ∘ v}
  map_add' x y := by
    apply Lorentz.ContrℂModule.ext
    rw [Lorentz.ContrℂModule.val_add]
    funext i
    simp only [Function.comp_apply, ofReal_eq_coe, Pi.add_apply]
    change ofReal (x i + y i) = _
    simp only [ofReal_eq_coe, ofReal_add]
  map_smul' c x := by
    apply Lorentz.ContrℂModule.ext
    rw [Lorentz.ContrℂModule.val_smul]
    funext i
    simp only [Function.comp_apply, ofReal_eq_coe, Pi.smul_apply]
    change ofReal (c • x i) = _
    simp only [smul_eq_mul, ofReal_eq_coe, ofReal_mul]

lemma inclCongrRealLorentz_val (v : LorentzVector 3) :
    (inclCongrRealLorentz v).val = ofReal ∘ v := rfl

lemma complexContrBasis_of_real (i : Fin 1 ⊕ Fin 3) :
    (complexContrBasis i) = inclCongrRealLorentz (LorentzVector.stdBasis i) := by
  apply Lorentz.ContrℂModule.ext
  simp only [complexContrBasis, Basis.coe_ofEquivFun, inclCongrRealLorentz, LorentzVector.stdBasis,
    LinearMap.coe_mk, AddHom.coe_mk]
  ext j
  simp only [Function.comp_apply, ofReal_eq_coe]
  erw [Pi.basisFun_apply]
  change (Pi.single i 1) j = _
  exact Eq.symm (Pi.apply_single (fun _ => ofReal') (congrFun rfl) i 1 j)

lemma inclCongrRealLorentz_ρ (M : SL(2, ℂ)) (v : LorentzVector 3) :
    (complexContr.ρ M) (inclCongrRealLorentz v) =
    inclCongrRealLorentz (SL2C.repLorentzVector M v) := by
  apply Lorentz.ContrℂModule.ext
  rw [complexContrBasis_ρ_val, inclCongrRealLorentz_val, inclCongrRealLorentz_val]
  rw [LorentzGroup.toComplex_mulVec_ofReal]
  apply congrArg
  simp only [SL2C.toLorentzGroup_apply_coe]
  rw [SL2C.repLorentzVector_apply_eq_mulVec]
  rfl

lemma SL2CRep_ρ_basis (M : SL(2, ℂ)) (i : Fin 1 ⊕ Fin 3) :
    (complexContr.ρ M) (complexContrBasis i) =
    ∑ j, (SL2C.toLorentzGroup M).1 j i •
    complexContrBasis j := by
  rw [complexContrBasis_of_real, inclCongrRealLorentz_ρ, SL2C.repLorentzVector_stdBasis, map_sum]
  apply congrArg
  funext j
  simp only [LinearMap.map_smulₛₗ, ofReal_eq_coe, coe_smul]
  rw [complexContrBasis_of_real]

end Lorentz
end
