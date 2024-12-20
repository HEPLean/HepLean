/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.ComplexVector.Modules
/-!

# Complex Lorentz vectors

We define complex Lorentz vectors in 4d space-time as representations of SL(2, C).

-/

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

namespace Lorentz

/-- The representation of `SL(2, ℂ)` on complex vectors corresponding to contravariant
  Lorentz vectors. In index notation these have an up index `ψⁱ`. -/
def complexContr : Rep ℂ SL(2, ℂ) := Rep.of ContrℂModule.SL2CRep

/-- The representation of `SL(2, ℂ)` on complex vectors corresponding to contravariant
  Lorentz vectors. In index notation these have a down index `ψⁱ`. -/
def complexCo : Rep ℂ SL(2, ℂ) := Rep.of CoℂModule.SL2CRep

/-- The standard basis of complex contravariant Lorentz vectors. -/
def complexContrBasis : Basis (Fin 1 ⊕ Fin 3) ℂ complexContr :=
  Basis.ofEquivFun ContrℂModule.toFin13ℂEquiv

@[simp]
lemma complexContrBasis_toFin13ℂ (i :Fin 1 ⊕ Fin 3) :
    (complexContrBasis i).toFin13ℂ = Pi.single i 1 := by
  simp only [complexContrBasis, Basis.coe_ofEquivFun]
  rfl

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

/-- The standard basis of complex contravariant Lorentz vectors indexed by `Fin 4`. -/
def complexContrBasisFin4 : Basis (Fin 4) ℂ complexContr :=
  Basis.reindex complexContrBasis finSumFinEquiv

/-- The standard basis of complex covariant Lorentz vectors. -/
def complexCoBasis : Basis (Fin 1 ⊕ Fin 3) ℂ complexCo :=
  Basis.ofEquivFun CoℂModule.toFin13ℂEquiv

@[simp]
lemma complexCoBasis_toFin13ℂ (i :Fin 1 ⊕ Fin 3) : (complexCoBasis i).toFin13ℂ = Pi.single i 1 := by
  simp only [complexCoBasis, Basis.coe_ofEquivFun]
  rfl

@[simp]
lemma complexCoBasis_ρ_apply (M : SL(2,ℂ)) (i j : Fin 1 ⊕ Fin 3) :
    (LinearMap.toMatrix complexCoBasis complexCoBasis) (complexCo.ρ M) i j =
    (LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ i j := by
  rw [LinearMap.toMatrix_apply]
  simp only [complexCoBasis, Basis.coe_ofEquivFun, Basis.ofEquivFun_repr_apply, transpose_apply]
  change ((LorentzGroup.toComplex (SL2C.toLorentzGroup M))⁻¹ᵀ *ᵥ (Pi.single j 1)) i = _
  simp only [mulVec_single, transpose_apply, mul_one]

/-- The standard basis of complex covariant Lorentz vectors indexed by `Fin 4`. -/
def complexCoBasisFin4 : Basis (Fin 4) ℂ complexCo :=
  Basis.reindex complexCoBasis finSumFinEquiv

/-!

## Relation to real

-/

/-- The semilinear map including real Lorentz vectors into complex contravariant
  lorentz vectors. -/
def inclCongrRealLorentz : ContrMod 3 →ₛₗ[Complex.ofRealHom] complexContr where
  toFun v := {val := ofReal ∘ v.toFin1dℝ}
  map_add' x y := by
    apply Lorentz.ContrℂModule.ext
    rw [Lorentz.ContrℂModule.val_add]
    funext i
    simp only [Function.comp_apply, ofRealHom_eq_coe, Pi.add_apply, map_add]
    simp only [ofRealHom_eq_coe, ofReal_add]
  map_smul' c x := by
    apply Lorentz.ContrℂModule.ext
    rw [Lorentz.ContrℂModule.val_smul]
    funext i
    simp only [Function.comp_apply, ofRealHom_eq_coe, Pi.smul_apply, _root_.map_smul]
    simp only [smul_eq_mul, ofRealHom_eq_coe, ofReal_mul]

lemma inclCongrRealLorentz_val (v : ContrMod 3) :
    (inclCongrRealLorentz v).val = ofRealHom ∘ v.toFin1dℝ := rfl

lemma complexContrBasis_of_real (i : Fin 1 ⊕ Fin 3) :
    (complexContrBasis i) = inclCongrRealLorentz (ContrMod.stdBasis i) := by
  apply Lorentz.ContrℂModule.ext
  simp only [complexContrBasis, Basis.coe_ofEquivFun, inclCongrRealLorentz,
    LinearMap.coe_mk, AddHom.coe_mk]
  ext j
  simp only [Function.comp_apply]
  change (Pi.single i 1) j = _
  by_cases h : i = j
  · subst h
    rw [ContrMod.toFin1dℝ, ContrMod.stdBasis_toFin1dℝEquiv_apply_same]
    simp
  · rw [ContrMod.toFin1dℝ, ContrMod.stdBasis_toFin1dℝEquiv_apply_ne h]
    simp [h]

lemma inclCongrRealLorentz_ρ (M : SL(2, ℂ)) (v : ContrMod 3) :
    (complexContr.ρ M) (inclCongrRealLorentz v) =
    inclCongrRealLorentz ((Contr 3).ρ (SL2C.toLorentzGroup M) v) := by
  apply Lorentz.ContrℂModule.ext
  rw [complexContrBasis_ρ_val, inclCongrRealLorentz_val, inclCongrRealLorentz_val]
  rw [LorentzGroup.toComplex_mulVec_ofReal]
  apply congrArg
  simp only [SL2C.toLorentzGroup_apply_coe]
  change _ = ContrMod.toFin1dℝ ((SL2C.toLorentzGroup M) *ᵥ v)
  simp only [SL2C.toLorentzGroup_apply_coe, ContrMod.mulVec_toFin1dℝ]

/-! TODO: Rename. -/
lemma SL2CRep_ρ_basis (M : SL(2, ℂ)) (i : Fin 1 ⊕ Fin 3) :
    (complexContr.ρ M) (complexContrBasis i) =
    ∑ j, (SL2C.toLorentzGroup M).1 j i •
    complexContrBasis j := by
  rw [complexContrBasis_of_real, inclCongrRealLorentz_ρ]
  rw [Contr.ρ_stdBasis, map_sum]
  apply congrArg
  funext j
  simp only [LinearMap.map_smulₛₗ, ofRealHom_eq_coe, coe_smul]
  rw [complexContrBasis_of_real]

/-! TODO: Include relation to real Lorentz vectors. -/
end Lorentz
end
