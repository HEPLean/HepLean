/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Contraction
import HepLean.SpaceTime.LorentzVector.LorentzAction
import HepLean.SpaceTime.LorentzTensor.MulActionTensor
/-!

# Real Lorentz tensors

-/
noncomputable section

open TensorProduct
open minkowskiMatrix
namespace realTensor

variable {d : ℕ}
/-!

## Definitions and lemmas needed to define a `LorentzTensorStructure`

-/

/-- The type colors for real Lorentz tensors. -/
inductive ColorType
  | up
  | down

end realTensor

open realTensor

/-! TODO: Set up the notation `𝓛𝓣ℝ` or similar. -/
/-- The `LorentzTensorStructure` associated with real Lorentz tensors. -/
def realLorentzTensor (d : ℕ) : TensorStructure ℝ where
  Color := ColorType
  ColorModule μ :=
    match μ with
    | .up => LorentzVector d
    | .down => CovariantLorentzVector d
  τ μ :=
    match μ with
    | .up => .down
    | .down => .up
  τ_involutive μ :=
    match μ with
    | .up => rfl
    | .down => rfl
  colorModule_addCommMonoid μ :=
    match μ with
    | .up => instAddCommMonoidLorentzVector d
    | .down => instAddCommMonoidCovariantLorentzVector d
  colorModule_module μ :=
    match μ with
    | .up => instModuleRealLorentzVector d
    | .down => instModuleRealCovariantLorentzVector d
  contrDual μ :=
    match μ with
    | .up => LorentzVector.contrUpDown
    | .down => LorentzVector.contrDownUp
  contrDual_symm μ :=
    match μ with
    | .up => by
      intro x y
      simp only [LorentzVector.contrDownUp, Equiv.cast_refl, Equiv.refl_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, comm_tmul]
    | .down => by
      intro x y
      simp only [LorentzVector.contrDownUp, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.comp_apply, comm_tmul, Equiv.cast_refl, Equiv.refl_apply]
  unit μ :=
    match μ with
    | .up => LorentzVector.unitUp
    | .down => LorentzVector.unitDown
  unit_lid μ :=
    match μ with
    | .up => LorentzVector.unitUp_lid
    | .down => LorentzVector.unitDown_lid
  metric μ :=
    match μ with
    | realTensor.ColorType.up => asProdLorentzVector
    | realTensor.ColorType.down => asProdCovariantLorentzVector
  metric_dual μ :=
    match μ with
    | realTensor.ColorType.up => asProdLorentzVector_contr_asCovariantProdLorentzVector
    | realTensor.ColorType.down => asProdCovariantLorentzVector_contr_asProdLorentzVector

/-- The action of the Lorentz group on real Lorentz tensors. -/
instance : MulActionTensor (LorentzGroup d) (realLorentzTensor d) where
  repColorModule μ :=
    match μ with
    | .up => LorentzVector.rep
    | .down => CovariantLorentzVector.rep
  contrDual_inv μ _ :=
    match μ with
    | .up => TensorProduct.ext' (fun _ _ => LorentzVector.contrUpDown_invariant_lorentzAction)
    | .down => TensorProduct.ext' (fun _ _ => LorentzVector.contrDownUp_invariant_lorentzAction)

end
