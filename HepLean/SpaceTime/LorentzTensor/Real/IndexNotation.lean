/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.TensorIndex
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexString
import HepLean.SpaceTime.LorentzTensor.Real.Basic
/-!

# Index notation for real Lorentz tensors

This uses the general concepts of index notation in `HepLean.SpaceTime.LorentzTensor.IndexNotation`
to define the index notation for real Lorentz tensors.

-/

instance : IndexNotation realTensorColor.Color where
  charList := {'ᵘ', 'ᵤ'}
  notaEquiv :=
    ⟨fun c =>
      match c with
      | realTensorColor.ColorType.up => ⟨'ᵘ', Finset.mem_insert_self 'ᵘ' {'ᵤ'}⟩
      | realTensorColor.ColorType.down => ⟨'ᵤ', Finset.insert_eq_self.mp (by rfl)⟩,
    fun c =>
      if c = 'ᵘ' then realTensorColor.ColorType.up
      else realTensorColor.ColorType.down,
    by
      intro c
      match c with
      | realTensorColor.ColorType.up => rfl
      | realTensorColor.ColorType.down => rfl,
    by
      intro c
      by_cases hc : c = 'ᵘ'
      simp [hc]
      exact SetCoe.ext (id (Eq.symm hc))
      have hc' : c = 'ᵤ' := by
        have hc2 := c.2
        simp at hc2
        simp_all
      simp [hc']
      exact SetCoe.ext (id (Eq.symm hc'))⟩

namespace realLorentzTensor

open realTensorColor

variable {d : ℕ}

instance : IndexNotation (realLorentzTensor d).Color := instIndexNotationColorRealTensorColor
instance : DecidableEq (realLorentzTensor d).Color := instDecidableEqColorRealTensorColor

@[simp]
lemma indexNotation_eq_color : @realLorentzTensor.instIndexNotationColor d =
    instIndexNotationColorRealTensorColor := by
  rfl

@[simp]
lemma realLorentzTensor_color : (realLorentzTensor d).Color = realTensorColor.Color := by
  rfl

@[simp]
lemma toTensorColor_eq : (realLorentzTensor d).toTensorColor = realTensorColor := by
  rfl

open IndexNotation IndexString

open TensorStructure TensorIndex

/-- The construction of a tensor index from a tensor and a string satisfying conditions
  which can be automatically checked. This is a modified version of
  `TensorStructure.TensorIndex.mkDualMap` specific to real Lorentz tensors. -/
noncomputable def fromIndexStringColor {cn : Fin n → realTensorColor.Color}
    (T : (realLorentzTensor d).Tensor cn) (s : String)
    (hs : listCharIndexStringBool realTensorColor.Color s.toList = true)
    (hn : n = (IndexString.toIndexList (⟨s, hs⟩ : IndexString realTensorColor.Color)).length)
    (hc : IndexListColor.colorPropBool (IndexString.toIndexList ⟨s, hs⟩))
    (hd : TensorColor.ColorMap.DualMap.boolFin
    (IndexString.toIndexList ⟨s, hs⟩).colorMap (cn ∘ Fin.cast hn.symm)) :
    (realLorentzTensor d).TensorIndex :=
  TensorStructure.TensorIndex.mkDualMap T
    ⟨(IndexString.toIndexList (⟨s, hs⟩ : IndexString realTensorColor.Color)),
      IndexListColor.colorPropBool_indexListColorProp hc⟩ hn
      (TensorColor.ColorMap.DualMap.boolFin_DualMap hd)

/-- A tactics used to prove `colorPropBool` for real Lorentz tensors. -/
macro "prodTactic" : tactic =>
    `(tactic| {
      change @IndexListColor.colorPropBool realTensorColor _ _ _
      simp only [toTensorColor_eq, indexNotation_eq_color, fromIndexStringColor, mkDualMap,
        String.toList, ↓Char.isValue, Equiv.coe_refl, Function.comp_apply, id_eq, ne_eq,
        Function.comp_id, RelIso.coe_fn_toEquiv, prod_index, IndexListColor.prod]
      rfl})

/-- A tactic used to prove `boolFin` for real Lornetz tensors. -/
macro "dualMapTactic" : tactic =>
    `(tactic| {
      simp only [String.toList, ↓Char.isValue, toTensorColor_eq]
      rfl})

/-- Notation for the construction of a tensor index from a tensor and a string.
  Conditions are checked automatically. -/
notation:20 T "|" S:21 => fromIndexStringColor T S (by rfl) (by rfl) (by rfl) (by dualMapTactic)

/-- Notation for the product of two tensor indices. Conditions are checked automatically. -/
notation:10 T "⊗ᵀ" S:11 => TensorIndex.prod T S (IndexListColor.colorPropBool_indexListColorProp
  (by prodTactic))

/-- An example showing the allowed constructions. -/
example (T : (realLorentzTensor d).Tensor ![ColorType.up, ColorType.down]) : True := by
  let _ := T|"ᵤ₁ᵤ₂"
  let _ := T|"ᵘ³ᵤ₄"
  let _ := T|"ᵤ₁ᵤ₂" ⊗ᵀ T|"ᵘ³ᵤ₄"
  let _ := T|"ᵤ₁ᵤ₂" ⊗ᵀ T|"ᵘ³ᵤ₄" ⊗ᵀ T|"ᵘ¹ᵘ²" ⊗ᵀ T|"ᵘ⁴ᵤ₃"
  exact trivial

end realLorentzTensor
