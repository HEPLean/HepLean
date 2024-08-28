/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.TensorIndex
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexString
import HepLean.SpaceTime.LorentzTensor.EinsteinNotation.Basic
/-!

# Index notation for Einstein tensors

-/

instance : IndexNotation einsteinTensorColor.Color where
  charList := {'ᵢ'}
  notaEquiv :=
    ⟨fun _ => ⟨'ᵢ', Finset.mem_singleton.mpr rfl⟩,
    fun _ => Unit.unit,
    fun _ => rfl,
    by
      intro c
      have hc2 := c.2
      simp only [↓Char.isValue, Finset.mem_singleton] at hc2
      exact SetCoe.ext (id (Eq.symm hc2))⟩

namespace einsteinTensor

open einsteinTensorColor
open IndexNotation IndexString
open TensorStructure TensorIndex

variable {R : Type} [CommSemiring R] {n m : ℕ}

instance : IndexNotation (einsteinTensor R n).Color := instIndexNotationColorEinsteinTensorColor
instance : DecidableEq (einsteinTensor R n).Color := instDecidableEqColorEinsteinTensorColor

@[simp]
lemma indexNotation_eq_color : @einsteinTensor.instIndexNotationColor R _ n =
    instIndexNotationColorEinsteinTensorColor := by
  rfl

@[simp]
lemma decidableEq_eq_color : @einsteinTensor.instDecidableEqColor R _ n =
    instDecidableEqColorEinsteinTensorColor := by
  rfl

@[simp]
lemma einsteinTensor_color : (einsteinTensor R n).Color = einsteinTensorColor.Color := by
  rfl

@[simp]
lemma toTensorColor_eq : (einsteinTensor R n).toTensorColor = einsteinTensorColor := by
  rfl

/-- The construction of a tensor index from a tensor and a string satisfying conditions
  which can be automatically checked. This is a modified version of
  `TensorStructure.TensorIndex.mkDualMap` specific to real Lorentz tensors. -/
noncomputable def fromIndexStringColor {R : Type} [CommSemiring R]
    {cn : Fin n → einsteinTensorColor.Color}
    (T : (einsteinTensor R m).Tensor cn) (s : String)
    (hs : listCharIsIndexString einsteinTensorColor.Color s.toList = true)
    (hn : n = (toIndexList' s hs).length)
    (hD : (toIndexList' s hs).OnlyUniqueDuals)
    (hC : IndexList.ColorCond.bool (toIndexList' s hs))
    (hd : TensorColor.ColorMap.DualMap.boolFin'
      (toIndexList' s hs).colorMap (cn ∘ Fin.cast hn.symm)) :
    (einsteinTensor R m).TensorIndex :=
  TensorStructure.TensorIndex.mkDualMap T ⟨(toIndexList' s hs), hD,
      IndexList.ColorCond.iff_bool.mpr hC⟩ hn
      (TensorColor.ColorMap.DualMap.boolFin'_DualMap hd)

@[simp]
lemma fromIndexStringColor_indexList {R : Type} [CommSemiring R]
    {cn : Fin n → einsteinTensorColor.Color}
    (T : (einsteinTensor R m).Tensor cn) (s : String)
    (hs : listCharIsIndexString einsteinTensorColor.Color s.toList = true)
    (hn : n = (toIndexList' s hs).length)
    (hD : (toIndexList' s hs).OnlyUniqueDuals)
    (hC : IndexList.ColorCond.bool (toIndexList' s hs))
    (hd : TensorColor.ColorMap.DualMap.boolFin'
      (toIndexList' s hs).colorMap (cn ∘ Fin.cast hn.symm)) :
    (fromIndexStringColor T s hs hn hD hC hd).toIndexList = toIndexList' s hs := by
  rfl

/-- A tactic used to prove `boolFin` for real Lornetz tensors. -/
macro "dualMapTactic" : tactic =>
    `(tactic| {
    simp only [toTensorColor_eq]
    decide })

/-- Notation for the construction of a tensor index from a tensor and a string.
  Conditions are checked automatically. -/
notation:20 T "|" S:21 => fromIndexStringColor T S
  (by decide)
  (by decide) (by rfl)
  (by decide)
  (by dualMapTactic)

/-- A tactics used to prove `colorPropBool` for real Lorentz tensors. -/
macro "prodTactic" : tactic =>
    `(tactic| {
    apply (ColorIndexList.AppendCond.iff_bool _ _).mpr
    change @ColorIndexList.AppendCond.bool einsteinTensorColor
      instDecidableEqColorEinsteinTensorColor _ _
    simp only [prod_toIndexList, indexNotation_eq_color, fromIndexStringColor, mkDualMap,
      toTensorColor_eq, decidableEq_eq_color]
    decide})

lemma mem_fin_list (n : ℕ) (i : Fin n) : i ∈ Fin.list n := by
  have h1' : (Fin.list n)[i] = i := Fin.getElem_list _ _
  exact h1' ▸ List.getElem_mem _ _ _

instance (n : ℕ) (i : Fin n) : Decidable (i ∈ Fin.list n) :=
  isTrue (mem_fin_list n i)

/-- The product of Real Lorentz tensors. Conditions on indices are checked automatically. -/
notation:10 T "⊗ᵀ" S:11 => TensorIndex.prod T S (by prodTactic)
/-- An example showing the allowed constructions. -/
example (T : (einsteinTensor R n).Tensor ![Unit.unit, Unit.unit]) : True := by
  let _ := T|"ᵢ₂ᵢ₃"
  let _ := T|"ᵢ₁ᵢ₂" ⊗ᵀ T|"ᵢ₂ᵢ₁"
  let _ := T|"ᵢ₁ᵢ₂" ⊗ᵀ T|"ᵢ₂ᵢ₁" ⊗ᵀ T|"ᵢ₃ᵢ₄"
  exact trivial

end einsteinTensor
