/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexListColor
import HepLean.SpaceTime.LorentzTensor.Basic
import HepLean.SpaceTime.LorentzTensor.RisingLowering
import HepLean.SpaceTime.LorentzTensor.Contraction
/-!

# The structure of a tensor with a string of indices

-/

namespace TensorStructure
noncomputable section

open TensorColor
open IndexNotation

variable {R : Type} [CommSemiring R] (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color}
  {cW : W → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν η : 𝓣.Color}

variable [IndexNotation 𝓣.Color] [Fintype 𝓣.Color] [DecidableEq 𝓣.Color]

/-- The structure an tensor with a index specification e.g. `ᵘ¹ᵤ₂`. -/
structure TensorIndex where
  /-- The list of indices. -/
  index : IndexListColor 𝓣.toTensorColor
  /-- The underlying tensor. -/
  tensor : 𝓣.Tensor index.1.colorMap

namespace TensorIndex
open TensorColor
variable {𝓣 : TensorStructure R} [IndexNotation 𝓣.Color] [Fintype 𝓣.Color] [DecidableEq 𝓣.Color]
variable {n m : ℕ} {cn : Fin n → 𝓣.Color} {cm : Fin m → 𝓣.Color}

lemma index_eq_colorMap_eq {T₁ T₂ : 𝓣.TensorIndex} (hi : T₁.index = T₂.index) :
    (T₂.index).1.colorMap = (T₁.index).1.colorMap ∘ (Fin.castOrderIso (by rw [hi])).toEquiv := by
  funext i
  congr 1
  rw [hi]
  simp only [RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply]
  exact
    (Fin.heq_ext_iff (congrArg IndexList.numIndices (congrArg Subtype.val (id (Eq.symm hi))))).mpr
      rfl

lemma ext (T₁ T₂ : 𝓣.TensorIndex) (hi : T₁.index = T₂.index)
    (h : T₁.tensor = 𝓣.mapIso (Fin.castOrderIso (by rw [hi])).toEquiv
    (index_eq_colorMap_eq hi) T₂.tensor) : T₁ = T₂ := by
  cases T₁; cases T₂
  simp at hi
  subst hi
  simp_all

/-- The construction of a `TensorIndex` from a tensor, a IndexListColor, and a condition
  on the dual maps. -/
def mkDualMap (T : 𝓣.Tensor cn) (l : IndexListColor 𝓣.toTensorColor) (hn : n = l.1.length)
    (hd : DualMap l.1.colorMap (cn ∘ Fin.cast hn.symm)) :
    𝓣.TensorIndex where
  index := l
  tensor :=
      𝓣.mapIso (Equiv.refl _) (DualMap.split_dual' (by simp [hd])) <|
      𝓣.dualize (DualMap.split l.1.colorMap (cn ∘ Fin.cast hn.symm)) <|
      (𝓣.mapIso (Fin.castOrderIso hn).toEquiv rfl T : 𝓣.Tensor (cn ∘ Fin.cast hn.symm))

/-- The contraction of indices in a `TensorIndex`. -/
def contr (T : 𝓣.TensorIndex) : 𝓣.TensorIndex where
  index := T.index.contr
  tensor :=
      𝓣.mapIso (Fin.castOrderIso T.index.contr_numIndices.symm).toEquiv
      T.index.contr_colorMap <|
      𝓣.contr (T.index.splitContr).symm T.index.splitContr_map T.tensor

/-- The tensor product of two `TensorIndex`. -/
def prod (T₁ T₂ : 𝓣.TensorIndex)
    (h : IndexListColorProp 𝓣.toTensorColor (T₁.index.1 ++ T₂.index.1)) : 𝓣.TensorIndex where
  index := T₁.index.prod T₂.index h
  tensor :=
      𝓣.mapIso ((Fin.castOrderIso (IndexListColor.prod_numIndices)).toEquiv.trans
        (finSumFinEquiv.symm)).symm
      (IndexListColor.prod_colorMap h) <|
      𝓣.tensoratorEquiv _ _ (T₁.tensor ⊗ₜ[R] T₂.tensor)

/-- The scalar multiplication of a `TensorIndex` by an element of `R`. -/
def smul (r : R) (T : 𝓣.TensorIndex) : 𝓣.TensorIndex where
  index := T.index
  tensor := r • T.tensor

/-- The addition of two `TensorIndex` given the condition that, after contraction,
  their index lists are the same. -/
def add (T₁ T₂ : 𝓣.TensorIndex) (h : IndexListColor.PermContr T₁.index T₂.index) :
    𝓣.TensorIndex where
  index := T₁.index.contr
  tensor :=
    let T1 := T₁.contr.tensor
    let T2 :𝓣.Tensor (T₁.contr.index).1.colorMap :=
      𝓣.mapIso h.toEquiv.symm h.toEquiv_colorMap T₂.contr.tensor
    T1 + T2

/-- An (equivalence) relation on two `TensorIndex` given that after contraction,
  the two underlying tensors are the equal. -/
def Rel (T₁ T₂ : 𝓣.TensorIndex) : Prop :=
  T₁.index.PermContr T₂.index ∧ ∀ (h : T₁.index.PermContr T₂.index),
  T₁.contr.tensor = 𝓣.mapIso h.toEquiv.symm h.toEquiv_colorMap T₂.contr.tensor

end TensorIndex
end
end TensorStructure
