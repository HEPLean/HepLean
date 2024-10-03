/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.IndexNotation.IndexList.Color
import HepLean.Tensors.Basic
import Init.Data.List.Lemmas
/-!

# Color index lists

A color index list is defined as a list of indices with two constraints. The first is that
if an index has a dual, that dual is unique. The second is that if an index has a dual, the
color of that dual is dual to the color of the index.

The indices of a tensor are required to be of this type.

-/

namespace IndexNotation

variable (𝓒 : TensorColor)
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

/-- A list of indices with the additional constraint that if a index has a dual,
  that dual is unique, and the dual of an index has dual color to that index.

  This is the permissible type of indices which can be used for a tensor. For example,
  the index list `['ᵘ¹', 'ᵤ₁']` can be extended to a `ColorIndexList` but the index list
  `['ᵘ¹', 'ᵤ₁', 'ᵤ₁']` cannot. -/
structure ColorIndexList (𝓒 : TensorColor) [IndexNotation 𝓒.Color] extends IndexList 𝓒.Color where
  /-- The condition that for index with a dual, that dual is the unique other index with
  an identical `id`. -/
  unique_duals : toIndexList.OnlyUniqueDuals
  /-- The condition that for an index with a dual, that dual has dual color to the index. -/
  dual_color : IndexList.ColorCond toIndexList

namespace ColorIndexList

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color]

variable (l l2 : ColorIndexList 𝓒)
open IndexList TensorColor

instance : Coe (ColorIndexList 𝓒) (IndexList 𝓒.Color) := ⟨fun l => l.toIndexList⟩

/-- The colorMap of a `ColorIndexList` as a `𝓒.ColorMap`.
    This is to be compared with `colorMap` which is a map `Fin l.length → 𝓒.Color`. -/
def colorMap' : 𝓒.ColorMap (Fin l.length) :=
  l.colorMap

@[ext]
lemma ext {l l' : ColorIndexList 𝓒} (h : l.val = l'.val) : l = l' := by
  cases l
  cases l'
  simp_all
  apply IndexList.ext
  exact h

lemma ext' {l l' : ColorIndexList 𝓒} (h : l.toIndexList = l'.toIndexList) : l = l' := by
  cases l
  cases l'
  simp_all

/-! TODO: `orderEmbOfFin_univ` should be replaced with a mathlib lemma if possible. -/
lemma orderEmbOfFin_univ (n m : ℕ) (h : n = m) :
    Finset.orderEmbOfFin (Finset.univ : Finset (Fin n)) (by simp [h]: Finset.univ.card = m) =
    (Fin.castOrderIso h.symm).toOrderEmbedding := by
  symm
  have h1 : (Fin.castOrderIso h.symm).toFun =
      (Finset.orderEmbOfFin (Finset.univ : Finset (Fin n))
      (by simp [h]: Finset.univ.card = m)).toFun := by
    apply Finset.orderEmbOfFin_unique
    intro x
    exact Finset.mem_univ ((Fin.castOrderIso (Eq.symm h)).toFun x)
    exact fun ⦃a b⦄ a => a
  exact Eq.symm (OrderEmbedding.range_inj.mp (congrArg Set.range (id (Eq.symm h1))))

/-!

## Cons for `ColorIndexList`

-/

/-- The `ColorIndexList` whose underlying list of indices is empty. -/
def empty : ColorIndexList 𝓒 where
  val := []
  unique_duals := rfl
  dual_color := rfl

/-!

## CountId for `ColorIndexList`

-/

lemma countId_le_two [DecidableEq 𝓒.Color] (l : ColorIndexList 𝓒) (I : Index 𝓒.Color) :
    l.countId I ≤ 2 :=
  (OnlyUniqueDuals.iff_countId_leq_two').mp l.unique_duals I

end ColorIndexList
end IndexNotation
