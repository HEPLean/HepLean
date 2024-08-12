/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.Color
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.UniqueDualInOther
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
/-!

# Index lists with color conditions

Here we consider `IndexListColor` which is a subtype of all lists of indices
on those where the elements to be contracted have consistent colors with respect to
a Tensor Color structure.

-/

namespace IndexNotation


namespace ColorIndexList

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

variable (l l' : ColorIndexList 𝓒)

/-!

## Reindexing

-/

def Reindexing : Prop := l.length = l'.length ∧
  ∀ (h : l.length = l'.length), l.colorMap = l'.colorMap ∘ Fin.cast h ∧
    Option.map (Fin.cast h) ∘ l.getDual? = l'.getDual? ∘ Fin.cast h

/-!

## Permutation

Test whether two `ColorIndexList`s are permutations of each other.
To prevent choice problems, this has to be done after contraction.

-/

def ContrPerm : Prop := l.contr.length = l'.contr.length ∧
  l.contr.withUniqueDualInOther l'.contr.toIndexList = Finset.univ ∧
  l'.contr.colorMap ∘ Subtype.val ∘ (l.contr.getDualInOtherEquiv l'.contr.toIndexList)
  = l.contr.colorMap ∘ Subtype.val



end ColorIndexList

end IndexNotation
