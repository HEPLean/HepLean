/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.UniqueDual
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.Append
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
/-!

# Index lists with color conditions

Here we consider `IndexListColor` which is a subtype of all lists of indices
on those where the elements to be contracted have consistent colors with respect to
a Tensor Color structure.

-/

namespace IndexNotation


variable (𝓒 : TensorColor)
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

structure ColorIndexList (𝓒 : TensorColor) [IndexNotation 𝓒.Color] extends IndexList 𝓒.Color where
  unique_duals : toIndexList.withDual = toIndexList.withUniqueDual
  dual_color : (Option.map toIndexList.colorMap) ∘ toIndexList.getDual?
    = (Option.map (𝓒.τ ∘ toIndexList.colorMap)) ∘
      Option.guard (fun i => (toIndexList.getDual? i).isSome)

namespace ColorIndexList

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

variable (l l2 : ColorIndexList 𝓒)

@[ext]
lemma ext {l l' : ColorIndexList 𝓒} (h : l.val = l'.val) : l = l' := by
  cases l
  cases l'
  simp_all
  apply IndexList.ext
  exact h

/-!

## Contracting an `ColorIndexList`

-/

def contr : ColorIndexList 𝓒 where
  toIndexList := l.toIndexList.contrIndexList
  unique_duals := by
    simp
  dual_color := by
    funext i
    simp [Option.guard]

@[simp]
lemma contr_contr : l.contr.contr = l.contr := by
  apply ext
  simp [contr]

/-!

## Contract equiv

-/

def contrEquiv :
    (l.withUniqueDualLT ⊕ l.withUniqueDualLT) ⊕ Fin l.contr.length ≃ Fin l.length :=
  (Equiv.sumCongr (l.withUniqueLTGTEquiv) (Equiv.refl _)).trans <|
  (Equiv.sumCongr (Equiv.subtypeEquivRight (by
  simp [l.unique_duals])) (Fin.castOrderIso l.contrIndexList_length).toEquiv).trans <|
  l.dualEquiv

/-!

## Append

-/

def append (h : (l.toIndexList ++ l2.toIndexList).withUniqueDual =
     (l.toIndexList ++ l2.toIndexList).withDual ) : ColorIndexList 𝓒 := by

end ColorIndexList

end IndexNotation
