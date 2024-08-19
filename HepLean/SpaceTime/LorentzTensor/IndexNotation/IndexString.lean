/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.TensorIndex
/-!

# Strings of indices

A string of indices e.g. `ᵘ¹²ᵤ₄₃` is the structure we usually see
following a tensor symbol in index notation.

This file defines such an index string, and from it constructs a list of indices.

-/

open Lean
open String

namespace IndexNotation

variable (X : Type) [IndexNotation X] [Fintype X] [DecidableEq X]

/-!

## The definition of an index string

-/

/-- Takes in a list of characters and splits it into a list of characters at those characters
  which are notation characters e.g. `'ᵘ'`. -/
def stringToPreIndexList (l : List Char) : List (List Char) :=
  let indexHeads := l.filter (fun c => isNotationChar X c)
  let indexTails := l.splitOnP (fun c => isNotationChar X c)
  let l' := List.zip indexHeads indexTails.tail
  l'.map fun x => x.1 :: x.2

/-- A bool which is true given a list of characters if and only if everl element
  of the corresponding `stringToPreIndexList` correspondings to an index. -/
def listCharIsIndexString (l : List Char) : Bool :=
  (stringToPreIndexList X l).all fun l => (listCharIndex X l && l ≠ [])

/-- A string of indices to be associated with a tensor. For example, `ᵘ⁰ᵤ₂₆₀ᵘ³`. -/
def IndexString : Type := {s : String // listCharIsIndexString X s.toList = true}

namespace IndexString

/-!

## Constructing a list of indices from an index string

-/

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]

/-- The character list associated with a index string. -/
def toCharList (s : IndexString X) : List Char := s.val.toList

/-! TODO: Move. -/
/-- Takes a list of characters to the correpsonding index if it exists else to `none`. -/
def charListToOptionIndex (l : List Char) : Option (Index X) :=
  if h : listCharIndex X l && l ≠ [] then
    some (Index.ofCharList l (by simpa using h))
  else
    none

/-- The indices associated to an index string. -/
def toIndexList (s : IndexString X) : IndexList X :=
  {val :=
    (stringToPreIndexList X s.toCharList).filterMap fun l => charListToOptionIndex l}

/-- The formation of an index list from a string `s` statisfying `listCharIndexStringBool`. -/
def toIndexList' (s : String) (hs : listCharIsIndexString X s.toList = true) : IndexList X :=
  toIndexList ⟨s, hs⟩

end IndexString

end IndexNotation
namespace TensorStructure

/-!

## Making a tensor index from an index string

-/

namespace TensorIndex
variable {R : Type} [CommSemiring R] (𝓣 : TensorStructure R)
variable {𝓣 : TensorStructure R} [IndexNotation 𝓣.Color] [Fintype 𝓣.Color] [DecidableEq 𝓣.Color]
variable {n m : ℕ} {cn : Fin n → 𝓣.Color} {cm : Fin m → 𝓣.Color}

open IndexNotation ColorIndexList IndexString

/-- The construction of a tensor index from a tensor and a string satisfing conditions which are
  easy to check automatically. -/
noncomputable def fromIndexString (T : 𝓣.Tensor cn) (s : String)
    (hs : listCharIsIndexString 𝓣.toTensorColor.Color s.toList = true)
    (hn : n = (toIndexList' s hs).length)
    (hD : (toIndexList' s hs).withDual = (toIndexList' s hs).withUniqueDual)
    (hC : IndexList.ColorCond (toIndexList' s hs))
    (hd : TensorColor.ColorMap.DualMap (toIndexList' s hs).colorMap
      (cn ∘ Fin.cast hn.symm)) : 𝓣.TensorIndex :=
  TensorStructure.TensorIndex.mkDualMap T ⟨(toIndexList' s hs), hD, hC⟩ hn hd

end TensorIndex

end TensorStructure
