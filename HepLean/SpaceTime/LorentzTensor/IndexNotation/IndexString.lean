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

## Lists of characters forming a string of indices.

-/

/-- A lemma used to show terminiation of recursive definitions which follow.
  It says that the length of `List.dropWhile _ l.tail` is less then the length of
  `l` when `l` is non-empty. -/
lemma dropWhile_isIndexSpecifier_length_lt (l : List Char) (hl : l ≠ []) :
    (List.dropWhile (fun c => !isNotationChar X c) l.tail).length < l.length := by
  let ld := l.tail.dropWhile (fun c => ¬ isNotationChar X c)
  let lt := l.tail.takeWhile (fun c => ¬ isNotationChar X c)
  simp only [gt_iff_lt]
  have h2 : lt ++ ld = l.tail := by
    exact List.takeWhile_append_dropWhile _ _
  have h3 := congrArg List.length h2
  rw [List.length_append] at h3
  have h4 : l.length ≠ 0 := by
    simp_all only [ne_eq, Bool.not_eq_true, Bool.decide_eq_false, List.takeWhile_append_dropWhile,
      List.length_tail, List.length_eq_zero, not_false_eq_true]
  have h5 : l.tail.length < l.length := by
    rw [List.length_tail]
    omega
  have h6 : ld.length < l.length := by
    omega
  simpa [ld] using h6

/-- The proposition for a list of characters to be an index string. -/
def listCharIndexString (l : List Char) : Prop :=
  if h : l = [] then True
  else
    let sfst := l.head h
    if ¬ isNotationChar X sfst then False
    else
      let lt := l.tail.takeWhile (fun c => ¬ isNotationChar X c)
      let ld := l.tail.dropWhile (fun c => ¬ isNotationChar X c)
      if ¬ listCharIndexTail sfst lt then False
      else listCharIndexString ld
termination_by l.length
decreasing_by
  simpa [ld, InvImage] using dropWhile_isIndexSpecifier_length_lt X l h

/-- A bool version of `listCharIndexString` for computation. -/
def listCharIndexStringBool (l : List Char) : Bool :=
  if h : l = [] then true
  else
    let sfst := l.head h
    if ¬ isNotationChar X sfst then false
    else
      let lt := l.tail.takeWhile (fun c => ¬ isNotationChar X c)
      let ld := l.tail.dropWhile (fun c => ¬ isNotationChar X c)
      if ¬ listCharIndexTail sfst lt then false
      else listCharIndexStringBool ld
termination_by l.length
decreasing_by
  simpa [ld, InvImage] using dropWhile_isIndexSpecifier_length_lt X l h

lemma listCharIndexString_iff (l : List Char) : listCharIndexString X l
    ↔ (if h : l = [] then True else
    let sfst := l.head h
    if ¬ isNotationChar X sfst then False
    else
      let lt := l.tail.takeWhile (fun c => ¬ isNotationChar X c)
      let ld := l.tail.dropWhile (fun c => ¬ isNotationChar X c)
      if ¬ listCharIndexTail sfst lt then False
      else listCharIndexString X ld) := by
  rw [listCharIndexString]

lemma listCharIndexString_iff_bool (l : List Char) :
    listCharIndexString X l ↔ listCharIndexStringBool X l = true := by
  rw [listCharIndexString, listCharIndexStringBool]
  by_cases h : l = []
  simp [h]
  simp [h]
  intro _ _
  exact listCharIndexString_iff_bool _
termination_by l.length
decreasing_by
  simpa [InvImage] using dropWhile_isIndexSpecifier_length_lt X l h

instance : Decidable (listCharIndexString X l) :=
  @decidable_of_decidable_of_iff _ _
    ((listCharIndexStringBool X l).decEq true)
      (listCharIndexString_iff_bool X l).symm

/-!

## Returning the chars of first index from chars of string of indices.

In particular from a list of characters which form an index string,
to a list of characters which forms an index.

-/

/-- If a list of characters corresponds to an index string, then its head is an
  index specifier. -/
lemma listCharIndexString_head_isIndexSpecifier (l : List Char) (h : listCharIndexString X l)
    (hl : l ≠ []) : isNotationChar X (l.head hl) := by
  by_contra
  rw [listCharIndexString] at h
  simp_all only [↓reduceDIte, Bool.false_eq_true, not_false_eq_true, ↓reduceIte]

/-- The tail of the first index in a list of characters corresponds to an index string
  (junk on other lists). -/
def listCharIndexStringHeadIndexTail (l : List Char) : List Char :=
  l.tail.takeWhile (fun c => ¬ isNotationChar X c)

/-- The tail of the first index in a list of characters corresponds to an index string
  is the tail of a list of characters corresponding to an index specified by the head. -/
lemma listCharIndexStringHeadIndexTail_listCharIndexTail (l : List Char)
    (h : listCharIndexString X l) (hl : l ≠ []) :
    listCharIndexTail (l.head hl) (listCharIndexStringHeadIndexTail X l) := by
  by_contra
  have h1 := listCharIndexString_head_isIndexSpecifier X l h hl
  rw [listCharIndexString] at h
  simp_all only [not_true_eq_false, Bool.not_eq_true, Bool.decide_eq_false, ite_not, if_false_right,
    ite_false, dite_false]
  obtain ⟨left, _⟩ := h
  rename_i x _
  simp [listCharIndexStringHeadIndexTail] at x
  simp_all only [Bool.false_eq_true]

/-- The first list of characters which form a index, from a list of characters
  which form a string of indices. -/
def listCharIndexStringHeadIndex (l : List Char) : List Char :=
  if h : l = [] then []
  else l.head h :: listCharIndexStringHeadIndexTail X l

lemma listCharIndexStringHeadIndex_listCharIndex (l : List Char) (h : listCharIndexString X l) :
    listCharIndex X (listCharIndexStringHeadIndex X l) := by
  by_cases h1 : l = []
  · subst h1
    simp [listCharIndex, listCharIndexStringHeadIndex]
  · simp [listCharIndexStringHeadIndex, listCharIndex, h1]
    apply And.intro
    exact listCharIndexString_head_isIndexSpecifier X l h h1
    exact listCharIndexStringHeadIndexTail_listCharIndexTail X l h h1

/-!

## Dropping chars of first index from chars of string of indices.

-/

/-- The list of characters obtained by dropping the first block which
  corresponds to an index. -/
def listCharIndexStringDropHeadIndex (l : List Char) : List Char :=
  l.tail.dropWhile (fun c => ¬ isNotationChar X c)

lemma listCharIndexStringDropHeadIndex_listCharIndexString (l : List Char)
    (h : listCharIndexString X l) :
    listCharIndexString X (listCharIndexStringDropHeadIndex X l) := by
  by_cases h1 : l = []
  · subst h1
    simp [listCharIndexStringDropHeadIndex, listCharIndexString]
  · simp [listCharIndexStringDropHeadIndex, h1]
    rw [listCharIndexString] at h
    simp_all only [↓reduceDIte, Bool.not_eq_true, Bool.decide_eq_false, ite_not, if_false_right,
      if_false_left, Bool.not_eq_false]

/-!

## Chars of all indices from char of string of indices

-/

/-- Given a list list of characters corresponding to an index string, the list
  of lists of characters which correspond to an index and are non-zero corresponding
  to that index string. -/
def listCharIndexStringTolistCharIndex (l : List Char) (h : listCharIndexString X l) :
    List ({lI : List Char // listCharIndex X lI ∧ lI ≠ []}) :=
  if hl : l = [] then [] else
    ⟨listCharIndexStringHeadIndex X l, by
      apply And.intro (listCharIndexStringHeadIndex_listCharIndex X l h)
      simp [listCharIndexStringHeadIndex]
      exact hl⟩ ::
    (listCharIndexStringTolistCharIndex (listCharIndexStringDropHeadIndex X l)
        (listCharIndexStringDropHeadIndex_listCharIndexString X l h))
termination_by l.length
decreasing_by
  rename_i h1
  simpa [InvImage, listCharIndexStringDropHeadIndex] using
    dropWhile_isIndexSpecifier_length_lt X l hl

/-!

## The definition of an index string

-/

/-- A string of indices to be associated with a tensor. For example, `ᵘ⁰ᵤ₂₆₀ᵘ³`. -/
def IndexString : Type := {s : String // listCharIndexStringBool X s.toList = true}

namespace IndexString

/-!

## Constructing a list of indices from an index string

-/

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]

/-- The character list associated with a index string. -/
def toCharList (s : IndexString X) : List Char := s.val.toList

/-- The char list of an index string satisfies `listCharIndexString`. -/
lemma listCharIndexString (s : IndexString X) : listCharIndexString X s.toCharList := by
  rw [listCharIndexString_iff_bool]
  exact s.prop

/-- The indices associated to an index string. -/
def toIndexList (s : IndexString X) : IndexList X :=
  {val := (listCharIndexStringTolistCharIndex X s.toCharList (listCharIndexString s)).map
    fun x => Index.ofCharList x.1 x.2}

/-- The formation of an index list from a string `s` statisfying `listCharIndexStringBool`. -/
def toIndexList' (s : String) (hs : listCharIndexStringBool X s.toList = true) : IndexList X :=
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
    (hs : listCharIndexStringBool 𝓣.toTensorColor.Color s.toList = true)
    (hn : n = (toIndexList' s hs).length)
    (hD : (toIndexList' s hs).withDual = (toIndexList' s hs).withUniqueDual)
    (hC : IndexList.ColorCond (toIndexList' s hs))
    (hd : TensorColor.ColorMap.DualMap (toIndexList' s hs).colorMap
      (cn ∘ Fin.cast hn.symm)) : 𝓣.TensorIndex :=
  TensorStructure.TensorIndex.mkDualMap T ⟨(toIndexList' s hs), hD, hC⟩ hn hd

end TensorIndex

end TensorStructure
