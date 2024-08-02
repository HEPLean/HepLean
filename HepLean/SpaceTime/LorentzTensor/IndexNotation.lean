/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Real.Basic
import Init.NotationExtra
/-!

# Notation for Lorentz Tensors

This file is currently a stub.

We plan to set up index-notation for dealing with tensors.

Some examples:

- `ψᵘ¹ᵘ²φᵤ₁` should correspond to the contraction of the first index of `ψ` and the
  only index of `φ`.
- `ψᵘ¹ᵘ² = ψᵘ²ᵘ¹` should define the symmetry of `ψ` under the exchange of its indices.
- `θᵤ₂(ψᵘ¹ᵘ²φᵤ₁) = (θᵤ₂ψᵘ¹ᵘ²)φᵤ₁` should correspond to an associativity properity of
  contraction.

It should also be possible to define this generically for any `LorentzTensorStructure`.

Further we plan to make easy to define tensors with indices. E.g. `(ψ : Tenᵘ¹ᵘ²ᵤ₃)`
  should correspond to a (real Lorentz) tensors with 3 indices, two upper and one lower.
  For `(ψ : Tenᵘ¹ᵘ²ᵤ₃)`, if one writes e.g. `ψᵤ₁ᵘ²ᵤ₃`, this should correspond to a
  lowering of the first index of `ψ`.

Further, it will be nice if we can have implicit contractions of indices
  e.g. in Weyl fermions.

-/
open Lean
open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Command
variable {R : Type} [CommSemiring R]

/-- The class defining index notation on a type `X`.
  Normally `X` will be taken as the type of colors of a `TensorStructure`. -/
class IndexNotation (X : Type) where
  /-- The list of characters describing the index notation e.g.
    `{'ᵘ', 'ᵤ'}` for real tensors. -/
  charList : Finset Char
  /-- An equivalence between `X` (colors of indices) and `charList`.
    This takes every color of index to its notation character. -/
  notaEquiv : X ≃ charList

namespace IndexNotation

variable (X : Type) [IndexNotation X]
variable [Fintype X] [DecidableEq X]

/-- The map taking a color to its notation character. -/
def nota {X : Type} [IndexNotation X] (x : X) : Char :=
  (IndexNotation.notaEquiv).toFun x

/-- A character is a `notation character` if it is in `charList`. -/
def isNotationChar (c : Char) : Bool :=
  if c ∈ charList X then true else false

/-- A character is a numeric superscript if it is e.g. `⁰`, `¹`, etc. -/
def isNumericSupscript (c : Char) : Bool :=
  c = '¹' ∨ c = '²' ∨ c = '³' ∨ c = '⁴' ∨ c = '⁵' ∨ c = '⁶' ∨ c = '⁷' ∨ c = '⁸' ∨ c = '⁹' ∨ c = '⁰'

/-- Given a character `f` which is a notation character, this is true if `c`
  is a subscript when `f` is a subscript or `c` is a superscript when `f` is a
  superscript. -/
def IsIndexId (f : Char) (c : Char) : Bool :=
  (isSubScriptAlnum f ∧ isNumericSubscript c) ∨
  (¬ isSubScriptAlnum f ∧ isNumericSupscript c)

open String

/-!

## Lists of characters corresponding to indices.

-/

/-- The proposition for a list of characters to be the tail of an index
  e.g. `['¹', '⁷', ...]` -/
def listCharIndexTail (f : Char) (l : List Char) : Prop :=
  l ≠ [] ∧ List.all l (fun c => IsIndexId f c)

instance : Decidable (listCharIndexTail f l) := instDecidableAnd

/-- The proposition for a list of characters to be the characters of an index
  e.g. `['ᵘ', '¹', '⁷', ...]` -/
def listCharIndex (l : List Char) : Prop :=
  if h : l = [] then True
  else
    let sfst := l.head h
    if ¬ isNotationChar X sfst then False
    else
      listCharIndexTail sfst l.tail

lemma listCharIndex_iff (l : List Char) : listCharIndex X l
    ↔ (if h : l = [] then True else
    let sfst := l.head h
    if ¬ isNotationChar X sfst then False
    else listCharIndexTail sfst l.tail) := by
  rw [listCharIndex]

instance : Decidable (listCharIndex X l) :=
  @decidable_of_decidable_of_iff _ _
    (@instDecidableDite _ _ _ _ _ <|
        fun _ => @instDecidableDite _ _ _ _ _ <|
        fun _ => instDecidableListCharIndexTail)
      (listCharIndex_iff X l).symm

lemma dropWhile_isIndexSpecifier_length_lt (l : List Char) (hl : l ≠ []) :
    (List.dropWhile (fun c => !isNotationChar X c) l.tail).length < l.length := by
  let ld := l.tail.dropWhile (fun c => ¬ isNotationChar X c)
  let lt := l.tail.takeWhile (fun c => ¬ isNotationChar X c)
  simp only [gt_iff_lt]
  rename_i _ inst_1 _ _
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
  rename_i _ _ _ _ x
  simp_all only [not_true_eq_false, Bool.not_eq_true, Bool.decide_eq_false, ite_not, if_false_right,
    ite_false, dite_false]
  obtain ⟨left, _⟩ := h
  simp [listCharIndexStringHeadIndexTail] at x
  simp_all only [Bool.false_eq_true]

/-- The first list of characters which form a index, from a list of characters
  which form a string of indices. -/
def listCharIndexStringHeadIndex (l : List Char) : List Char :=
  if h : l = [] then []
  else l.head h :: listCharIndexStringHeadIndexTail X l

/-- The list of characters obtained by dropping the first block which
  corresponds to an index. -/
def listCharIndexStringDropHeadIndex (l : List Char) : List Char :=
  l.tail.dropWhile (fun c => ¬ isNotationChar X c)

lemma listCharIndexStringHeadIndex_listCharIndex (l : List Char) (h : listCharIndexString X l) :
    listCharIndex X (listCharIndexStringHeadIndex X l) := by
  by_cases h1 : l = []
  · subst h1
    simp [listCharIndex, listCharIndexStringHeadIndex]
  · simp [listCharIndexStringHeadIndex, listCharIndex, h1]
    apply And.intro
    exact listCharIndexString_head_isIndexSpecifier X l h h1
    exact listCharIndexStringHeadIndexTail_listCharIndexTail X l h h1

lemma listCharIndexStringDropHeadIndex_listCharIndexString (l : List Char)
    (h : listCharIndexString X l) :
    listCharIndexString X (listCharIndexStringDropHeadIndex X l) := by
  by_cases h1 : l = []
  · subst h1
    simp [listCharIndexStringDropHeadIndex, listCharIndexString]
  · simp [listCharIndexStringDropHeadIndex, h1]
    rw [listCharIndexString] at h
    rename_i _ inst_1 _ _
    simp_all only [↓reduceDIte, Bool.not_eq_true, Bool.decide_eq_false, ite_not, if_false_right,
      if_false_left, Bool.not_eq_false]

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

## Index and index strings
-/

/-- An index is a non-empty string satisfying the condtion `listCharIndex`,
  e.g. `ᵘ¹²` or `ᵤ₄₃` etc. -/
def Index : Type := {s : String // listCharIndex X s.toList ∧ s.toList ≠ []}

namespace Index

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]

/-- Creats an index from a non-empty list of characters satisfying `listCharIndex`. -/
def ofCharList (l : List Char) (h : listCharIndex X l ∧ l ≠ []) : Index X := ⟨l.asString, h⟩

instance : ToString (Index X) := ⟨fun i => i.val⟩

/-- Gets the first character in an index e.g. `ᵘ` as an element of `charList X`. -/
def head (s : Index X) : charList X :=
  ⟨s.val.toList.head (s.prop.2), by
    have h := s.prop.1
    have h2 := s.prop.2
    simp [listCharIndex] at h
    simp_all only [toList, ne_eq, Bool.not_eq_true, ↓reduceDIte]
    simpa [isNotationChar] using h.1⟩

/-- The color associated to an index. -/
def toColor (s : Index X) : X := (IndexNotation.notaEquiv).invFun s.head

/-- A map from super and subscript numerical characters to the natural numbers,
  returning `0` on all other characters. -/
def charToNat (c : Char) : Nat :=
  match c with
  | '₀' => 0
  | '₁' => 1
  | '₂' => 2
  | '₃' => 3
  | '₄' => 4
  | '₅' => 5
  | '₆' => 6
  | '₇' => 7
  | '₈' => 8
  | '₉' => 9
  | '⁰' => 0
  | '¹' => 1
  | '²' => 2
  | '³' => 3
  | '⁴' => 4
  | '⁵' => 5
  | '⁶' => 6
  | '⁷' => 7
  | '⁸' => 8
  | '⁹' => 9
  | _ => 0

/-- The numerical characters associated with an index. -/
def tail (s : Index X) : List Char := s.val.toList.tail

/-- The natural numbers assocaited with an index. -/
def tailNat (s : Index X) : List Nat := s.tail.map charToNat

/-- The id of an index, as a natural number. -/
def id (s : Index X) : Nat := s.tailNat.foldl (fun a b => 10 * a + b) 0

end Index

/-- The type of lists of indices. -/
def IndexList : Type := List (Index X)

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]

variable (l : IndexList X)
/-- The number of indices in an index list. -/
def numIndices : Nat := l.length

/-- The map of from `Fin s.numIndices` into colors associated to an index list. -/
def colorMap : Fin l.numIndices → X :=
  fun i => (l.get i).toColor

/-- The map of from `Fin s.numIndices` into the natural numbers associated to an index list. -/
def idMap : Fin l.numIndices → Nat :=
  fun i => (l.get i).id

/-- Given a list of indices a subset of `Fin l.numIndices × Index X`
  of pairs of positions in `l` and the corresponding item in `l`. -/
def toPosSet (l : IndexList X) : Set (Fin l.numIndices × Index X) :=
  {(i, l.get i) | i : Fin l.numIndices}

/-- Equivalence between `toPosSet` and `Fin l.numIndices`. -/
def toPosSetEquiv (l : IndexList X) : l.toPosSet ≃ Fin l.numIndices where
  toFun := fun x => x.1.1
  invFun := fun x => ⟨(x, l.get x), by simp [toPosSet]⟩
  left_inv x := by
    have hx := x.prop
    simp [toPosSet] at hx
    simp only [List.get_eq_getElem]
    obtain ⟨i, hi⟩ := hx
    have hi2 : i = x.1.1 := by
      obtain ⟨val, property⟩ := x
      obtain ⟨fst, snd⟩ := val
      simp_all only [Prod.mk.injEq]
    subst hi2
    simp_all only [Subtype.coe_eta]
  right_inv := by
    intro x
    rfl

lemma toPosSet_is_finite (l : IndexList X) : l.toPosSet.Finite :=
  Finite.intro l.toPosSetEquiv

instance : Fintype l.toPosSet where
  elems := Finset.map l.toPosSetEquiv.symm.toEmbedding Finset.univ
  complete := by
    intro x
    simp_all only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_univ]

/-- Given a list of indices a finite set of `Fin l.numIndices × Index X`
  of pairs of positions in `l` and the corresponding item in `l`. -/
def toPosFinset (l : IndexList X) : Finset (Fin l.numIndices × Index X) :=
  l.toPosSet.toFinset

end IndexList

/-- A string of indices to be associated with a tensor.
  E.g. `ᵘ⁰ᵤ₂₆₀ᵘ³`. -/
def IndexString : Type := {s : String // listCharIndexStringBool X s.toList = true}

namespace IndexString

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]

/-- The character list associated with a index string. -/
def toCharList (s : IndexString X) : List Char := s.val.toList

/-- The char list of an index string satisfies `listCharIndexString`. -/
lemma listCharIndexString (s : IndexString X) : listCharIndexString X s.toCharList := by
  rw [listCharIndexString_iff_bool]
  exact s.prop

/-- The indices associated to an index string. -/
def toIndexList (s : IndexString X) : IndexList X :=
  (listCharIndexStringTolistCharIndex X s.toCharList (listCharIndexString s)).map
  fun x => Index.ofCharList x.1 x.2

end IndexString

end IndexNotation

instance : IndexNotation realTensorColor.Color where
  charList := {'ᵘ', 'ᵤ'}
  notaEquiv :=
    {toFun := fun x =>
        match x with
        | .up => ⟨'ᵘ', by decide⟩
        | .down => ⟨'ᵤ', by decide⟩,
      invFun := fun x =>
        match x with
        | ⟨'ᵘ', _⟩ => .up
        | ⟨'ᵤ', _⟩ => .down
        | _ => .up,
      left_inv := by
        intro x
        fin_cases x <;> rfl,
      right_inv := by
        intro x
        fin_cases x <;> rfl}

namespace TensorColor

variable {n m : ℕ}

variable {R : Type} [CommSemiring R] (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color}
  {cW : W → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}
  {cn : Fin n → 𝓣.Color} {cm : Fin m → 𝓣.Color}

variable (𝓒 : TensorColor)
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

open IndexNotation

/-- The proposition on an `i : Fin s.length` such the corresponding element of
  `s` does not contract with any other element (i.e. share an index). -/
def NoContr (s : IndexList 𝓒.Color) (i : Fin s.length) : Prop :=
  ∀ j, i ≠ j → s.idMap i ≠ s.idMap j

instance (i : Fin s.length) : Decidable (NoContr 𝓒 s i) :=
  Fintype.decidableForallFintype

/-- The finset of indices of `s` corresponding to elements which do not contract. -/
def noContrFinset (s : IndexList 𝓒.Color) : Finset (Fin s.length) :=
  Finset.univ.filter (𝓒.NoContr s)

/-- An eqiuvalence between the subtype of indices of `s` which do not contract and
  `Fin _`. -/
def noContrSubtypeEquiv (s : IndexList 𝓒.Color) :
    {i : Fin s.length // NoContr 𝓒 s i} ≃ Fin (𝓒.noContrFinset s).card :=
  (Equiv.subtypeEquivRight (by
    intro x
    simp only [noContrFinset, Finset.mem_filter, Finset.mem_univ, true_and])).trans
  (Finset.orderIsoOfFin (𝓒.noContrFinset s) (by rfl)).toEquiv.symm

/-- The subtype of indices `s` which do contract. -/
def contrSubtype (s : IndexList 𝓒.Color) : Type :=
  {i : Fin s.length // ¬ NoContr 𝓒 s i}

instance (s : IndexList 𝓒.Color) : Fintype (𝓒.contrSubtype s) :=
  Subtype.fintype fun x => ¬𝓒.NoContr s x

instance (s : IndexList 𝓒.Color) : DecidableEq (𝓒.contrSubtype s) :=
  Subtype.instDecidableEq

/-- Given a `i : 𝓒.contrSubtype s` the proposition on a `j` in `Fin s.length` for
  it to be an index of `s` contracting with `i`. -/
def getDualProp {s : IndexList 𝓒.Color} (i : 𝓒.contrSubtype s) (j : Fin s.length) : Prop :=
    i.1 ≠ j ∧ s.idMap i.1 = s.idMap j

instance {s : IndexList 𝓒.Color} (i : 𝓒.contrSubtype s) (j : Fin s.length) :
    Decidable (𝓒.getDualProp i j) :=
  instDecidableAnd

/-- Given a `i : 𝓒.contrSubtype s` the index of `s` contracting with `i`. -/
def getDualFin {s : IndexList 𝓒.Color} (i : 𝓒.contrSubtype s) : Fin s.length :=
  (Fin.find (𝓒.getDualProp i)).get (by simpa [NoContr, Fin.isSome_find_iff] using i.prop)

lemma some_getDualFin_eq_find {s : IndexList 𝓒.Color} (i : 𝓒.contrSubtype s) :
    Fin.find (𝓒.getDualProp i) = some (getDualFin 𝓒 i) := by
  simp [getDualFin]

lemma getDualFin_not_NoContr {s : IndexList 𝓒.Color} (i : 𝓒.contrSubtype s) :
    ¬ NoContr 𝓒 s (getDualFin 𝓒 i) := by
  have h := 𝓒.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h
  simp [NoContr]
  exact ⟨i.1, And.intro (fun a => h.1.1 a.symm) h.1.2.symm⟩

/-- The dual index of an element of `𝓒.contrSubtype s`, that is the index
  contracting with it. -/
def getDual {s : IndexList 𝓒.Color} (i : 𝓒.contrSubtype s) : 𝓒.contrSubtype s :=
  ⟨getDualFin 𝓒 i, getDualFin_not_NoContr 𝓒 i⟩

lemma getDual_id {s : IndexList 𝓒.Color} (i : 𝓒.contrSubtype s) :
    s.idMap i.1 = s.idMap (getDual 𝓒 i).1 := by
  simp [getDual]
  have h1 := 𝓒.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h1
  simp only [getDualProp, ne_eq, and_imp] at h1
  exact h1.1.2

lemma getDual_neq_self {s : IndexList 𝓒.Color} (i : 𝓒.contrSubtype s) :
    i ≠ 𝓒.getDual i := by
  have h1 := 𝓒.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h1
  exact ne_of_apply_ne Subtype.val h1.1.1

/-- An index list is allowed if every contracting index has exactly one dual,
  and the color of the dual is dual to the color of the index. -/
def AllowedIndexString (s : IndexList 𝓒.Color) : Prop :=
  (∀ (i j : 𝓒.contrSubtype s), 𝓒.getDualProp i j.1 → j = 𝓒.getDual i) ∧
  (∀ (i : 𝓒.contrSubtype s), s.colorMap i.1 = 𝓒.τ (s.colorMap (𝓒.getDual i).1))

@[simp]
lemma getDual_getDual {s : IndexList 𝓒.Color} (h : 𝓒.AllowedIndexString s) (i : 𝓒.contrSubtype s) :
    getDual 𝓒 (getDual 𝓒 i) = i := by
  refine (h.1 (getDual 𝓒 i) i ?_).symm
  simp [getDualProp]
  apply And.intro
  exact Subtype.coe_ne_coe.mpr (getDual_neq_self 𝓒 i).symm
  exact (getDual_id 𝓒 i).symm

/-- The set of contracting ordered pairs of indices. -/
def contrPairSet (s : IndexList 𝓒.Color) : Set (𝓒.contrSubtype s × 𝓒.contrSubtype s) :=
  {p | p.1.1 < p.2.1 ∧ s.idMap p.1.1 = s.idMap p.2.1}

lemma getDual_lt_self_mem_contrPairSet {s : IndexList 𝓒.Color} {i : 𝓒.contrSubtype s}
    (h : (getDual 𝓒 i).1 < i.1) : (getDual 𝓒 i, i) ∈ 𝓒.contrPairSet s :=
  And.intro h (𝓒.getDual_id i).symm

lemma getDual_not_lt_self_mem_contrPairSet {s : IndexList 𝓒.Color} {i : 𝓒.contrSubtype s}
    (h : ¬ (getDual 𝓒 i).1 < i.1) : (i, getDual 𝓒 i) ∈ 𝓒.contrPairSet s := by
  apply And.intro
  have h1 := 𝓒.getDual_neq_self i
  simp only [Subtype.coe_lt_coe, gt_iff_lt]
  simp at h
  exact lt_of_le_of_ne h h1
  simp only
  exact getDual_id 𝓒 i

lemma contrPairSet_fst_eq_dual_snd {s : IndexList 𝓒.Color} (h : 𝓒.AllowedIndexString s)
    (x : 𝓒.contrPairSet s) : x.1.1 = getDual 𝓒 x.1.2 :=
  (h.1 (x.1.2) x.1.1 (And.intro (Fin.ne_of_gt x.2.1) x.2.2.symm))

lemma contrPairSet_snd_eq_dual_fst {s : IndexList 𝓒.Color} (h : 𝓒.AllowedIndexString s)
    (x : 𝓒.contrPairSet s) : x.1.2 = getDual 𝓒 x.1.1 := by
  rw [contrPairSet_fst_eq_dual_snd, getDual_getDual]
  exact h
  exact h

lemma contrPairSet_dual_snd_lt_self {s : IndexList 𝓒.Color} (h : 𝓒.AllowedIndexString s)
    (x : 𝓒.contrPairSet s) : (getDual 𝓒 x.1.2).1 < x.1.2.1 := by
  rw [← 𝓒.contrPairSet_fst_eq_dual_snd h]
  exact x.2.1

/-- An equivalence between two coppies of `𝓒.contrPairSet s` and `𝓒.contrSubtype s`.
  This equivalence exists due to the ordering on pairs in `𝓒.contrPairSet s`. -/
def contrPairEquiv {s : IndexList 𝓒.Color} (h : 𝓒.AllowedIndexString s) :
    𝓒.contrPairSet s ⊕ 𝓒.contrPairSet s ≃ 𝓒.contrSubtype s where
  toFun x :=
    match x with
    | Sum.inl p => p.1.2
    | Sum.inr p => p.1.1
  invFun x :=
    if h : (𝓒.getDual x).1 < x.1 then
      Sum.inl ⟨(𝓒.getDual x, x), 𝓒.getDual_lt_self_mem_contrPairSet h⟩
    else
      Sum.inr ⟨(x, 𝓒.getDual x), 𝓒.getDual_not_lt_self_mem_contrPairSet h⟩
  left_inv x := by
    match x with
    | Sum.inl x =>
      simp only [Subtype.coe_lt_coe]
      rw [dif_pos]
      simp [← 𝓒.contrPairSet_fst_eq_dual_snd h]
      exact 𝓒.contrPairSet_dual_snd_lt_self h _
    | Sum.inr x =>
      simp only [Subtype.coe_lt_coe]
      rw [dif_neg]
      simp only [← 𝓒.contrPairSet_snd_eq_dual_fst h, Prod.mk.eta, Subtype.coe_eta]
      rw [← 𝓒.contrPairSet_snd_eq_dual_fst h]
      have h1 := x.2.1
      simp only [not_lt, ge_iff_le]
      exact le_of_lt h1
  right_inv x := by
    by_cases h1 : (getDual 𝓒 x).1 < x.1
    simp only [h1, ↓reduceDIte]
    simp only [h1, ↓reduceDIte]

@[simp]
lemma contrPairEquiv_apply_inr {s : IndexList 𝓒.Color} (h : 𝓒.AllowedIndexString s)
    (x : 𝓒.contrPairSet s) : 𝓒.contrPairEquiv h (Sum.inr x) = x.1.1 := by
  simp [contrPairEquiv]

@[simp]
lemma contrPairEquiv_apply_inl {s : IndexList 𝓒.Color} (h : 𝓒.AllowedIndexString s)
    (x : 𝓒.contrPairSet s) : 𝓒.contrPairEquiv h (Sum.inl x) = x.1.2 := by
  simp [contrPairEquiv]

/-- An equivalence between `Fin s.length` and
  `(𝓒.contrPairSet s ⊕ 𝓒.contrPairSet s) ⊕ Fin (𝓒.noContrFinset s).card`, which
  can be used for contractions. -/
def splitContr {s : IndexList 𝓒.Color} (h : 𝓒.AllowedIndexString s) :
    Fin s.length ≃ (𝓒.contrPairSet s ⊕ 𝓒.contrPairSet s) ⊕ Fin (𝓒.noContrFinset s).card :=
  (Equiv.sumCompl (𝓒.NoContr s)).symm.trans <|
  (Equiv.sumComm { i // 𝓒.NoContr s i} { i // ¬ 𝓒.NoContr s i}).trans <|
  Equiv.sumCongr (𝓒.contrPairEquiv h).symm (𝓒.noContrSubtypeEquiv s)

lemma splitContr_map {s : IndexList 𝓒.Color} (hs : 𝓒.AllowedIndexString s) :
    s.colorMap ∘ (𝓒.splitContr hs).symm ∘ Sum.inl ∘ Sum.inl =
    𝓒.τ ∘ s.colorMap ∘ (𝓒.splitContr hs).symm ∘ Sum.inl ∘ Sum.inr := by
  funext x
  simp [splitContr, contrPairEquiv_apply_inr]
  erw [contrPairEquiv_apply_inr, contrPairEquiv_apply_inl]
  rw [contrPairSet_fst_eq_dual_snd _ hs]
  exact hs.2 _

end TensorColor
/-
def testIndex : Index realTensorColor.Color := ⟨"ᵘ¹", by decide⟩

def testIndexString : IndexString realTensorColor.Color := ⟨"ᵘ⁰ᵤ₀ᵘ⁰", by rfl⟩

#eval realTensorColor.AllowedIndexString testIndexString.toIndexList
-/
