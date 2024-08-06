/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Sort
/-!

# Index notation for a type

In this file we will define an index of a Lorentz tensor as a
string satisfying certain properties.

For example, the string `ᵘ¹²` is an index of a real Lorentz tensors.
The first character `ᵘ` specifies the color of the index, and the subsequent characters
`¹²` specify the id of the index.

Strings of indices e.g. `ᵘ¹²ᵤ₄₃`` are defined elsewhere.

-/

open Lean
open String

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

/-!

## Lists of characters forming an index

Here we define `listCharIndex` and properties thereof.

-/

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

/-- An auxillary rewrite lemma to prove that `listCharIndex` is decidable. -/
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

/-!

## The definition of an index and its properties

-/

/-- An index is a non-empty string satisfying the condtion `listCharIndex`,
  e.g. `ᵘ¹²` or `ᵤ₄₃` etc. -/
def Index : Type := {s : String // listCharIndex X s.toList ∧ s.toList ≠ []}

instance : DecidableEq (Index X) := Subtype.instDecidableEq

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

/-!

## List of indices

-/

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

lemma idMap_cast {l1 l2 : IndexList X} (h : l1 = l2) (i : Fin l1.numIndices) :
    l1.idMap i = l2.idMap (Fin.cast (by rw [h]) i) := by
  subst h
  rfl

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

instance : HAppend (IndexList X) (IndexList X) (IndexList X) :=
    @instHAppendOfAppend (List (Index X)) List.instAppend

/-- The construction of a list of indices from a map
  from `Fin n` to `Index X`. -/
def fromFinMap {n : ℕ} (f : Fin n → Index X) : IndexList X :=
  (Fin.list n).map f

@[simp]
lemma fromFinMap_numIndices {n : ℕ} (f : Fin n → Index X) :
    (fromFinMap f).numIndices = n := by
  simp [fromFinMap, numIndices]

/-!

## Contracted and non-contracting indices

-/

/-- The proposition on a element (or really index of element) of a index list
  `s` which is ture iff does not share an id with any other element.
  This tells us that it should not be contracted with any other element. -/
def NoContr (i : Fin l.length) : Prop :=
  ∀ j, i ≠ j → l.idMap i ≠ l.idMap j

instance (i : Fin l.length) : Decidable (l.NoContr i) :=
  Fintype.decidableForallFintype

/-- The finset of indices of an index list corresponding to elements which do not contract. -/
def noContrFinset : Finset (Fin l.length) :=
  Finset.univ.filter l.NoContr

/-- An eqiuvalence between the subtype of indices of a index list `l` which do not contract and
  `Fin l.noContrFinset.card`. -/
def noContrSubtypeEquiv : {i : Fin l.length // l.NoContr i} ≃ Fin l.noContrFinset.card :=
  (Equiv.subtypeEquivRight (fun x => by simp [noContrFinset])).trans
  (Finset.orderIsoOfFin l.noContrFinset rfl).toEquiv.symm

@[simp]
lemma idMap_noContrSubtypeEquiv_neq (i j : Fin l.noContrFinset.card) (h : i ≠ j) :
    l.idMap (l.noContrSubtypeEquiv.symm i).1 ≠ l.idMap (l.noContrSubtypeEquiv.symm j).1 := by
  have hi := ((l.noContrSubtypeEquiv).symm i).2
  simp [NoContr] at hi
  have hj := hi ((l.noContrSubtypeEquiv).symm j)
  apply hj
  rw [@SetCoe.ext_iff]
  erw [Equiv.apply_eq_iff_eq]
  exact h

/-- The subtype of indices `l` which do contract. -/
def contrSubtype : Type := {i : Fin l.length // ¬ l.NoContr i}

instance : Fintype l.contrSubtype :=
  Subtype.fintype fun x => ¬ l.NoContr x

instance : DecidableEq l.contrSubtype :=
  Subtype.instDecidableEq

/-!

## Getting the index which contracts with a given index

-/

/-- Given a `i : l.contrSubtype` the proposition on a `j` in `Fin s.length` for
  it to be an index of `s` contracting with `i`. -/
def getDualProp (i j : Fin l.length) : Prop :=
    i ≠ j ∧ l.idMap i = l.idMap j

instance (i j : Fin l.length) :
    Decidable (l.getDualProp i j) :=
  instDecidableAnd

/-- Given a `i : l.contrSubtype` the index of `s` contracting with `i`. -/
def getDualFin (i : l.contrSubtype) : Fin l.length :=
  (Fin.find (l.getDualProp i.1)).get (by simpa [NoContr, Fin.isSome_find_iff] using i.prop)

lemma some_getDualFin_eq_find (i : l.contrSubtype) :
    Fin.find (l.getDualProp i.1) = some (l.getDualFin i) := by
  simp [getDualFin]

lemma getDualFin_not_NoContr (i : l.contrSubtype) : ¬ l.NoContr (l.getDualFin i) := by
  have h := l.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h
  simp [NoContr]
  exact ⟨i.1, And.intro (fun a => h.1.1 a.symm) h.1.2.symm⟩

/-- The dual index of an element of `𝓒.contrSubtype s`, that is the index
  contracting with it. -/
def getDual (i : l.contrSubtype) : l.contrSubtype :=
  ⟨l.getDualFin i, l.getDualFin_not_NoContr i⟩

lemma getDual_id (i : l.contrSubtype) : l.idMap i.1 = l.idMap (l.getDual i).1 := by
  simp [getDual]
  have h1 := l.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h1
  simp only [getDualProp, ne_eq, and_imp] at h1
  exact h1.1.2

lemma getDual_neq_self (i : l.contrSubtype) : i ≠ l.getDual i := by
  have h1 := l.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h1
  exact ne_of_apply_ne Subtype.val h1.1.1

lemma getDual_getDualProp (i : l.contrSubtype) : l.getDualProp i.1 (l.getDual i).1 := by
  simp [getDual]
  have h1 := l.some_getDualFin_eq_find i
  rw [Fin.find_eq_some_iff] at h1
  simp only [getDualProp, ne_eq, and_imp] at h1
  exact h1.1

/-!

## Index lists with no contracting indices

-/

/-- The proposition on a `IndexList` for it to have no contracting
  indices. -/
def HasNoContr : Prop := ∀ i, l.NoContr i

lemma contrSubtype_is_empty_of_hasNoContr (h : l.HasNoContr) : IsEmpty l.contrSubtype := by
  rw [_root_.isEmpty_iff]
  intro a
  exact h a.1 a.1 (fun _ => a.2 (h a.1)) rfl

lemma hasNoContr_id_inj (h : l.HasNoContr) : Function.Injective l.idMap := fun i j => by
  simpa using (h i j).mt

lemma hasNoContr_color_eq_of_id_eq (h : l.HasNoContr) (i j : Fin l.length) :
    l.idMap i = l.idMap j → l.colorMap i = l.colorMap j := by
  intro h1
  apply l.hasNoContr_id_inj h at h1
  rw [h1]

@[simp]
lemma hasNoContr_noContrFinset_card (h : l.HasNoContr) :
    l.noContrFinset.card = List.length l := by
  simp only [noContrFinset]
  rw [Finset.filter_true_of_mem]
  simp
  intro x _
  exact h x

/-!

## The contracted index list

-/

/-- The index list of those indices of `l` which do not contract. -/
def contrIndexList : IndexList X :=
  IndexList.fromFinMap (fun i => l.get (l.noContrSubtypeEquiv.symm i))

@[simp]
lemma contrIndexList_numIndices : l.contrIndexList.numIndices = l.noContrFinset.card := by
  simp [contrIndexList]

@[simp]
lemma contrIndexList_idMap_apply (i : Fin l.contrIndexList.numIndices) :
    l.contrIndexList.idMap i =
    l.idMap (l.noContrSubtypeEquiv.symm (Fin.cast (by simp) i)).1 := by
  simp [contrIndexList, IndexList.fromFinMap, IndexList.idMap]
  rfl

lemma contrIndexList_hasNoContr : HasNoContr l.contrIndexList := by
  intro i
  simp [NoContr]
  intro j h
  refine l.idMap_noContrSubtypeEquiv_neq _ _ ?_
  rw [@Fin.ne_iff_vne]
  simp only [Fin.coe_cast, ne_eq]
  exact Fin.val_ne_of_ne h

/-- Contracting indices on a index list that has no contractions does nothing. -/
@[simp]
lemma contrIndexList_of_hasNoContr (h : HasNoContr l) : l.contrIndexList = l := by
  simp only [contrIndexList, List.get_eq_getElem]
  have hn : (@Finset.univ (Fin (List.length l)) (Fin.fintype (List.length l))).card =
      (Finset.filter l.NoContr Finset.univ).card := by
    rw [Finset.filter_true_of_mem (fun a _ => h a)]
  have hx : (Finset.filter l.NoContr Finset.univ).card = (List.length l) := by
    rw [← hn]
    exact Finset.card_fin (List.length l)
  apply List.ext_get
  simpa [fromFinMap, noContrFinset] using hx
  intro n h1 h2
  simp only [noContrFinset, noContrSubtypeEquiv, OrderIso.toEquiv_symm, Equiv.symm_trans_apply,
    RelIso.coe_fn_toEquiv, Equiv.subtypeEquivRight_symm_apply_coe, fromFinMap, List.get_eq_getElem,
    OrderIso.symm_symm, Finset.coe_orderIsoOfFin_apply, List.getElem_map, Fin.getElem_list,
    Fin.cast_mk]
  simp only [Finset.filter_true_of_mem (fun a _ => h a)]
  congr
  rw [(Finset.orderEmbOfFin_unique' _
    (fun x => Finset.mem_univ ((Fin.castOrderIso hx).toOrderEmbedding x))).symm]
  rfl

/-- Applying contrIndexlist is equivalent to applying it once. -/
@[simp]
lemma contrIndexList_contrIndexList : l.contrIndexList.contrIndexList = l.contrIndexList :=
  l.contrIndexList.contrIndexList_of_hasNoContr (l.contrIndexList_hasNoContr)

/-!

## Pairs of contracting indices

-/

/-- The set of contracting ordered pairs of indices. -/
def contrPairSet : Set (l.contrSubtype × l.contrSubtype) :=
  {p | p.1.1 < p.2.1 ∧ l.idMap p.1.1 = l.idMap p.2.1}

instance : DecidablePred fun x => x ∈ l.contrPairSet := fun _ =>
  And.decidable

instance : Fintype l.contrPairSet := setFintype _

lemma contrPairSet_isEmpty_of_hasNoContr (h : l.HasNoContr) :
    IsEmpty l.contrPairSet := by
  simp only [contrPairSet, Subtype.coe_lt_coe, Set.coe_setOf, isEmpty_subtype, not_and, Prod.forall]
  refine fun a b h' =>  h a.1 b.1 (Fin.ne_of_lt h')


lemma getDual_lt_self_mem_contrPairSet {i : l.contrSubtype}
    (h : (l.getDual i).1 < i.1) : (l.getDual i, i) ∈ l.contrPairSet :=
  And.intro h (l.getDual_id i).symm

lemma getDual_not_lt_self_mem_contrPairSet {i : l.contrSubtype}
    (h : ¬ (l.getDual i).1 < i.1) : (i, l.getDual i) ∈ l.contrPairSet := by
  apply And.intro
  have h1 := l.getDual_neq_self i
  simp only [Subtype.coe_lt_coe, gt_iff_lt]
  simp at h
  exact lt_of_le_of_ne h h1
  simp only
  exact l.getDual_id i

/-- The list of elements of `l` which contract together. -/
def contrPairList : List (Fin l.length × Fin l.length) :=
  (List.product (Fin.list l.length) (Fin.list l.length)).filterMap fun (i, j) => if
  l.getDualProp i j then some (i, j) else none

end IndexList

end IndexNotation
