/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Set.Finite
import Mathlib.Logic.Equiv.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
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
structure IndexList where
  /-- The list of index values. For example `['ᵘ¹','ᵘ²','ᵤ₁']`. -/
  val : List (Index X)

namespace IndexList

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]

variable (l : IndexList X)

/-- The number of indices in an index list. -/
def length : ℕ := l.val.length

lemma ext (h : l.val = l2.val) : l = l2 := by
  cases l
  cases l2
  simp_all

/-- The index list constructed by prepending an index to the list. -/
def cons (i : Index X) : IndexList X := {val := i :: l.val}

@[simp]
lemma cons_val (i : Index X) : (l.cons i).val = i :: l.val := by
  rfl

@[simp]
lemma cons_length (i : Index X) : (l.cons i).length = l.length + 1 := by
  rfl

/-- The tail of an index list. That is, the index list with the first index dropped. -/
def tail : IndexList X := {val := l.val.tail}

@[simp]
lemma tail_val : l.tail.val = l.val.tail := by
  rfl

/-- The first index in a non-empty index list. -/
def head (h : l ≠ {val := ∅}) : Index X := l.val.head (by cases' l; simpa using h)

lemma head_cons_tail (h : l ≠ {val := ∅}) : l = (l.tail.cons (l.head h)) := by
  apply ext
  simp only [cons_val, tail_val]
  simp only [head, List.head_cons_tail]

lemma induction {P : IndexList X → Prop } (h_nil : P {val := ∅})
  (h_cons : ∀ (x : Index X) (xs : IndexList X), P xs → P (xs.cons x)) (l : IndexList X) : P l := by
  cases' l with val
  induction val with
  | nil => exact h_nil
  | cons x xs ih =>
    exact h_cons x ⟨xs⟩ ih

/-- The map of from `Fin s.numIndices` into colors associated to an index list. -/
def colorMap : Fin l.length → X :=
  fun i => (l.val.get i).toColor

/-- The map of from `Fin s.numIndices` into the natural numbers associated to an index list. -/
def idMap : Fin l.length → Nat :=
  fun i => (l.val.get i).id

lemma idMap_cast {l1 l2 : IndexList X} (h : l1 = l2) (i : Fin l1.length) :
    l1.idMap i = l2.idMap (Fin.cast (by rw [h]) i) := by
  subst h
  rfl

/-- Given a list of indices a subset of `Fin l.numIndices × Index X`
  of pairs of positions in `l` and the corresponding item in `l`. -/
def toPosSet (l : IndexList X) : Set (Fin l.length × Index X) :=
  {(i, l.val.get i) | i : Fin l.length}

/-- Equivalence between `toPosSet` and `Fin l.numIndices`. -/
def toPosSetEquiv (l : IndexList X) : l.toPosSet ≃ Fin l.length where
  toFun := fun x => x.1.1
  invFun := fun x => ⟨(x, l.val.get x), by simp [toPosSet]⟩
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

/-- Given a list of indices a finite set of `Fin l.length × Index X`
  of pairs of positions in `l` and the corresponding item in `l`. -/
def toPosFinset (l : IndexList X) : Finset (Fin l.length × Index X) :=
  l.toPosSet.toFinset

/-- The construction of a list of indices from a map
  from `Fin n` to `Index X`. -/
def fromFinMap {n : ℕ} (f : Fin n → Index X) : IndexList X where
  val := (Fin.list n).map f

@[simp]
lemma fromFinMap_numIndices {n : ℕ} (f : Fin n → Index X) :
    (fromFinMap f).length = n := by
  simp [fromFinMap, length]

/-!

## Appending index lists.

-/

section append

variable {X : Type} [IndexNotation X] [Fintype X] [DecidableEq X]
variable (l l2 l3 : IndexList X)

instance : HAppend (IndexList X) (IndexList X) (IndexList X) where
  hAppend := fun l l2 => {val := l.val ++ l2.val}

@[simp]
lemma cons_append (i : Index X) : (l.cons i) ++ l2 = (l ++ l2).cons i := by
  rfl

@[simp]
lemma append_length : (l ++ l2).length = l.length + l2.length := by
  simp [IndexList.length]
  exact List.length_append l.val l2.val

lemma append_assoc : l ++ l2 ++ l3 = l ++ (l2 ++ l3) := by
  apply ext
  change l.val ++ l2.val ++ l3.val = l.val ++ (l2.val ++ l3.val)
  exact List.append_assoc l.val l2.val l3.val

/-- An equivalence between the sum of the types of indices of `l` an `l2` and the type
  of indices of the joined index list `l ++ l2`. -/
def appendEquiv {l l2 : IndexList X} : Fin l.length ⊕ Fin l2.length ≃ Fin (l ++ l2).length :=
  finSumFinEquiv.trans (Fin.castOrderIso (List.length_append _ _).symm).toEquiv

/-- The inclusion of the indices of `l` into the indices of `l ++ l2`. -/
def appendInl : Fin l.length ↪ Fin (l ++ l2).length where
  toFun := appendEquiv ∘ Sum.inl
  inj' := by
    intro i j h
    simp [Function.comp] at h
    exact h

/-- The inclusion of the indices of `l2` into the indices of `l ++ l2`. -/
def appendInr : Fin l2.length ↪ Fin (l ++ l2).length where
  toFun := appendEquiv ∘ Sum.inr
  inj' := by
    intro i j h
    simp [Function.comp] at h
    exact h

@[simp]
lemma appendInl_appendEquiv :
    (l.appendInl l2).trans appendEquiv.symm.toEmbedding =
    {toFun := Sum.inl, inj' := Sum.inl_injective} := by
  ext i
  simp [appendInl]

@[simp]
lemma appendInr_appendEquiv :
    (l.appendInr l2).trans appendEquiv.symm.toEmbedding =
    {toFun := Sum.inr, inj' := Sum.inr_injective} := by
  ext i
  simp [appendInr]

@[simp]
lemma append_val {l l2 : IndexList X} : (l ++ l2).val = l.val ++ l2.val := by
  rfl

@[simp]
lemma idMap_append_inl {l l2 : IndexList X} (i : Fin l.length) :
    (l ++ l2).idMap (appendEquiv (Sum.inl i)) = l.idMap i := by
  simp [appendEquiv, idMap]
  rw [List.getElem_append_left]
  rfl

@[simp]
lemma idMap_append_inr {l l2 : IndexList X} (i : Fin l2.length) :
    (l ++ l2).idMap (appendEquiv (Sum.inr i)) = l2.idMap i := by
  simp [appendEquiv, idMap, IndexList.length]
  rw [List.getElem_append_right]
  · simp only [Nat.add_sub_cancel_left]
  · omega
  · omega

@[simp]
lemma colorMap_append_inl {l l2 : IndexList X} (i : Fin l.length) :
    (l ++ l2).colorMap (appendEquiv (Sum.inl i)) = l.colorMap i := by
  simp [appendEquiv, colorMap, IndexList.length]
  rw [List.getElem_append_left]

@[simp]
lemma colorMap_append_inl' :
    (l ++ l2).colorMap ∘ appendEquiv ∘ Sum.inl = l.colorMap := by
  funext i
  simp

@[simp]
lemma colorMap_append_inr {l l2 : IndexList X} (i : Fin l2.length) :
    (l ++ l2).colorMap (appendEquiv (Sum.inr i)) = l2.colorMap i := by
  simp [appendEquiv, colorMap, IndexList.length]
  rw [List.getElem_append_right]
  · simp only [Nat.add_sub_cancel_left]
  · omega
  · omega

@[simp]
lemma colorMap_append_inr' :
    (l ++ l2).colorMap ∘ appendEquiv ∘ Sum.inr = l2.colorMap := by
  funext i
  simp

lemma colorMap_sumELim (l1 l2 : IndexList X) :
    Sum.elim l1.colorMap l2.colorMap =
    (l1 ++ l2).colorMap ∘ appendEquiv := by
  funext x
  match x with
  | Sum.inl i => simp
  | Sum.inr i => simp

end append

/-!

## countId

-/

/-- The number of times the id of an index `I` appears in a list of indices `l`. -/
def countId (I : Index X) : ℕ :=
  l.val.countP (fun J => I.id = J.id)

@[simp]
lemma countId_append (I : Index X) : (l ++ l2).countId I = l.countId I + l2.countId I := by
  simp [countId]

lemma countId_eq_length_filter (I : Index X) :
    l.countId I = (l.val.filter (fun J => I.id = J.id)).length := by
  simp [countId]
  rw [List.countP_eq_length_filter]

lemma countId_index_neq_zero (i : Fin l.length) : l.countId (l.val.get i) ≠ 0 := by
  rw [countId_eq_length_filter]
  by_contra hn
  rw [List.length_eq_zero] at hn
  have hm : l.val.get i ∈ List.filter (fun J => decide ((l.val.get i).id = J.id)) l.val := by
    simpa using List.getElem_mem l.val i.1 i.isLt
  rw [hn] at hm
  simp at hm

lemma countId_append_symm (I : Index X) : (l ++ l2).countId I = (l2 ++ l).countId I := by
  simp only [countId_append]
  omega

lemma countId_eq_one_append_mem_right_self_eq_one {I : Index X} (hI : I ∈ l2.val)
    (h : (l ++ l2).countId I = 1) : l2.countId I = 1 := by
  simp at h
  have hmem : I ∈ l2.val.filter (fun J => I.id = J.id) := by
    simp [List.mem_filter, decide_True, and_true, hI]
  have h1 : l2.countId I ≠ 0 := by
    rw [countId_eq_length_filter]
    by_contra hn
    rw [@List.length_eq_zero] at hn
    rw [hn] at hmem
    simp at hmem
  omega

lemma countId_eq_one_append_mem_right_other_eq_zero {I : Index X} (hI : I ∈ l2.val)
    (h : (l ++ l2).countId I = 1) : l.countId I = 0 := by
  simp at h
  have hmem : I ∈ l2.val.filter (fun J => I.id = J.id) := by
    simp [List.mem_filter, decide_True, and_true, hI]
  have h1 : l2.countId I ≠ 0 := by
    rw [countId_eq_length_filter]
    by_contra hn
    rw [@List.length_eq_zero] at hn
    rw [hn] at hmem
    simp at hmem
  omega

@[simp]
lemma countId_cons_eq_two {I : Index X} :
    (l.cons I).countId I = 2 ↔ l.countId I = 1 := by
  simp [countId]

lemma countId_congr {I J : Index X} (h : I.id = J.id) : l.countId I = l.countId J := by
  simp [countId, h]

lemma countId_neq_zero_mem (I : Index X) (h : l.countId I ≠ 0) :
    ∃ I', I' ∈ l.val ∧ I.id = I'.id := by
  rw [countId_eq_length_filter] at h
  have h' := List.isEmpty_iff_length_eq_zero.mp.mt h
  simp only at h'
  have h'' := eq_false_of_ne_true h'
  rw [List.isEmpty_false_iff_exists_mem] at h''
  obtain ⟨I', hI'⟩ := h''
  simp only [List.mem_filter, decide_eq_true_eq] at hI'
  exact ⟨I', hI'⟩


/-!

## Filter id

-/
/-! TODO: Replace with Mathlib lemma. -/
lemma filter_sort_comm {n : ℕ} (s : Finset (Fin n)) (p : Fin n → Prop) [DecidablePred p] :
    List.filter p (Finset.sort (fun i j => i ≤ j) s) =
    Finset.sort (fun i j => i ≤ j) (Finset.filter p s) := by
  simp [Finset.filter, Finset.sort]
  have : ∀ (m : Multiset (Fin n)), List.filter p (Multiset.sort (fun i j => i ≤ j) m) =
      Multiset.sort (fun i j => i ≤ j) (Multiset.filter p m) := by
    apply Quot.ind
    intro m
    simp [List.mergeSort]
    have h1 : List.Sorted (fun i j => i ≤ j) (List.filter (fun b => decide (p b))
        (List.mergeSort (fun i j => i ≤ j) m)) := by
      simp [List.Sorted]
      rw [List.pairwise_filter]
      rw [@List.pairwise_iff_get]
      intro i j h1 _ _
      have hs : List.Sorted (fun i j => i ≤ j) (List.mergeSort (fun i j => i ≤ j) m) := by
        exact List.sorted_mergeSort (fun i j => i ≤ j) m
      simp [List.Sorted] at hs
      rw [List.pairwise_iff_get] at hs
      exact hs i j h1
    have hp1 : (List.mergeSort (fun i j => i ≤ j) m).Perm m := by
      exact List.perm_mergeSort (fun i j => i ≤ j) m
    have hp2 : (List.filter (fun b => decide (p b)) ((List.mergeSort (fun i j => i ≤ j) m))).Perm
        (List.filter (fun b => decide (p b)) m) := by
      exact List.Perm.filter (fun b => decide (p b)) hp1
    have hp3 : (List.filter (fun b => decide (p b)) m).Perm
      (List.mergeSort (fun i j => i ≤ j) (List.filter (fun b => decide (p b)) m)) := by
      exact List.Perm.symm (List.perm_mergeSort (fun i j => i ≤ j)
      (List.filter (fun b => decide (p b)) m))
    have hp4 := hp2.trans hp3
    refine List.eq_of_perm_of_sorted hp4 h1 ?_
    exact List.sorted_mergeSort (fun i j => i ≤ j) (List.filter (fun b => decide (p b)) m)
  exact this s.val

lemma filter_id_eq_sort (i : Fin l.length) : l.val.filter (fun J => (l.val.get i).id = J.id) =
    List.map l.val.get (Finset.sort (fun i j => i ≤ j)
      (Finset.filter (fun j => l.idMap i = l.idMap j) Finset.univ)) := by
  have h1 := (List.finRange_map_get l.val).symm
  have h2 : l.val = List.map l.val.get (Finset.sort (fun i j => i ≤ j) Finset.univ) := by
    nth_rewrite 1 [h1, (Fin.sort_univ l.val.length).symm]
    rfl
  nth_rewrite 3 [h2]
  rw [List.filter_map]
  apply congrArg
  rw [← filter_sort_comm]
  apply List.filter_congr
  intro x _
  simp [idMap]

end IndexList

end IndexNotation
