/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Basic
/-!

# Index lists

i.e. lists of indices.

-/

namespace IndexNotation

variable (X : Type) [IndexNotation X]
variable [Fintype X] [DecidableEq X]

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
