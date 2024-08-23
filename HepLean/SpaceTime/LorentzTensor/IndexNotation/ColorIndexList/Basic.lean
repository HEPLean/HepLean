/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Color
import HepLean.SpaceTime.LorentzTensor.IndexNotation.OnlyUniqueDuals
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
import HepLean.SpaceTime.LorentzTensor.Contraction
/-!

# Index lists and color

The main definiton of this file is `ColorIndexList`. This type defines the
permissible index lists which can be used for a tensor. These are lists of indices for which
every index with a dual has a unique dual, and the color of that dual (when it exists) is dual
to the color of the index.

We also define `AppendCond`, which is a condition on two `ColorIndexList`s which allows them to be
appended to form a new `ColorIndexList`.

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
  unique_duals : toIndexList.withDual = toIndexList.withUniqueDual
  /-- The condition that for an index with a dual, that dual has dual color to the index. -/
  dual_color : IndexList.ColorCond toIndexList

namespace ColorIndexList

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

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
  exact Eq.symm (Fin.orderEmbedding_eq (congrArg Set.range (id (Eq.symm h1))))

/-!

## Cons for `ColorIndexList`

-/

/-- The `ColorIndexList` whose underlying list of indices is empty. -/
def empty : ColorIndexList 𝓒 where
  val := []
  unique_duals := rfl
  dual_color := rfl

/-- The `ColorIndexList` obtained by adding an index, subject to some conditions,
  to the start of `l`. -/
def cons (I : Index 𝓒.Color) (hI1 : l.val.countP (fun J => I.id = J.id) ≤ 1)
    (hI2 : l.val.countP (fun J => I.id = J.id) =
    l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ J.toColor)) : ColorIndexList 𝓒 where
  toIndexList := l.toIndexList.cons I
  unique_duals := by
    symm
    rw [withUniqueDual_eq_withDual_cons_iff]
    · exact hI1
    · exact l.unique_duals.symm
  dual_color := by
    have h1 : (l.toIndexList.cons I).withUniqueDual = (l.toIndexList.cons I).withDual ∧
      (l.toIndexList.cons I).ColorCond := by
      rw [ColorCond.cons_iff]
      exact ⟨l.unique_duals.symm, l.dual_color, hI1, hI2⟩
    exact h1.2

/-- The tail of a `ColorIndexList`. In other words, the `ColorIndexList` with the first index
  removed. -/
def tail (l : ColorIndexList 𝓒) : ColorIndexList 𝓒 where
  toIndexList := l.toIndexList.tail
  unique_duals := by
    by_cases hl : l.toIndexList = {val := []}
    · rw [hl]
      simp [IndexList.tail]
      rfl
    · have hl' := l.head_cons_tail hl
      have h1 := l.unique_duals
      rw [hl'] at h1
      exact (withUniqueDual_eq_withDual_of_cons _ h1.symm).symm
  dual_color := by
    by_cases hl : l.toIndexList = {val := []}
    · rw [hl]
      simp [IndexList.tail]
      rfl
    · have hl' := l.head_cons_tail hl
      have h1 := l.unique_duals
      have h2 := l.dual_color
      rw [hl'] at h1 h2
      exact (ColorCond.of_cons _ h2 h1.symm)

@[simp]
lemma tail_toIndexList : l.tail.toIndexList = l.toIndexList.tail := by
  rfl

/-- The first index in a `ColorIndexList`. -/
def head (h : l ≠ empty) : Index 𝓒.Color :=
  l.toIndexList.head (by
    cases' l
    simpa [empty] using h)

lemma head_uniqueDual (h : l ≠ empty) :
    l.tail.val.countP (fun J => (l.head h).id = J.id) ≤ 1 := by
  have h1 := l.unique_duals.symm
  have hl : l.toIndexList = (l.tail.toIndexList.cons (l.head h)) := by
    simpa using l.head_cons_tail _
  rw [hl] at h1
  rw [withUniqueDual_eq_withDual_cons_iff'] at h1
  exact h1.2

lemma head_color_dual (h : l ≠ empty) :
    l.tail.val.countP (fun J => (l.head h).id = J.id) =
    l.tail.val.countP (fun J => (l.head h).id = J.id ∧ (l.head h).toColor = 𝓒.τ J.toColor) := by
  have h1 : l.withUniqueDual = l.withDual ∧ ColorCond l := ⟨l.unique_duals.symm, l.dual_color⟩
  have hl : l.toIndexList = (l.tail.toIndexList.cons (l.head h)) := by
    simpa using l.head_cons_tail _
  rw [hl, ColorCond.cons_iff] at h1
  exact h1.2.2.2

lemma head_cons_tail (h : l ≠ empty) :
    l = (l.tail).cons (l.head h) (l.head_uniqueDual h) (l.head_color_dual h) := by
  apply ext'
  exact IndexList.head_cons_tail _ _

/-!

## Induction for `ColorIndexList`

-/

lemma induction {P : ColorIndexList 𝓒 → Prop } (h_nil : P empty)
    (h_cons : ∀ (I : Index 𝓒.Color) (l : ColorIndexList 𝓒)
    (hI1 : l.val.countP (fun J => I.id = J.id) ≤ 1) (hI2 : l.val.countP (fun J => I.id = J.id) =
    l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ J.toColor)), P l → P (l.cons I hI1 hI2))
    (l : ColorIndexList 𝓒) : P l := by
  by_cases h : l = empty
  · subst l
    exact h_nil
  · rw [l.head_cons_tail h]
    refine h_cons (l.head h) (l.tail) (l.head_uniqueDual h) (l.head_color_dual h) ?_
    exact induction h_nil h_cons l.tail
termination_by l.length
decreasing_by {
  by_cases hn : l = empty
  · subst hn
    simp
    exact False.elim (h rfl)
  · have h1 : l.tail.length < l.length := by
      simp [IndexList.tail, length]
      by_contra hn'
      simp at hn'
      have hv : l = empty := ext hn'
      exact False.elim (hn hv)
    exact h1
}

end ColorIndexList
end IndexNotation
