/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.ColorIndexList.Basic
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
/-!

# Appending two ColorIndexLists

We define the contraction of ColorIndexLists.

-/

namespace IndexNotation
namespace ColorIndexList

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
  (l l2 : ColorIndexList 𝓒)

open IndexList TensorColor

/-!

## Append

-/

/-- The condition on the `ColorIndexList`s `l` and `l2` so that on appending they form
  a `ColorIndexList`.

  Note: `AppendCond` does not form an equivalence relation as it is not reflexive or
  transitive. -/
def AppendCond : Prop :=
  (l.toIndexList ++ l2.toIndexList).withUniqueDual = (l.toIndexList ++ l2.toIndexList).withDual
  ∧ ColorCond (l.toIndexList ++ l2.toIndexList)

/-- Given two `ColorIndexList`s satisfying `AppendCond`. The correponding combined
  `ColorIndexList`. -/
def append (h : AppendCond l l2) : ColorIndexList 𝓒 where
  toIndexList := l.toIndexList ++ l2.toIndexList
  unique_duals := h.1.symm
  dual_color := h.2

/-- The join of two `ColorIndexList` satisfying the condition `AppendCond` that they
  can be appended to form a `ColorIndexList`. -/
scoped[IndexNotation.ColorIndexList] notation l " ++["h"] " l2 => append l l2 h

@[simp]
lemma append_toIndexList (h : AppendCond l l2) :
    (l ++[h] l2).toIndexList = l.toIndexList ++ l2.toIndexList := by
  rfl

namespace AppendCond

variable {l l2 l3 : ColorIndexList 𝓒}

@[symm]
lemma symm (h : AppendCond l l2) : AppendCond l2 l := by
  apply And.intro _ (h.2.symm h.1)
  rw [append_withDual_eq_withUniqueDual_symm]
  exact h.1

lemma inr (h : AppendCond l l2) (h' : AppendCond (l ++[h] l2) l3) :
    AppendCond l2 l3 := by
  apply And.intro
  · have h1 := h'.1
    simp at h1
    rw [append_assoc] at h1
    exact l.append_withDual_eq_withUniqueDual_inr (l2.toIndexList ++ l3.toIndexList) h1
  · have h1 := h'.2
    simp at h1
    rw [append_assoc] at h1
    refine ColorCond.inr ?_ h1
    rw [← append_assoc]
    exact h'.1

lemma assoc (h : AppendCond l l2) (h' : AppendCond (l ++[h] l2) l3) :
    AppendCond l (l2 ++[h.inr h'] l3) := by
  apply And.intro
  · simp
    rw [← append_assoc]
    simpa using h'.1
  · simp
    rw [← append_assoc]
    exact h'.2

lemma swap (h : AppendCond l l2) (h' : AppendCond (l ++[h] l2) l3) :
    AppendCond (l2 ++[h.symm] l) l3:= by
  apply And.intro
  · simp only [append_toIndexList]
    rw [← append_withDual_eq_withUniqueDual_swap]
    simpa using h'.1
  · exact ColorCond.swap h'.1 h'.2

/-! TODO: Show that `AppendCond l l2` implies `AppendCond l.contr l2.contr`. -/
/-! TODO: Show that `(l1.contr ++[h.contr] l2.contr).contr = (l1 ++[h] l2)` -/

lemma of_eq (h1 : l.withUniqueDual = l.withDual)
    (h2 : l2.withUniqueDual = l2.withDual)
    (h3 : l.withUniqueDualInOther l2 = l.withDualInOther l2)
    (h4 : l2.withUniqueDualInOther l = l2.withDualInOther l)
    (h5 : ColorCond.bool (l.toIndexList ++ l2.toIndexList)) :
    AppendCond l l2 := by
  rw [AppendCond]
  rw [append_withDual_eq_withUniqueDual_iff']
  simp_all
  exact ColorCond.iff_bool.mpr h5

/-- A boolean which is true for two index lists `l` and `l2` if on appending
  they can form a `ColorIndexList`. -/
def bool (l l2 : IndexList 𝓒.Color) : Bool :=
  if ¬ (l ++ l2).withUniqueDual = (l ++ l2).withDual then
    false
  else
    ColorCond.bool (l ++ l2)

lemma bool_iff (l l2 : IndexList 𝓒.Color) :
    bool l l2 ↔ (l ++ l2).withUniqueDual = (l ++ l2).withDual ∧ ColorCond.bool (l ++ l2) := by
  simp [bool]

lemma iff_bool (l l2 : ColorIndexList 𝓒) : AppendCond l l2 ↔ bool l.toIndexList l2.toIndexList := by
  rw [AppendCond]
  simp [bool]
  rw [ColorCond.iff_bool]
  simp

end AppendCond

end ColorIndexList
end IndexNotation
