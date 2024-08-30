/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.ColorIndexList.Basic
import HepLean.SpaceTime.LorentzTensor.IndexNotation.ColorIndexList.Contraction
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
/-!

# Appending two ColorIndexLists

We define conditional appending of `ColorIndexList`'s.

It is conditional on `AppendCond` being true, which we define.

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
  (l.toIndexList ++ l2.toIndexList).OnlyUniqueDuals ∧ ColorCond (l.toIndexList ++ l2.toIndexList)

/-- Given two `ColorIndexList`s satisfying `AppendCond`. The correponding combined
  `ColorIndexList`. -/
def append (h : AppendCond l l2) : ColorIndexList 𝓒 where
  toIndexList := l.toIndexList ++ l2.toIndexList
  unique_duals := h.1
  dual_color := h.2

/-- The join of two `ColorIndexList` satisfying the condition `AppendCond` that they
  can be appended to form a `ColorIndexList`. -/
scoped[IndexNotation.ColorIndexList] notation l " ++["h"] " l2 => append l l2 h

@[simp]
lemma append_toIndexList (h : AppendCond l l2) :
    (l ++[h] l2).toIndexList = l.toIndexList ++ l2.toIndexList := rfl

namespace AppendCond

variable {l l2 l3 : ColorIndexList 𝓒}

@[symm]
lemma symm (h : AppendCond l l2) : AppendCond l2 l := by
  apply And.intro _ (h.2.symm h.1)
  rw [OnlyUniqueDuals.symm]
  exact h.1

lemma inr (h : AppendCond l l2) (h' : AppendCond (l ++[h] l2) l3) :
    AppendCond l2 l3 := by
  apply And.intro
  · have h1 := h'.1
    simp at h1
    rw [append_assoc] at h1
    exact OnlyUniqueDuals.inr h1
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
    apply OnlyUniqueDuals.swap
    simpa using h'.1
  · exact ColorCond.swap h'.1 h'.2

/-- If `AppendCond l l2` then `AppendCond l.contr l2`. Note that the inverse
  is generally not true. -/
lemma contr_left (h : AppendCond l l2) : AppendCond l.contr l2 :=
  And.intro (OnlyUniqueDuals.contrIndexList_left h.1) (ColorCond.contrIndexList_left h.1 h.2)

lemma contr_right (h : AppendCond l l2) : AppendCond l l2.contr := (contr_left h.symm).symm

lemma contr (h : AppendCond l l2) : AppendCond l.contr l2.contr := contr_left (contr_right h)

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
  simp only [bool, ite_not, Bool.if_false_right, Bool.and_eq_true, decide_eq_true_eq]
  rw [ColorCond.iff_bool]
  exact Eq.to_iff rfl

lemma countId_contr_fst_eq_zero_mem_snd (h : AppendCond l l2) {I : Index 𝓒.Color}
    (hI : I ∈ l2.val) : l.contr.countId I = 0 ↔ l.countId I = 0 := by
  rw [countId_contr_eq_zero_iff]
  have h1 := countId_mem l2.toIndexList I hI
  have h1I := h.1
  rw [OnlyUniqueDuals.iff_countId_leq_two'] at h1I
  have h1I' := h1I I
  simp at h1I'
  omega

lemma countId_contr_snd_eq_zero_mem_fst (h : AppendCond l l2) {I : Index 𝓒.Color}
    (hI : I ∈ l.val) : l2.contr.countId I = 0 ↔ l2.countId I = 0 := by
  exact countId_contr_fst_eq_zero_mem_snd h.symm hI

end AppendCond

lemma append_contr_left (h : AppendCond l l2) :
    (l.contr ++[h.contr_left] l2).contr = (l ++[h] l2).contr := by
  apply ext
  simp only [contr, append_toIndexList]
  rw [contrIndexList_append_eq_filter, contrIndexList_append_eq_filter,
    contrIndexList_contrIndexList]
  apply congrArg
  apply List.filter_congr
  intro I hI
  simp only [decide_eq_decide]
  simp [contrIndexList] at hI
  exact AppendCond.countId_contr_fst_eq_zero_mem_snd h hI.1

lemma append_contr_right (h : AppendCond l l2) :
    (l ++[h.contr_right] l2.contr).contr = (l ++[h] l2).contr := by
  apply ext
  simp [contr]
  rw [contrIndexList_append_eq_filter, contrIndexList_append_eq_filter,
    contrIndexList_contrIndexList]
  apply congrFun
  apply congrArg
  apply List.filter_congr
  intro I hI
  simp only [decide_eq_decide]
  simp only [contrIndexList, List.mem_filter, decide_eq_true_eq] at hI
  exact AppendCond.countId_contr_snd_eq_zero_mem_fst h hI.1

lemma append_contr (h : AppendCond l l2) :
    (l.contr ++[h.contr] l2.contr).contr = (l ++[h] l2).contr := by
  rw [append_contr_left, append_contr_right]

end ColorIndexList
end IndexNotation
