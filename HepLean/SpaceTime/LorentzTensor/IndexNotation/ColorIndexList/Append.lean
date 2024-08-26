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

/-- If `AppendCond l l2` then `AppendCond l.contr l2`. Note that the inverse
  is generally not true. -/
lemma contr_left (h : AppendCond l l2) : AppendCond l.contr l2 := by
  apply And.intro (append_withDual_eq_withUniqueDual_contr_left l.toIndexList l2.toIndexList h.1)
  · rw [ColorCond.iff_countColorCond_all]
    · simp only [append_val, countId_append, List.all_append, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq]
      apply And.intro
      · intro I hI hI2
        have hIC1 : l.contr.countId I = 1 :=
          mem_contrIndexList_countId_contrIndexList l.toIndexList hI
        have hIC2 : l2.countId I = 1 := by omega
        obtain ⟨I1, hI1, hI1'⟩ := countId_neq_zero_mem l.contr I (by omega)
        apply ColorCond.countColorCond_of_filter_eq (l.toIndexList ++ l2.toIndexList) _ _
        · have h2 := h.2
          rw [ColorCond.iff_countColorCond_all] at h2
          · simp only [append_val, countId_append, List.all_append, Bool.and_eq_true, List.all_eq_true,
              decide_eq_true_eq] at h2
            have hn := h2.1 I (List.mem_of_mem_filter hI)
            have hc : l.countId I + l2.countId I = 2 := by
              rw [contr, countId_contrIndexList_eq_one_iff_countId_eq_one] at hIC1
              omega
            exact hn hc
          · exact h.1
        · erw [List.filter_append, List.filter_append]
          apply congrFun
          apply congrArg
          rw [countId_congr _ hI1'] at hIC1
          rw [hI1', filter_id_of_countId_eq_one_mem l.contr hI1 hIC1]
          simp [contr, contrIndexList] at hI1
          exact filter_id_of_countId_eq_one_mem l hI1.1 hI1.2
      · intro I hI1 hI2
        by_cases hICz : l2.countId I = 0
        · rw [hICz] at hI2
          have hx : l.contr.countId I ≤ 1 := countId_contrIndexList_le_one l.toIndexList I
          omega
        · by_cases hICo : l2.countId I = 1
          · have hIC1 : l.contr.countId I = 1 := by omega
            obtain ⟨I1, hI', hI1'⟩ := countId_neq_zero_mem l.contr I (by omega)
            apply ColorCond.countColorCond_of_filter_eq (l.toIndexList ++ l2.toIndexList) _ _
            · have h2 := h.2
              rw [ColorCond.iff_countColorCond_all] at h2
              · simp only [append_val, countId_append, List.all_append, Bool.and_eq_true, List.all_eq_true,
                  decide_eq_true_eq] at h2
                refine h2.2 I hI1 ?_
                rw [contr, countId_contrIndexList_eq_one_iff_countId_eq_one] at hIC1
                omega
              · exact h.1
            · erw [List.filter_append, List.filter_append]
              apply congrFun
              apply congrArg
              rw [hI1']
              rw [countId_congr _ hI1'] at hIC1
              rw [filter_id_of_countId_eq_one_mem l.contr hI' hIC1]
              simp [contr, contrIndexList] at hI'
              exact filter_id_of_countId_eq_one_mem l hI'.1 hI'.2
          · have hICt : l2.countId I = 2  := by
              omega
            apply ColorCond.countColorCond_of_filter_eq l2 _ _
            · have hl2C := l2.dual_color
              rw [ColorCond.iff_countColorCond_all] at hl2C
              · simp only [List.all_eq_true, decide_eq_true_eq] at hl2C
                exact hl2C I hI1 hICt
              · exact l2.unique_duals.symm
            · erw [List.filter_append]
              rw [filter_id_of_countId_eq_zero' l.contr.toIndexList]
              · rfl
              · omega
    · exact append_withDual_eq_withUniqueDual_contr_left l.toIndexList l2.toIndexList h.1

lemma contr_right (h : AppendCond l l2) : AppendCond l l2.contr := (contr_left h.symm).symm

lemma contr (h : AppendCond l l2) : AppendCond l.contr l2.contr := contr_left (contr_right h)

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

lemma countId_contr_fst_eq_zero_mem_snd (h : AppendCond l l2) {I : Index 𝓒.Color}
    (hI : I ∈ l2.val) : l.contr.countId I = 0 ↔ l.countId I = 0 := by
  rw [countId_contr_eq_zero_iff]
  refine Iff.intro (fun h' => ?_) (fun h' => ?_)
  · have h1 := h.1
    rw [withUniqueDual_eq_withDual_iff_countId_leq_two'] at h1
    have h1I := h1 I
    simp at h1I
    have h2 :  l2.countId I ≠ 0 := countId_mem l2.toIndexList I hI
    omega
  · simp [h']

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
