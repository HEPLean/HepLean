/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.Contraction
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.OnlyUniqueDuals
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
/-!

# Index lists and color

In this file we look at the interaction of index lists and color.

The main definition of this file is `ColorCond`.
-/

namespace IndexNotation

namespace Index

variable {𝓒 : TensorColor}
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
variable (I : Index 𝓒.Color)

/-- The dual of an index is the index with the same id, but opposite color. -/
def dual : Index 𝓒.Color := ⟨𝓒.τ I.toColor, I.id⟩

@[simp]
lemma dual_dual : I.dual.dual = I := by
  simp [dual, toColor, id]
  rw [𝓒.τ_involutive]
  rfl

@[simp]
lemma dual_id : I.dual.id = I.id := by
  simp [dual, id]

@[simp]
lemma dual_color : I.dual.toColor = 𝓒.τ I.toColor := by
  simp [dual, toColor]

end Index

namespace IndexList

variable {𝓒 : TensorColor}
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
variable (l l2 l3 : IndexList 𝓒.Color)

def countColorQuot (I : Index 𝓒.Color) : ℕ := l.val.countP (fun J => I = J ∨ I.dual = J)

lemma countColorQuot_eq_filter_id_countP (I : Index 𝓒.Color) :
    l.countColorQuot I =
    (l.val.filter (fun J => I.id = J.id)).countP
    (fun J => I.toColor = J.toColor ∨ I.toColor = 𝓒.τ (J.toColor)) := by
  simp [countColorQuot]
  rw [List.countP_filter]
  apply List.countP_congr
  intro I' _
  simp [Index.eq_iff_color_eq_and_id_eq]
  apply Iff.intro
  · intro a_1
    cases a_1 with
    | inl h => simp_all only [true_or, and_self]
    | inr h_1 =>
      simp_all only [and_true]
      obtain ⟨left, _⟩ := h_1
      rw [← left]
      rw [𝓒.τ_involutive]
      simp
  · intro a_1
    simp_all only [and_true]
    obtain ⟨left, _⟩ := a_1
    cases left with
    | inl h => simp_all only [true_or]
    | inr h_1 =>
      simp_all only
      rw [𝓒.τ_involutive]
      simp

lemma countColorQuot_eq_filter_color_countP (I : Index 𝓒.Color) :
    l.countColorQuot I = (l.val.filter (fun J =>  I.toColor = J.toColor ∨ I.toColor = 𝓒.τ (J.toColor))).countP
    (fun J =>  I.id = J.id) := by
  rw [countColorQuot_eq_filter_id_countP]
  rw [List.countP_filter, List.countP_filter]
  apply List.countP_congr
  intro I' _
  simpa using And.comm

@[simp]
lemma countColorQuot_append (I : Index 𝓒.Color) :
    (l ++ l2).countColorQuot I = countColorQuot l I + countColorQuot l2 I := by
  simp [countColorQuot]

lemma countColorQuot_eq_countId_iff_of_isSome (hl : l.OnlyUniqueDuals) (i : Fin l.length)
    (hi : (l.getDual? i).isSome) :
    l.countColorQuot (l.val.get i) = l.countId (l.val.get i) ↔
    (l.colorMap i = l.colorMap ((l.getDual? i).get hi) ∨
    l.colorMap i = 𝓒.τ (l.colorMap ((l.getDual? i).get hi))) := by
  rw [countColorQuot_eq_filter_id_countP, countId_eq_length_filter]
  have hi1 := hi
  rw [← mem_withDual_iff_isSome, ← hl, mem_withUniqueDual_iff_countId_eq_two] at hi1
  rcases l.filter_id_of_countId_eq_two hi1 with hf | hf
  all_goals
    erw [hf]
    simp [List.countP, List.countP.go]
    refine Iff.intro (fun h => ?_) (fun h => ?_)
    · by_contra hn
      have hn' : (decide (l.val[↑i].toColor = l.val[↑((l.getDual? i).get hi)].toColor) ||
        decide (l.val[↑i].toColor = 𝓒.τ l.val[↑((l.getDual? i).get hi)].toColor)) = false := by
        simpa using hn
      erw [hn'] at h
      simp at h
    · have hn' : (decide (l.val[↑i].toColor = l.val[↑((l.getDual? i).get hi)].toColor) ||
        decide (l.val[↑i].toColor = 𝓒.τ l.val[↑((l.getDual? i).get hi)].toColor)) = true := by
        simpa using h
      erw [hn']
      simp

lemma countColorQuot_of_countId_zero {I : Index 𝓒.Color} (h : l.countId I = 0) :
    l.countColorQuot I = 0 := by
  rw [countColorQuot_eq_filter_id_countP]
  rw [countId_eq_length_filter, List.length_eq_zero] at h
  simp [h, countColorQuot]

lemma countColorQuot_le_countId (I : Index 𝓒.Color) :
    l.countColorQuot I ≤ l.countId I := by
  rw [countColorQuot_eq_filter_color_countP, countId]
  apply List.Sublist.countP_le
  exact List.filter_sublist l.val

lemma countColorQuot_contrIndexList_le_one (I : Index 𝓒.Color) :
    l.contrIndexList.countColorQuot I ≤ 1 :=
  (l.contrIndexList.countColorQuot_le_countId I).trans
  (countId_contrIndexList_le_one l I)

lemma countColorQuot_contrIndexList_eq_zero_or_one (I : Index 𝓒.Color) :
    l.contrIndexList.countColorQuot I = 0 ∨ l.contrIndexList.countColorQuot I = 1 := by
  have h1 := countColorQuot_contrIndexList_le_one l I
  omega

lemma countColorQuot_contrIndexList_le_countColorQuot (I : Index 𝓒.Color) :
    l.contrIndexList.countColorQuot I ≤ l.countColorQuot I := by
  rw [countColorQuot_eq_filter_color_countP, countColorQuot_eq_filter_color_countP]
  apply List.Sublist.countP_le
  exact List.Sublist.filter _ (List.filter_sublist l.val)

lemma countColorQuot_contrIndexList_eq_of_countId_eq
    (h1 : l.contrIndexList.countId I = l.countId I) :
    l.contrIndexList.countColorQuot I = l.countColorQuot I := by
  rw [countColorQuot_eq_filter_id_countP,
    l.filter_id_contrIndexList_eq_of_countId_contrIndexList I h1,
    countColorQuot_eq_filter_id_countP]

def countSelf (I : Index 𝓒.Color) : ℕ := l.val.countP (fun J => I = J)

lemma countSelf_eq_filter_id_countP : l.countSelf I =
    (l.val.filter (fun J => I.id = J.id)).countP (fun J => I.toColor = J.toColor) := by
  simp [countSelf]
  rw [List.countP_filter]
  apply List.countP_congr
  intro I' _
  simp [Index.eq_iff_color_eq_and_id_eq]

lemma countSelf_eq_filter_color_countP :
  l.countSelf I =
    (l.val.filter (fun J => I.toColor = J.toColor)).countP (fun J => I.id = J.id) := by
  simp [countSelf]
  rw [List.countP_filter]
  apply List.countP_congr
  intro I' _
  simpa [Index.eq_iff_color_eq_and_id_eq] using And.comm

lemma countSelf_of_countId_zero {I : Index 𝓒.Color} (h : l.countId I = 0) :
    l.countSelf I = 0 := by
  rw [countId_eq_length_filter, List.length_eq_zero] at h
  simp [h, countSelf_eq_filter_id_countP]

lemma countSelf_count (I : Index 𝓒.Color) : l.countSelf I = l.val.count I := by
  rw [countSelf, List.count]
  apply List.countP_congr
  intro I' _
  simp
  exact eq_comm

lemma countSelf_eq_zero (I : Index 𝓒.Color) : l.countSelf I = 0 ↔ I ∉ l.val := by
  rw [countSelf_count]
  exact List.count_eq_zero

lemma countSelf_neq_zero (I : Index 𝓒.Color) : l.countSelf I ≠ 0 ↔ I ∈ l.val := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · simpa using (l.countSelf_eq_zero I).mpr.mt h
  · exact (l.countSelf_eq_zero I).mp.mt (by simpa using h)

@[simp]
lemma countSelf_append (I : Index 𝓒.Color) :
    (l ++ l2).countSelf I = countSelf l I + countSelf l2 I := by
  simp [countSelf]

lemma countSelf_le_countId (I : Index 𝓒.Color) :
    l.countSelf I ≤ l.countId I := by
  rw [countSelf_eq_filter_color_countP, countId]
  apply List.Sublist.countP_le
  exact List.filter_sublist l.val

lemma countSelf_eq_one_of_countId_eq_one (I : Index 𝓒.Color) (h1 : l.countId I = 1)
    (hme : I ∈ l.val) : l.countSelf I = 1 := by
  rw [countSelf_eq_filter_id_countP]
  rw [filter_id_of_countId_eq_one_mem l hme h1]
  simp

lemma countSelf_contrIndexList_le_one (I : Index 𝓒.Color) :
    l.contrIndexList.countSelf I ≤ 1 :=
  (l.contrIndexList.countSelf_le_countId I).trans (countId_contrIndexList_le_one l I)

lemma countSelf_contrIndexList_eq_zero_or_one (I : Index 𝓒.Color) :
    l.contrIndexList.countSelf I = 0 ∨ l.contrIndexList.countSelf I = 1 := by
  have h1 := countSelf_contrIndexList_le_one l I
  omega

lemma countSelf_contrIndexList_eq_zero_of_zero (I : Index 𝓒.Color) (h : l.countSelf I = 0) :
    l.contrIndexList.countSelf I = 0 := by
  rw [countSelf_eq_zero] at h ⊢
  simp_all [contrIndexList]

lemma countSelf_contrIndexList_le_countSelf (I : Index 𝓒.Color) :
    l.contrIndexList.countSelf I ≤ l.countSelf I := by
  rw [countSelf_eq_filter_color_countP, countSelf_eq_filter_color_countP]
  apply List.Sublist.countP_le
  exact List.Sublist.filter _ (List.filter_sublist l.val)

lemma countSelf_contrIndexList_eq_of_countId_eq
    (h1 : l.contrIndexList.countId I = l.countId I) :
    l.contrIndexList.countSelf I = l.countSelf I := by
  rw [countSelf_eq_filter_id_countP,
    l.filter_id_contrIndexList_eq_of_countId_contrIndexList I h1,
    countSelf_eq_filter_id_countP]

@[simp]
lemma countSelf_contrIndexList_get (i : Fin l.contrIndexList.length) :
    l.contrIndexList.countSelf l.contrIndexList.val[Fin.val i] = 1 := by
  refine countSelf_eq_one_of_countId_eq_one _ _ ?h1 ?hme
  · refine mem_contrIndexList_countId_contrIndexList l ?_
    exact List.getElem_mem l.contrIndexList.val (↑i) _
  · exact List.getElem_mem l.contrIndexList.val (↑i) _

def countDual (I : Index 𝓒.Color) : ℕ := l.val.countP (fun J => I.dual = J)

lemma countDual_eq_countSelf_Dual (I : Index 𝓒.Color) : l.countDual I = l.countSelf I.dual := by
  rw [countDual, countSelf]

lemma countDual_eq_filter_id_countP : l.countDual I =
    (l.val.filter (fun J => I.id = J.id)).countP (fun J => I.toColor = 𝓒.τ (J.toColor)) := by
  simp [countDual]
  rw [List.countP_filter]
  apply List.countP_congr
  intro I' _
  simp [Index.eq_iff_color_eq_and_id_eq, Index.dual, Index.toColor, Index.id]
  intro _
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [← h]
    exact (𝓒.τ_involutive _).symm
  · rw [h]
    exact (𝓒.τ_involutive _)

lemma countDual_of_countId_zero {I : Index 𝓒.Color} (h : l.countId I = 0) :
    l.countDual I = 0 := by
  rw [countId_eq_length_filter, List.length_eq_zero] at h
  simp [h, countDual_eq_filter_id_countP]

@[simp]
lemma countDual_append (I : Index 𝓒.Color) :
    (l ++ l2).countDual I = countDual l I + countDual l2 I := by
  simp [countDual]

lemma countDual_contrIndexList_eq_of_countId_eq
    (h1 : l.contrIndexList.countId I = l.countId I) :
    l.contrIndexList.countDual I = l.countDual I := by
  rw [countDual_eq_countSelf_Dual, countDual_eq_countSelf_Dual]
  refine countSelf_contrIndexList_eq_of_countId_eq l h1

lemma countSelf_eq_countDual_iff_of_isSome (hl : l.OnlyUniqueDuals)
    (i : Fin l.length) (hi : (l.getDual? i).isSome) :
    l.countSelf (l.val.get i) = l.countDual (l.val.get i) ↔
    l.colorMap i = 𝓒.τ (l.colorMap ((l.getDual? i).get hi))
    ∨ (l.colorMap i) = 𝓒.τ (l.colorMap i) := by
  rw [countSelf_eq_filter_id_countP, countDual_eq_filter_id_countP]
  have hi1 := hi
  rw [← mem_withDual_iff_isSome, ← hl, mem_withUniqueDual_iff_countId_eq_two] at hi1
  rcases l.filter_id_of_countId_eq_two hi1 with hf | hf
  all_goals
    erw [hf]
    simp [List.countP, List.countP.go]
    by_cases hn : l.colorMap i = 𝓒.τ (l.colorMap ((l.getDual? i).get hi))
    · simp [hn]
      have hn' : decide (l.val[↑i].toColor = 𝓒.τ l.val[↑((l.getDual? i).get hi)].toColor)
        = true := by simpa [colorMap] using hn
      erw [hn']
      simp only [cond_true]
      have hτ : l.colorMap ((l.getDual? i).get hi) = 𝓒.τ (l.colorMap i) := by
        rw [hn]
        exact (𝓒.τ_involutive _).symm
      simp [colorMap] at hτ
      erw [hτ]
    · have hn' : decide (l.val[↑i].toColor = 𝓒.τ l.val[↑((l.getDual? i).get hi)].toColor) =
          false := by simpa [colorMap] using hn
      erw [hn']
      simp [hn]
      by_cases hm : l.colorMap i = 𝓒.τ (l.colorMap i)
      · trans True
        · simp
          have hm' : decide (l.val[↑i].toColor = 𝓒.τ l.val[↑i].toColor) = true := by simpa using hm
          erw [hm']
          simp only [cond_true]
          have hm'' : decide (l.val[↑i].toColor = l.val[↑((l.getDual? i).get hi)].toColor)
              = false := by
            simp only [Fin.getElem_fin, decide_eq_false_iff_not]
            simp [colorMap] at hm
            erw [hm]
            by_contra hn'
            have hn'' : l.colorMap i = 𝓒.τ (l.colorMap ((l.getDual? i).get hi)) := by
              simp [colorMap]
              rw [← hn']
              exact (𝓒.τ_involutive _).symm
            exact hn hn''
          erw [hm'']
          simp
        · exact true_iff_iff.mpr hm
      · simp [hm]
        simp [colorMap] at hm
        have hm' : decide (l.val[↑i].toColor = 𝓒.τ l.val[↑i].toColor) = false := by simpa using hm
        erw [hm']
        simp only [cond_false, ne_eq]
        by_cases hm'' : decide (l.val[↑i].toColor = l.val[↑((l.getDual? i).get hi)].toColor) = true
        · erw [hm'']
          simp
        · have hm''' : decide (l.val[↑i].toColor = l.val[↑((l.getDual? i).get hi)].toColor)
              = false := by
            simpa using hm''
          erw [hm''']
          simp

/-- The condition an index and its' dual, when it exists, have dual colors. -/
def ColorCond : Prop := Option.map l.colorMap ∘
  l.getDual? = Option.map (𝓒.τ ∘ l.colorMap) ∘
  Option.guard fun i => (l.getDual? i).isSome

namespace ColorCond

variable {l l2 l3 : IndexList 𝓒.Color}

lemma iff_withDual :
    l.ColorCond ↔ ∀ (i : l.withDual), 𝓒.τ
    (l.colorMap ((l.getDual? i).get (l.withDual_isSome i))) = l.colorMap i := by
  refine Iff.intro (fun h i => ?_) (fun h => ?_)
  · have h' := congrFun h i
    simp at h'
    rw [show l.getDual? i = some ((l.getDual? i).get (l.withDual_isSome i)) by simp] at h'
    have h'' : (Option.guard (fun i => (l.getDual? i).isSome = true) ↑i) = i := by
      apply Option.guard_eq_some.mpr
      simp [l.withDual_isSome i]
    rw [h'', Option.map_some', Option.map_some'] at h'
    simp at h'
    rw [h']
    exact 𝓒.τ_involutive (l.colorMap i)
  · funext i
    by_cases hi : (l.getDual? i).isSome
    · have h'' : (Option.guard (fun i => (l.getDual? i).isSome = true) ↑i) = i := by
        apply Option.guard_eq_some.mpr
        simp only [true_and]
        exact hi
      simp only [Function.comp_apply, h'', Option.map_some']
      rw [show l.getDual? ↑i = some ((l.getDual? i).get hi) by simp]
      rw [Option.map_some']
      simp only [Option.some.injEq]
      have hii := h ⟨i, by simp [withDual, hi]⟩
      simp at hii
      rw [← hii]
      exact (𝓒.τ_involutive _).symm
    · simp [Option.guard, hi]
      exact Option.not_isSome_iff_eq_none.mp hi

lemma iff_on_isSome : l.ColorCond ↔ ∀ (i : Fin l.length) (h : (l.getDual? i).isSome), 𝓒.τ
    (l.colorMap ((l.getDual? i).get h)) = l.colorMap i := by
  rw [iff_withDual]
  simp only [Subtype.forall, mem_withDual_iff_isSome]

/-- A condition on an index list `l` and and index `I`. If the id of `I` appears
twice in `l` (and `I` at least once) then this condition is equivalent to the dual of `I` having
dual color to `I`, but written totally in terms of lists. -/
@[simp]
abbrev countColorCond (l : IndexList 𝓒.Color) (I : Index 𝓒.Color) : Prop :=
    l.countColorQuot I = l.countId I ∧
    l.countSelf I = l.countDual I

lemma countColorCond_of_filter_eq (l l2 : IndexList 𝓒.Color) {I : Index 𝓒.Color}
    (hf : l.val.filter (fun J => I.id = J.id) = l2.val.filter (fun J => I.id = J.id))
    (h1 : countColorCond l I) : countColorCond l2 I := by
  rw [countColorCond, countColorQuot_eq_filter_id_countP, countId_eq_length_filter, countSelf_eq_filter_id_countP,
    countDual_eq_filter_id_countP, ← hf]
  rw [countColorCond, countColorQuot_eq_filter_id_countP, countId_eq_length_filter, countSelf_eq_filter_id_countP,
    countDual_eq_filter_id_countP] at h1
  exact h1

lemma iff_countColorCond_isSome (hl : l.OnlyUniqueDuals) : l.ColorCond ↔
    ∀ (i : Fin l.length) (_ : (l.getDual? i).isSome), countColorCond l (l.val.get i) := by
  rw [iff_on_isSome]
  simp only [countColorCond]
  refine Iff.intro (fun h i hi => ?_) (fun h i hi => ?_)
  · rw [l.countColorQuot_eq_countId_iff_of_isSome hl i hi,
      l.countSelf_eq_countDual_iff_of_isSome hl i hi]
    have hi' := h i hi
    exact And.intro (Or.inr hi'.symm) (Or.inl hi'.symm)
  · have hi' := h i hi
    rw [l.countColorQuot_eq_countId_iff_of_isSome hl i hi,
      l.countSelf_eq_countDual_iff_of_isSome hl i hi] at hi'
    rcases hi'.1 with hi1 | hi1
      <;> rcases hi'.2 with hi2 | hi2
    · exact hi2.symm
    · rw [← hi1]
      exact hi2.symm
    · exact hi1.symm
    · exact hi1.symm

lemma iff_countColorCond_index (hl : l.OnlyUniqueDuals) :
    l.ColorCond ↔ ∀ (i : Fin l.length), l.countId (l.val.get i) = 2
      → countColorCond l (l.val.get i) := by
  rw [iff_countColorCond_isSome hl]
  refine Iff.intro (fun h i hi => ?_) (fun h i hi => ?_)
  · rw [← mem_withUniqueDual_iff_countId_eq_two] at hi
    exact h i (mem_withUniqueDual_isSome l i hi)
  · rw [← mem_withDual_iff_isSome, ← hl, mem_withUniqueDual_iff_countId_eq_two] at hi
    exact h i hi

lemma iff_countColorCond_mem (hl : l.OnlyUniqueDuals) :
    l.ColorCond ↔ ∀ (I : Index 𝓒.Color) (_ : I ∈ l.val),
    l.countId I = 2 → countColorCond l I := by
  rw [iff_countColorCond_index hl]
  refine Iff.intro (fun h I hI hi => ?_) (fun h i hi => ?_)
  · let i := l.val.indexOf I
    have hi' : i < l.length := List.indexOf_lt_length.mpr hI
    have hIi : I = l.val.get ⟨i, hi'⟩ := (List.indexOf_get hi').symm
    rw [hIi] at hi ⊢
    exact h ⟨i, hi'⟩ hi
  · exact h (l.val.get i) (List.getElem_mem l.val (↑i) i.isLt) hi


lemma mem_iff_dual_mem (hl : l.OnlyUniqueDuals) (hc : l.ColorCond) (I : Index 𝓒.Color)
    (hId : l.countId I = 2) : I ∈ l.val ↔ I.dual ∈ l.val := by
  rw [iff_countColorCond_mem hl] at hc
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · have hc' := hc I h hId
    simp only [countColorCond] at hc'
    rw [← countSelf_neq_zero] at h
    rw [← countSelf_neq_zero, ← countDual_eq_countSelf_Dual]
    omega
  · have hIdd : l.countId I.dual = 2 := by
      rw [← hId]
      apply countId_congr
      simp
    have hc' := (hc I.dual h hIdd).2
    simp at hc'
    rw [← countSelf_neq_zero]
    rw [← countSelf_neq_zero] at h
    rw [countDual_eq_countSelf_Dual] at hc'
    simp at hc'
    omega

lemma iff_countColorCond (hl : l.OnlyUniqueDuals) :
    l.ColorCond ↔ ∀ I, l.countSelf I ≠ 0 → l.countId I = 2 → countColorCond l I := by
  refine Iff.intro (fun h I hIs hi => ?_) (fun h => ?_)
  · rw [countSelf_neq_zero] at hIs
    rw [iff_countColorCond_mem hl] at h
    exact h I hIs hi
  · rw [iff_countColorCond_mem hl]
    intro I hmem hi
    refine h I ?_ hi
    rw [countSelf_neq_zero]
    exact hmem

lemma assoc (h : ColorCond (l ++ l2 ++ l3)) : ColorCond (l ++ (l2 ++ l3)) := by
  rw [← append_assoc]
  exact h

lemma symm (hl : (l ++ l2).OnlyUniqueDuals) (h : ColorCond (l ++ l2)) :
    ColorCond (l2 ++ l) := by
  rw [iff_countColorCond hl] at h
  rw [iff_countColorCond (OnlyUniqueDuals.symm' hl)]
  intro I hI1 hI2
  have hI' := h I (by simp_all; omega) (by simp_all; omega)
  simp_all
  omega

lemma inl (hl : (l ++ l2).OnlyUniqueDuals) (h : ColorCond (l ++ l2)) : ColorCond l := by
  rw [iff_countColorCond hl] at h
  rw [iff_countColorCond (OnlyUniqueDuals.inl hl)]
  intro I hI1 hI2
  have hI2' : l2.countId I = 0 := by
    rw [OnlyUniqueDuals.iff_countId_leq_two'] at hl
    have hlI := hl I
    simp at hlI
    omega
  have hI' := h I (by
    simp only [countSelf_append, ne_eq, add_eq_zero, not_and, hI1, false_implies])
    (by simp_all)
  simp at hI'
  rw [l2.countColorQuot_of_countId_zero hI2', l2.countSelf_of_countId_zero hI2',
    l2.countDual_of_countId_zero hI2', hI2'] at hI'
  simp at hI'
  omega

lemma inr (hl : (l ++ l2).OnlyUniqueDuals) (h : ColorCond (l ++ l2)) : ColorCond l2 := by
  have hs := symm hl h
  rw [OnlyUniqueDuals.symm] at hl
  exact inl hl hs

lemma swap (hl : (l ++ l2 ++ l3).OnlyUniqueDuals) (h : ColorCond (l ++ l2 ++ l3)) :
    ColorCond (l2 ++ l ++ l3) := by
  rw [iff_countColorCond hl] at h
  rw [iff_countColorCond (OnlyUniqueDuals.swap hl)]
  intro I hI1 hI2
  have hI' := h I (by simp_all) (by simp_all; omega)
  simp_all only [countSelf_append, ne_eq, add_eq_zero, not_and, and_imp, countId_append,
    countColorCond, countColorQuot_append, countDual_append, not_false_eq_true, implies_true]
  omega

/-!

## Contractions

-/

lemma contrIndexList : ColorCond l.contrIndexList := by
  funext i
  simp [Option.guard]

lemma contrIndexList_left (hl : (l ++ l2).OnlyUniqueDuals) (h1 : (l ++ l2).ColorCond) :
    ColorCond (l.contrIndexList ++ l2) := by
  rw [iff_countColorCond hl] at h1
  rw [iff_countColorCond (OnlyUniqueDuals.contrIndexList_left hl)]
  intro I hI1 hI2
  simp only [countSelf_append, ne_eq] at hI1
  have hc := countSelf_contrIndexList_le_countSelf l I
  have h2 := (countId_eq_two_ofcontrIndexList_left_of_OnlyUniqueDuals l l2 hl I hI2 )
  have hI1' := h1 I (by simp_all; omega) h2
  have hIdEq : l.contrIndexList.countId I = l.countId I := by
    simp at h2 hI2
    omega
  simp
  rw [l.countColorQuot_contrIndexList_eq_of_countId_eq hIdEq,
    l.countSelf_contrIndexList_eq_of_countId_eq hIdEq,
    l.countDual_contrIndexList_eq_of_countId_eq hIdEq, hIdEq]
  simpa using hI1'

/-!

## Bool

-/
/-- A bool which is true for an index list if and only if every index and its' dual, when it exists,
  have dual colors. -/
def bool (l : IndexList 𝓒.Color) : Bool :=
  if (∀ (i : l.withDual), 𝓒.τ
      (l.colorMap ((l.getDual? i).get (l.withDual_isSome i))) = l.colorMap i) then
    true
  else false

lemma iff_bool : l.ColorCond ↔ bool l := by
  rw [iff_withDual, bool]
  simp only [Subtype.forall, mem_withDual_iff_isSome, Bool.if_false_right, Bool.and_true,
    decide_eq_true_eq]

end ColorCond

end IndexList

end IndexNotation
