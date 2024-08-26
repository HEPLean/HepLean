/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.OnlyUniqueDuals
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
/-!

# Index lists and color

In this file we look at the interaction of index lists and color.

The main definition of this file is `ColorCond`.
-/

namespace IndexNotation

namespace IndexList

variable {𝓒 : TensorColor}
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
variable (l l2 l3 : IndexList 𝓒.Color)

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

lemma color_quot_filter_of_countP_two (hl : l.withUniqueDual = l.withDual) (i : Fin l.length)
    (hi : (l.getDual? i).isSome) :
    (l.val.filter (fun J => (l.val.get i).id = J.id)).countP
    (fun J => (l.val.get i).toColor = J.toColor ∨ (l.val.get i).toColor = 𝓒.τ (J.toColor)) =
    (l.val.filter (fun J => (l.val.get i).id = J.id)).length ↔
    (l.colorMap i = l.colorMap ((l.getDual? i).get hi) ∨
    l.colorMap i = 𝓒.τ (l.colorMap ((l.getDual? i).get hi))) := by
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

lemma color_dual_eq_self_filter_of_countP_two (hl : l.withUniqueDual = l.withDual)
    (i : Fin l.length) (hi : (l.getDual? i).isSome) :
    (l.val.filter (fun J => (l.val.get i).id = J.id)).countP
    (fun J => (l.val.get i).toColor = J.toColor) =
    (l.val.filter (fun J => (l.val.get i).id = J.id)).countP
    (fun J => (l.val.get i).toColor = 𝓒.τ (J.toColor))
    ↔ l.colorMap i = 𝓒.τ (l.colorMap ((l.getDual? i).get hi))
    ∨ (l.colorMap i) = 𝓒.τ (l.colorMap i) := by
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

/-- A condition on an index list `l` and and index `I`. If the id of `I` appears
twice in `l` (and `I` at least once) then this condition is equivalent to the dual of `I` having
dual color to `I`, but written totally in terms of lists. -/
abbrev countColorCond (l : IndexList 𝓒.Color) (I : Index 𝓒.Color) : Prop :=
    (l.val.filter (fun J => I.id = J.id)).countP
    (fun J => I.toColor = J.toColor ∨ I.toColor = 𝓒.τ (J.toColor)) =
    (l.val.filter (fun J => I.id = J.id)).length ∧
    (l.val.filter (fun J => I.id = J.id)).countP (fun J => I.toColor = J.toColor) =
    (l.val.filter (fun J => I.id = J.id)).countP (fun J => I.toColor = 𝓒.τ (J.toColor))

lemma countColorCond_cons_neg (l : IndexList 𝓒.Color) (I I' : Index 𝓒.Color) (hid : I.id ≠ I'.id) :
    countColorCond (l.cons I) I' ↔ countColorCond l I' := by
  have h1 : (l.cons I).val.filter (fun J => I'.id = J.id) =
      l.val.filter (fun J => I'.id = J.id) := by
    simp only [cons]
    rw [List.filter_cons_of_neg]
    simp only [decide_eq_true_eq]
    exact id (Ne.symm hid)
  rw [countColorCond, countColorCond, h1]

lemma color_eq_of_countColorCond_cons_pos (l : IndexList 𝓒.Color) (I I' : Index 𝓒.Color)
    (hl : countColorCond (l.cons I) I') (hI : I.id = I'.id) : I.toColor = I'.toColor ∨
    I.toColor = 𝓒.τ I'.toColor := by
  have hl1 := hl.1
  rw [List.countP_eq_length] at hl1
  have h2 := hl1 I (by simp; exact hI.symm)
  simp at h2
  rcases h2 with h2 | h2
  · simp [h2]
  · rw [h2]
    apply Or.inr (𝓒.τ_involutive _).symm

lemma iff_countColorCond_isSome (hl : l.withUniqueDual = l.withDual) :
    l.ColorCond ↔
    ∀ (i : Fin l.length) (_ : (l.getDual? i).isSome), countColorCond l (l.val.get i) := by
  rw [iff_on_isSome]
  simp only [countColorCond]
  refine Iff.intro (fun h i hi => ?_) (fun h i hi => ?_)
  · rw [color_quot_filter_of_countP_two hl i hi, color_dual_eq_self_filter_of_countP_two hl i hi]
    have hi' := h i hi
    exact And.intro (Or.inr hi'.symm) (Or.inl hi'.symm)
  · have hi' := h i hi
    rw [color_quot_filter_of_countP_two hl i hi,
      color_dual_eq_self_filter_of_countP_two hl i hi] at hi'
    rcases hi'.1 with hi1 | hi1
      <;> rcases hi'.2 with hi2 | hi2
    · exact hi2.symm
    · rw [← hi1]
      exact hi2.symm
    · exact hi1.symm
    · exact hi1.symm

lemma iff_countColorCond (hl : l.withUniqueDual = l.withDual) :
    l.ColorCond ↔ ∀ (i : Fin l.length), l.countId (l.val.get i) = 2
      → countColorCond l (l.val.get i) := by
  rw [iff_countColorCond_isSome hl]
  refine Iff.intro (fun h i hi => ?_) (fun h i hi => ?_)
  · rw [← mem_withUniqueDual_iff_countId_eq_two] at hi
    exact h i (mem_withUniqueDual_isSome l i hi)
  · rw [← mem_withDual_iff_isSome, ← hl, mem_withUniqueDual_iff_countId_eq_two] at hi
    exact h i hi

lemma iff_countColorCond_mem (hl : l.withUniqueDual = l.withDual) :
    l.ColorCond ↔ ∀ (I : Index 𝓒.Color) (_ : I ∈ l.val),
    l.countId I = 2 → countColorCond l I := by
  rw [iff_countColorCond hl]
  refine Iff.intro (fun h I hI hi => ?_) (fun h i hi => ?_)
  · let i := l.val.indexOf I
    have hi' : i < l.length := List.indexOf_lt_length.mpr hI
    have hIi : I = l.val.get ⟨i, hi'⟩ := (List.indexOf_get hi').symm
    rw [hIi] at hi ⊢
    exact h ⟨i, hi'⟩ hi
  · exact h (l.val.get i) (List.getElem_mem l.val (↑i) i.isLt) hi

/-- The lemma `ColorCond` written totally in terms of lists. -/
lemma iff_countColorCond_all (hl : l.withUniqueDual = l.withDual) :
    l.ColorCond ↔ l.val.all (fun I =>
      (l.countId I = 2 → countColorCond l I)) := by
  rw [iff_countColorCond_mem hl]
  simp only [List.all_eq_true, decide_eq_true_eq]

@[simp]
lemma consDual_color {I : Index 𝓒.Color} (hI : l.countId I = 1)
    (hI2 : (l.countId I =
    l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ (J.toColor)))) :
    (l.consDual hI).toColor = 𝓒.τ I.toColor := by
  have h1 : l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ (J.toColor))
      = (l.val.filter (fun J => I.id = J.id)).countP (fun J => I.toColor = 𝓒.τ (J.toColor)) := by
    rw [List.countP_filter]
    apply congrFun
    apply congrArg
    funext J
    simp only [Bool.decide_and, decide_eq_true_eq]
    exact Bool.and_comm (decide (I.id = J.id)) (decide (I.toColor = 𝓒.τ J.toColor))
  rw [h1, countId, List.countP_eq_length_filter, l.consDual_filter hI] at hI2
  symm at hI2
  rw [List.countP_eq_length] at hI2
  simp only [List.mem_singleton, decide_eq_true_eq, forall_eq] at hI2
  rw [hI2, 𝓒.τ_involutive]

lemma of_cons (I : Index 𝓒.Color) (h : (l.cons I).ColorCond)
    (hl : (l.cons I).withUniqueDual = (l.cons I).withDual) : l.ColorCond := by
  rw [iff_countColorCond_mem hl] at h
  have hl' : l.withUniqueDual = l.withDual := withUniqueDual_eq_withDual_of_cons l hl
  rw [iff_countColorCond_mem hl']
  intro I' hI'mem hi
  have hI''mem : I' ∈ (l.cons I).val := by
    simp [hI'mem]
  have hI'' := h I' hI''mem
  by_cases hI'id : I'.id ≠ I.id
  · rw [countId_eq_length_filter, cons_val, List.filter_cons_of_neg,
      countColorCond_cons_neg] at hI''
    · rw [countId_eq_length_filter] at hi
      exact hI'' hi
    · exact id (Ne.symm hI'id)
    · simpa using hI'id
  · simp at hI'id
    rw [countId_eq_length_filter, hI'id] at hi
    rw [propext (withUniqueDual_eq_withDual_cons_iff l I hl'), countId_eq_length_filter, hi] at hl
    simp at hl

lemma countId_of_cons (I : Index 𝓒.Color) (h : (l.cons I).ColorCond)
    (hl : (l.cons I).withUniqueDual = (l.cons I).withDual) :
    l.countId I =
    l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ (J.toColor)) := by
  have h1 := (l.withUniqueDual_eq_withDual_cons_iff I
          (l.withUniqueDual_eq_withDual_of_cons hl)).mp hl
  rw [List.countP_eq_length_filter]
  trans (l.val.filter (fun J => I.id = J.id)).countP (fun J => I.toColor = 𝓒.τ (J.toColor))
  · by_cases hc : l.countId I = 1
    · rw [l.consDual_filter hc]
      simp [List.countP, List.countP.go]
      rw [iff_withDual] at h
      have h' := h ⟨⟨0, by simp⟩, (by
        rw [mem_withDual_iff_countId_gt_one]
        simp_all [countId])⟩
      change 𝓒.τ (l.consDual hc).toColor = _ at h'
      rw [h']
      simpa [colorMap] using hc
    · have hc' : l.countId I = 0 := by
        omega
      rw [countId_eq_length_filter, List.length_eq_zero] at hc'
      simp [hc']
      omega
  · rw [List.countP_filter]
    simp only [decide_eq_true_eq, Bool.decide_and]
    rw [← List.countP_eq_length_filter]
    apply congrFun
    apply congrArg
    funext J
    exact Bool.and_comm (decide (I.toColor = 𝓒.τ J.toColor)) (decide (I.id = J.id))

lemma cons_of_countP (h : l.ColorCond) (I : Index 𝓒.Color) (hl : l.withUniqueDual = l.withDual)
    (hI1 : l.countId I ≤ 1)
    (hI2 : l.countId I =
    l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ (J.toColor))) :
    (l.cons I).ColorCond := by
  rw [iff_countColorCond_mem]
  · intro I' hI'
    by_cases hI'' : I' ≠ I
    · have hI'mem : I' ∈ l.val := by
        simp only [cons, List.mem_cons] at hI'
        rcases hI' with hI' | hI'
        · exact False.elim (hI'' hI')
        · exact hI'
      by_cases hI'id : I'.id ≠ I.id
      · rw [countId_eq_length_filter, cons_val, List.filter_cons_of_neg]
        · rw [iff_countColorCond_mem] at h
          rw [countColorCond_cons_neg l I I' hI'id.symm]
          · rw [← countId_eq_length_filter]
            exact h I' hI'mem
          · exact hl
        · simpa using hI'id
      · simp at hI'id
        intro hI
        rw [countId_eq_length_filter, hI'id] at hI
        simp at hI
        rw [← List.countP_eq_length_filter] at hI
        have hI'dual : I' = l.consDual hI := by
          simp [consDual_iff, hI'id, hI'mem]
        subst hI'dual
        rw [countColorCond, l.filter_of_constDual hI]
        simp only [List.countP, List.countP.go, Bool.decide_or, true_or, decide_True, zero_add,
          Nat.reduceAdd, cond_true, List.length_cons, List.length_singleton]
        rw [consDual_color hI hI2, 𝓒.τ_involutive]
        simp
    · simp only [ne_eq, Decidable.not_not] at hI''
      symm at hI''
      subst hI''
      intro hIf
      rw [countId_cons_eq_two] at hIf
      rw [countColorCond]
      simp only [Bool.decide_or, cons_val, decide_True, List.filter_cons_of_pos, Bool.true_or,
        List.countP_cons_of_pos, List.length_cons, add_left_inj]
      rw [l.consDual_filter hIf]
      simp only [List.countP, List.countP.go, zero_add, List.length_singleton, Nat.reduceAdd]
      rw [consDual_color hIf hI2, 𝓒.τ_involutive]
      simp only [decide_True, Bool.or_true, cond_true, true_and]
      by_cases h1 : (I.toColor = 𝓒.τ I.toColor)
      · have h1' : decide (I.toColor = 𝓒.τ I.toColor) = true := by simpa using h1
        simp [h1']
      · have h1' : decide (I.toColor = 𝓒.τ I.toColor) = false := by simpa using h1
        simp [h1']
  · exact (withUniqueDual_eq_withDual_cons_iff l I hl).mpr hI1

lemma cons_iff (I : Index 𝓒.Color) :
    (l.cons I).withUniqueDual = (l.cons I).withDual ∧
    (l.cons I).ColorCond ↔
    l.withUniqueDual = l.withDual ∧ l.ColorCond ∧
    l.countId I ≤ 1 ∧
    (l.countId I =
    l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ (J.toColor))) := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · apply And.intro
    · exact l.withUniqueDual_eq_withDual_of_cons h.1
    · apply And.intro
      · exact of_cons I h.2 h.1
      · apply And.intro
        · exact (l.withUniqueDual_eq_withDual_cons_iff I
            (l.withUniqueDual_eq_withDual_of_cons h.1)).mp h.1
        · exact countId_of_cons I h.2 h.1
  · apply And.intro
    · rw [withUniqueDual_eq_withDual_cons_iff]
      · exact h.2.2.1
      · exact h.1
    · exact cons_of_countP h.2.1 I h.1 h.2.2.1 h.2.2.2

lemma assoc (h : ColorCond (l ++ l2 ++ l3)) : ColorCond (l ++ (l2 ++ l3)) := by
  rw [← append_assoc]
  exact h

lemma inl (h : ColorCond (l ++ l2)) : ColorCond l := by
  rw [iff_withDual] at h ⊢
  intro i
  simpa only [withDual_isSome, getDual?_append_inl_of_getDual?_isSome, Option.get_some,
    colorMap_append_inl] using h ⟨appendEquiv (Sum.inl i), by simp only [mem_withDual_iff_isSome,
      withDual_isSome, getDual?_append_inl_of_getDual?_isSome, Option.isSome_some]⟩

lemma symm (hu : (l ++ l2).withUniqueDual = (l ++ l2).withDual) (h : ColorCond (l ++ l2)) :
    ColorCond (l2 ++ l) := by
  rw [iff_on_isSome] at h ⊢
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  rw [append_withDual_eq_withUniqueDual_symm] at hu
  rw [← mem_withDual_iff_isSome, ← hu] at hj
  match k with
  | Sum.inl k =>
    have hn := l2.append_inl_not_mem_withDual_of_withDualInOther l k hj
    by_cases hk' : (l2.getDual? k).isSome
    · simp_all only [mem_withDual_iff_isSome, getDual?_append_inl_of_getDual?_isSome,
      Option.isSome_some, mem_withInDualOther_iff_isSome, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none, true_iff, Option.get_some, colorMap_append_inl]
      have hk'' := h (appendEquiv (Sum.inr k))
      simp only [getDual?_isSome_append_inr_iff, colorMap_append_inr] at hk''
      simp_all only [getDual?_append_inl_of_getDual?_isSome, Option.isSome_some, Option.isSome_none,
        Bool.false_eq_true, or_false, Option.isNone_none,
        getDual?_inr_getDualInOther?_isNone_getDual?_isSome, Option.get_some, colorMap_append_inr,
        true_implies]
    · simp_all only [mem_withDual_iff_isSome, Bool.false_eq_true, mem_withInDualOther_iff_isSome,
      Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none, false_iff, Option.isNone_none,
      colorMap_append_inl]
      have hn' : (l2.getDualInOther? l k).isSome := by
        simp_all only [Option.isNone_none, getDual?_isSome_append_inl_iff, Option.isSome_none,
          Bool.false_eq_true, false_or]
      have hk'' := h (appendEquiv (Sum.inr k))
      simp only [getDual?_isSome_append_inr_iff, colorMap_append_inr] at hk''
      simp_all only [Option.isSome_none, Bool.false_eq_true, or_true,
        getDual?_append_inr_getDualInOther?_isSome, Option.get_some, colorMap_append_inl,
        true_implies, Option.isNone_none, getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome,
        colorMap_append_inr]
  | Sum.inr k =>
    have hn := l2.append_inr_not_mem_withDual_of_withDualInOther l k hj
    by_cases hk' : (l.getDual? k).isSome
    · simp_all only [mem_withDual_iff_isSome, mem_withInDualOther_iff_isSome, Bool.not_eq_true,
        Option.not_isSome, Option.isNone_iff_eq_none, true_iff, Option.isNone_none,
        getDual?_inr_getDualInOther?_isNone_getDual?_isSome, Option.get_some, colorMap_append_inr]
      have hk'' := h (appendEquiv (Sum.inl k))
      simp only [getDual?_isSome_append_inl_iff, colorMap_append_inl] at hk''
      simp_all only [Option.isNone_none, getDual?_inr_getDualInOther?_isNone_getDual?_isSome,
        Option.isSome_some, Option.isSome_none, Bool.false_eq_true, or_false,
        getDual?_append_inl_of_getDual?_isSome, Option.get_some, colorMap_append_inl, true_implies]
    · simp_all only [mem_withDual_iff_isSome, Bool.false_eq_true, mem_withInDualOther_iff_isSome,
      Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none, false_iff,
      colorMap_append_inr]
      have hn' : (l.getDualInOther? l2 k).isSome := by
        exact Option.ne_none_iff_isSome.mp hn
      have hk'' := h (appendEquiv (Sum.inl k))
      simp only [getDual?_isSome_append_inl_iff, colorMap_append_inl] at hk''
      simp_all only [Option.isSome_none, Bool.false_eq_true, or_true, Option.isNone_none,
        getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome, Option.get_some,
        colorMap_append_inr, true_implies, getDual?_append_inr_getDualInOther?_isSome,
        colorMap_append_inl]

lemma inr (hu : (l ++ l2).withUniqueDual = (l ++ l2).withDual) (h : ColorCond (l ++ l2)) :
    ColorCond l2 := inl (symm hu h)

lemma triple_right (hu : (l ++ l2 ++ l3).withUniqueDual = (l ++ l2 ++ l3).withDual)
    (h : ColorCond (l ++ l2 ++ l3)) : ColorCond (l2 ++ l3) := by
  have h1 := assoc h
  rw [append_assoc] at hu
  exact h1.inr hu

lemma triple_drop_mid (hu : (l ++ l2 ++ l3).withUniqueDual = (l ++ l2 ++ l3).withDual)
    (h : ColorCond (l ++ l2 ++ l3)) : ColorCond (l ++ l3) := by
  rw [append_assoc] at hu
  refine (((assoc h).symm hu).assoc.inr ?_).symm ?_
  · rw [append_withDual_eq_withUniqueDual_symm, append_assoc] at hu
    exact hu
  · rw [append_withDual_eq_withUniqueDual_symm, append_assoc] at hu
    exact append_withDual_eq_withUniqueDual_inr _ _ hu

lemma swap (hu : (l ++ l2 ++ l3).withUniqueDual = (l ++ l2 ++ l3).withDual)
    (h : ColorCond (l ++ l2 ++ l3)) :
    ColorCond (l2 ++ l ++ l3) := by
  have hC := h
  have hu' := hu
  rw [iff_on_isSome] at h ⊢
  intro j hj
  obtain ⟨k, hk⟩ := appendEquiv.surjective j
  subst hk
  match k with
  | Sum.inl k =>
    have hj' := hj
    rw [append_withDual_eq_withUniqueDual_swap] at hu
    rw [← mem_withDual_iff_isSome, ← hu] at hj'
    have hn := (l2 ++ l).append_inl_not_mem_withDual_of_withDualInOther l3 k hj'
    simp only [mem_withDual_iff_isSome, mem_withInDualOther_iff_isSome, Bool.not_eq_true,
      Option.not_isSome, Option.isNone_iff_eq_none] at hn
    simp only [getDual?_isSome_append_inl_iff] at hj
    by_cases hk' : ((l2 ++ l).getDual? k).isSome
    · simp only [hk', getDual?_append_inl_of_getDual?_isSome, Option.get_some, colorMap_append_inl]
      have hu' := append_withDual_eq_withUniqueDual_inl (l2 ++ l) l3 hu
      have hC' := hC.inl.symm ((append_withDual_eq_withUniqueDual_symm l2 l).mp hu')
      rw [iff_on_isSome] at hC'
      exact hC' k hk'
    · simp only [hk', Bool.false_eq_true, false_iff] at hn
      rw [← @Option.not_isSome_iff_eq_none, not_not] at hn
      simp_all only [mem_withDual_iff_isSome, Bool.false_eq_true, or_true, Bool.not_eq_true,
        Option.not_isSome, Option.isNone_iff_eq_none, Option.isNone_none,
        getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome, Option.get_some,
        colorMap_append_inr, colorMap_append_inl]
      obtain ⟨k', hk'⟩ := appendEquiv.surjective k
      subst hk'
      match k' with
      | Sum.inl k' =>
        simp only [getDualInOther?_append_of_inl] at hn
        simp only [getDualInOther?_append_of_inl, colorMap_append_inl]
        have hL := triple_right hu' hC
        rw [iff_on_isSome] at hL
        have hL' := hL (appendEquiv (Sum.inl k')) (by simp only [getDual?_isSome_append_inl_iff, hn,
          or_true])
        simp_all only [Option.isNone_none, getDualInOther?_append_of_inl,
          getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome, Option.isSome_some,
          getDual?_eq_none_append_inl_iff, Option.get_some, colorMap_append_inr,
          colorMap_append_inl]
      | Sum.inr k' =>
        simp only [getDualInOther?_append_of_inr] at hn
        simp only [getDualInOther?_append_of_inr, colorMap_append_inr]
        have hR := triple_drop_mid hu' hC
        rw [iff_on_isSome] at hR
        have hR' := hR (appendEquiv (Sum.inl k')) (by simp only [getDual?_isSome_append_inl_iff, hn,
          or_true])
        simp_all only [Option.isNone_none, getDualInOther?_append_of_inr,
          getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome, Option.isSome_some,
          getDual?_eq_none_append_inr_iff, Option.get_some, colorMap_append_inr,
          colorMap_append_inl]
  | Sum.inr k =>
    have hj' := hj
    rw [append_withDual_eq_withUniqueDual_swap] at hu
    rw [← mem_withDual_iff_isSome, ← hu] at hj'
    have hn := (l2 ++ l).append_inr_not_mem_withDual_of_withDualInOther l3 k hj'
    simp only [mem_withDual_iff_isSome, mem_withInDualOther_iff_isSome,
      getDualInOther?_isSome_of_append_iff, not_or, Bool.not_eq_true, Option.not_isSome,
      Option.isNone_iff_eq_none] at hn
    by_cases hk' : (l3.getDual? k).isSome
    · simp_all only [mem_withDual_iff_isSome, true_iff, Option.isNone_iff_eq_none,
      getDualInOther?_eq_none_of_append_iff, and_self,
      getDual?_inr_getDualInOther?_isNone_getDual?_isSome, Option.get_some, colorMap_append_inr]
      have hRR := hC.inr hu'
      rw [iff_on_isSome] at hRR
      exact hRR k hk'
    · simp_all only [mem_withDual_iff_isSome, Bool.false_eq_true, false_iff, not_and,
      Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none, colorMap_append_inr]
      by_cases hk'' : (l3.getDualInOther? l2 k).isSome
      · simp_all only [getDualInOther?_of_append_of_isSome, Option.isSome_some,
        getDual?_append_inr_getDualInOther?_isSome, Option.get_some, colorMap_append_inl]
        have hL := triple_right hu' hC
        rw [iff_on_isSome] at hL
        have hL' := hL (appendEquiv (Sum.inr k)) (by simp [hk''])
        simp_all only [getDualInOther?_of_append_of_isSome, Option.isSome_some,
          getDual?_append_inr_getDualInOther?_isSome, Option.get_some, colorMap_append_inl,
          colorMap_append_inr]
      · simp_all only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none,
          true_implies]
        rw [← Option.not_isSome_iff_eq_none, not_not] at hn
        simp_all only [getDualInOther?_of_append_of_isNone_isSome, Option.isSome_some,
          getDual?_append_inr_getDualInOther?_isSome, Option.get_some, colorMap_append_inl,
          colorMap_append_inr]
        have hR := triple_drop_mid hu' hC
        rw [iff_on_isSome] at hR
        have hR' := hR (appendEquiv (Sum.inr k)) (by simp [hn])
        simp_all only [getDualInOther?_of_append_of_isNone_isSome, Option.isSome_some,
          getDual?_append_inr_getDualInOther?_isSome, Option.get_some, colorMap_append_inl,
          colorMap_append_inr]

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
