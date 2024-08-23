/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Contraction
import HepLean.SpaceTime.LorentzTensor.IndexNotation.OnlyUniqueDuals
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
import HepLean.SpaceTime.LorentzTensor.Contraction
/-!

# Index lists and color

In this file we look at the interaction of index lists with color.

The main definiton of this file is `ColorIndexList`. This type defines the
permissible index lists which can be used for a tensor. These are lists of indices for which
every index with a dual has a unique dual, and the color of that dual (when it exists) is dual
to the color of the index.

We also define `AppendCond`, which is a condition on two `ColorIndexList`s which allows them to be
appended to form a new `ColorIndexList`.

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
  rw [← mem_withDual_iff_isSome, ← hl, mem_withUniqueDual_iff_countP] at hi1
  rcases l.filter_id_of_countP_two hi1 with hf | hf
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
  rw [← mem_withDual_iff_isSome, ← hl, mem_withUniqueDual_iff_countP] at hi1
  rcases l.filter_id_of_countP_two hi1 with hf | hf
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
abbrev countPCond (l : IndexList 𝓒.Color) (I : Index 𝓒.Color) : Prop :=
    (l.val.filter (fun J => I.id = J.id)).countP
    (fun J => I.toColor = J.toColor ∨ I.toColor = 𝓒.τ (J.toColor)) =
    (l.val.filter (fun J => I.id = J.id)).length ∧
    (l.val.filter (fun J => I.id = J.id)).countP (fun J => I.toColor = J.toColor) =
    (l.val.filter (fun J => I.id = J.id)).countP (fun J => I.toColor = 𝓒.τ (J.toColor))

lemma countPCond_cons_neg (l : IndexList 𝓒.Color) (I I' : Index 𝓒.Color) (hid : I.id ≠ I'.id) :
    countPCond (l.cons I) I' ↔ countPCond l I' := by
  have h1 : (l.cons I).val.filter (fun J => I'.id = J.id) =
      l.val.filter (fun J => I'.id = J.id) := by
    simp only [cons]
    rw [List.filter_cons_of_neg]
    simp only [decide_eq_true_eq]
    exact id (Ne.symm hid)
  rw [countPCond, countPCond, h1]

lemma color_eq_of_countPCond_cons_pos (l : IndexList 𝓒.Color) (I I' : Index 𝓒.Color)
    (hl : countPCond (l.cons I) I') (hI : I.id = I'.id) : I.toColor = I'.toColor ∨
    I.toColor = 𝓒.τ I'.toColor := by
  have hl1 := hl.1
  rw [List.countP_eq_length] at hl1
  have h2 := hl1 I (by simp; exact hI.symm)
  simp at h2
  rcases h2 with h2 | h2
  · rw [h2]
    simp
  · rw [h2]
    apply Or.inr (𝓒.τ_involutive _).symm

lemma iff_countP_isSome (hl : l.withUniqueDual = l.withDual) :
    l.ColorCond ↔
    ∀ (i : Fin l.length) (_ : (l.getDual? i).isSome), countPCond l (l.val.get i) := by
  rw [iff_on_isSome]
  simp only [countPCond]
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

lemma iff_countP (hl : l.withUniqueDual = l.withDual) :
    l.ColorCond ↔ ∀ (i : Fin l.length), (l.val.filter (fun J => (l.val.get i).id = J.id)).length = 2
      → countPCond l (l.val.get i) := by
  rw [iff_countP_isSome hl]
  refine Iff.intro (fun h i hi => ?_) (fun h i hi => ?_)
  · rw [← List.countP_eq_length_filter] at hi
    rw [← @mem_withUniqueDual_iff_countP] at hi
    exact h i (mem_withUniqueDual_isSome l i hi)
  · rw [← @mem_withDual_iff_isSome, ← hl] at hi
    rw [mem_withUniqueDual_iff_countP, List.countP_eq_length_filter] at hi
    exact h i hi

lemma iff_countP_mem (hl : l.withUniqueDual = l.withDual) :
    l.ColorCond ↔ ∀ (I : Index 𝓒.Color) (_ : I ∈ l.val),
    (l.val.filter (fun J => I.id = J.id)).length = 2 → countPCond l I := by
  rw [iff_countP hl]
  refine Iff.intro (fun h I hI hi => ?_) (fun h i hi => ?_)
  · let i := l.val.indexOf I
    have hi' : i < l.length := List.indexOf_lt_length.mpr hI
    have hIi : I = l.val.get ⟨i, hi'⟩ := (List.indexOf_get hi').symm
    rw [hIi] at hi ⊢
    exact h ⟨i, hi'⟩ hi
  · exact h (l.val.get i) (List.getElem_mem l.val (↑i) i.isLt) hi

/-- The lemma `ColorCond` written totally in terms of lists. -/
lemma iff_countP_all (hl : l.withUniqueDual = l.withDual) :
    l.ColorCond ↔ l.val.all (fun I =>
      ((l.val.filter (fun J => I.id = J.id)).length = 2 → countPCond l I)) := by
  rw [iff_countP_mem hl]
  simp only [List.all_eq_true, decide_eq_true_eq]

@[simp]
lemma consDual_color {I : Index 𝓒.Color} (hI : l.val.countP (fun J => I.id = J.id) = 1)
    (hI2 : (l.val.countP (fun J => I.id = J.id) =
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
  rw [h1, List.countP_eq_length_filter] at hI2
  rw [l.consDual_filter hI] at hI2
  symm at hI2
  rw [List.countP_eq_length] at hI2
  simp at hI2
  rw [hI2, 𝓒.τ_involutive]

lemma of_cons (I : Index 𝓒.Color) (h : (l.cons I).ColorCond)
    (hl : (l.cons I).withUniqueDual = (l.cons I).withDual) : l.ColorCond := by
  rw [iff_countP_mem hl] at h
  have hl' : l.withUniqueDual = l.withDual := withUniqueDual_eq_withDual_of_cons l hl
  rw [iff_countP_mem hl']
  intro I' hI'mem hi
  have hI''mem : I' ∈ (l.cons I).val := by
    simp [hI'mem]
  have hI'' := h I' hI''mem
  by_cases hI'id : I'.id ≠ I.id
  · rw [cons_val, List.filter_cons_of_neg, countPCond_cons_neg] at hI''
    · exact hI'' hi
    · exact id (Ne.symm hI'id)
    · simpa using hI'id
  · simp at hI'id
    rw [hI'id] at hi
    rw [propext (withUniqueDual_eq_withDual_cons_iff l I hl')] at hl
    rw [List.countP_eq_length_filter, hi] at hl
    simp at hl

lemma countP_of_cons (I : Index 𝓒.Color) (h : (l.cons I).ColorCond)
    (hl : (l.cons I).withUniqueDual = (l.cons I).withDual) :
    l.val.countP (fun J => I.id = J.id) =
    l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ (J.toColor)) := by
  have h1 := (l.withUniqueDual_eq_withDual_cons_iff I
          (l.withUniqueDual_eq_withDual_of_cons hl)).mp hl
  rw [List.countP_eq_length_filter]
  trans (l.val.filter (fun J => I.id = J.id)).countP (fun J => I.toColor = 𝓒.τ (J.toColor))
  · by_cases hc : List.countP (fun J => (I.id = J.id)) l.val = 1
    · rw [l.consDual_filter hc]
      simp [List.countP, List.countP.go]
      rw [iff_withDual] at h
      have h' := h ⟨⟨0, by simp⟩, (by
        rw [mem_withDual_iff_countP]
        simp [hc])⟩
      change 𝓒.τ (l.consDual hc).toColor = _ at h'
      rw [h']
      simp [colorMap]
    · have hc' : List.countP (fun J => (I.id = J.id)) l.val = 0 := by
        omega
      rw [List.countP_eq_length_filter, List.length_eq_zero] at hc'
      simp [hc']
  · rw [List.countP_filter]
    apply congrFun
    apply congrArg
    funext J
    simp only [decide_eq_true_eq, Bool.decide_and]
    exact Bool.and_comm (decide (I.toColor = 𝓒.τ J.toColor)) (decide (I.id = J.id))

lemma cons_of_countP (h : l.ColorCond) (I : Index 𝓒.Color) (hl : l.withUniqueDual = l.withDual)
    (hI1 : l.val.countP (fun J => I.id = J.id) ≤ 1)
    (hI2 : (l.val.countP (fun J => I.id = J.id) =
    l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ (J.toColor)))) :
    (l.cons I).ColorCond := by
  rw [iff_countP_mem]
  · intro I' hI'
    by_cases hI'' : I' ≠ I
    · have hI'mem : I' ∈ l.val := by
        simp only [cons, List.mem_cons] at hI'
        rcases hI' with hI' | hI'
        · exact False.elim (hI'' hI')
        · exact hI'
      by_cases hI'id : I'.id ≠ I.id
      · rw [cons_val]
        rw [List.filter_cons_of_neg]
        · rw [iff_countP_mem] at h
          rw [countPCond_cons_neg l I I' hI'id.symm]
          · exact h I' hI'mem
          · exact hl
        · simpa using hI'id
      · simp at hI'id
        intro hI
        rw [hI'id] at hI
        simp at hI
        rw [← List.countP_eq_length_filter] at hI
        have hI'dual : I' = l.consDual hI := by
          rw [consDual_iff]
          simp [hI'id, hI'mem]
        subst hI'dual
        rw [countPCond, l.filter_of_constDual hI]
        simp [List.countP, List.countP.go]
        rw [consDual_color hI hI2, 𝓒.τ_involutive]
        simp
    · simp at hI''
      symm at hI''
      subst hI''
      simp only [cons_val, decide_True, List.filter_cons_of_pos, List.length_cons, Nat.reduceEqDiff]
      intro hIf
      rw [← List.countP_eq_length_filter] at hIf
      rw [countPCond]
      simp only [Bool.decide_or, cons_val, decide_True, List.filter_cons_of_pos, Bool.true_or,
        List.countP_cons_of_pos, List.length_cons, add_left_inj]
      rw [l.consDual_filter hIf]
      simp only [List.countP, List.countP.go, zero_add, List.length_singleton, Nat.reduceAdd]
      rw [consDual_color hIf hI2, 𝓒.τ_involutive]
      simp only [decide_True, Bool.or_true, cond_true, true_and]
      by_cases h1 : (I.toColor = 𝓒.τ I.toColor)
      · have h1' : decide (I.toColor = 𝓒.τ I.toColor) = true := by simpa using h1
        rw [h1']
        simp
      · have h1' : decide (I.toColor = 𝓒.τ I.toColor) = false := by simpa using h1
        rw [h1']
        simp
  · exact (withUniqueDual_eq_withDual_cons_iff l I hl).mpr hI1

lemma cons_iff (I : Index 𝓒.Color) :
    (l.cons I).withUniqueDual = (l.cons I).withDual ∧
    (l.cons I).ColorCond ↔
    l.withUniqueDual = l.withDual ∧ l.ColorCond ∧
    l.val.countP (fun J => I.id = J.id) ≤ 1 ∧
    (l.val.countP (fun J => I.id = J.id) =
    l.val.countP (fun J => I.id = J.id ∧ I.toColor = 𝓒.τ (J.toColor))) := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · apply And.intro
    · exact l.withUniqueDual_eq_withDual_of_cons h.1
    · apply And.intro
      · exact of_cons I h.2 h.1
      · apply And.intro
        · exact (l.withUniqueDual_eq_withDual_cons_iff I
            (l.withUniqueDual_eq_withDual_of_cons h.1)).mp h.1
        · exact countP_of_cons I h.2 h.1
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
  refine ((((assoc h).symm hu).assoc).inr ?_).symm ?_
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
        rw [← @Option.not_isSome_iff_eq_none, not_not] at hn
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
/-!

## Contracting an `ColorIndexList`

-/

/-- The contraction of a `ColorIndexList`, `l`.
  That is, the `ColorIndexList` obtained by taking only those indices in `l` which do not
  have a dual. This can be thought of as contracting all of those indices with a dual. -/
def contr : ColorIndexList 𝓒 where
  toIndexList := l.toIndexList.contrIndexList
  unique_duals := by
    simp
  dual_color := by
    funext i
    simp [Option.guard]

@[simp]
lemma contr_contr : l.contr.contr = l.contr := by
  apply ext
  simp [contr]

@[simp]
lemma contr_contr_idMap (i : Fin l.contr.contr.length) :
    l.contr.contr.idMap i = l.contr.idMap (Fin.cast (by simp) i) := by
  simp only [contr, contrIndexList_idMap, Fin.cast_trans]
  apply congrArg
  simp only [withoutDualEquiv, RelIso.coe_fn_toEquiv, Finset.coe_orderIsoOfFin_apply,
    EmbeddingLike.apply_eq_iff_eq]
  have h1 : l.contrIndexList.withoutDual = Finset.univ := by
    have hx := l.contrIndexList.withDual_union_withoutDual
    have hx2 := l.contrIndexList_withDual
    simp_all
  simp only [h1]
  rw [orderEmbOfFin_univ]
  · rfl
  · rw [h1]
    simp

@[simp]
lemma contr_contr_colorMap (i : Fin l.contr.contr.length) :
    l.contr.contr.colorMap i = l.contr.colorMap (Fin.cast (by simp) i) := by
  simp only [contr, contrIndexList_colorMap, Fin.cast_trans]
  apply congrArg
  simp only [withoutDualEquiv, RelIso.coe_fn_toEquiv, Finset.coe_orderIsoOfFin_apply,
    EmbeddingLike.apply_eq_iff_eq]
  have h1 : l.contrIndexList.withoutDual = Finset.univ := by
    have hx := l.contrIndexList.withDual_union_withoutDual
    have hx2 := l.contrIndexList_withDual
    simp_all
  simp only [h1]
  rw [orderEmbOfFin_univ]
  · rfl
  · rw [h1]
    simp

@[simp]
lemma contr_of_withDual_empty (h : l.withDual = ∅) :
    l.contr = l := by
  simp [contr]
  apply ext
  simp [l.contrIndexList_of_withDual_empty h]

@[simp]
lemma contr_getDual?_eq_none (i : Fin l.contr.length) :
    l.contr.getDual? i = none := by
  simp only [contr, contrIndexList_getDual?]

@[simp]
lemma contr_areDualInSelf (i j : Fin l.contr.length) :
    l.contr.AreDualInSelf i j ↔ False := by
  simp [contr]

/-!

## Contract equiv

-/

/-- An equivalence splitting the indices of `l` into
  a sum type of those indices and their duals (with choice determined by the ordering on `Fin`),
  and those indices without duals.

  This equivalence is used to contract the indices of tensors. -/
def contrEquiv : (l.withUniqueDualLT ⊕ l.withUniqueDualLT) ⊕ Fin l.contr.length ≃ Fin l.length :=
  (Equiv.sumCongr (l.withUniqueLTGTEquiv) (Equiv.refl _)).trans <|
  (Equiv.sumCongr (Equiv.subtypeEquivRight (by
  simp only [l.unique_duals, implies_true]))
    (Fin.castOrderIso l.contrIndexList_length).toEquiv).trans <|
  l.dualEquiv

lemma contrEquiv_inl_inl_isSome (i : l.withUniqueDualLT) :
    (l.getDual? (l.contrEquiv (Sum.inl (Sum.inl i)))).isSome := by
  change (l.getDual? i).isSome
  have h1 : i.1 ∈ l.withUniqueDual := by
    have hi2 := i.2
    simp only [withUniqueDualLT, Finset.mem_filter] at hi2
    exact hi2.1
  exact mem_withUniqueDual_isSome l.toIndexList (↑i) h1

@[simp]
lemma contrEquiv_inl_inr_eq (i : l.withUniqueDualLT) :
    (l.contrEquiv (Sum.inl (Sum.inr i))) =
    (l.getDual? i.1).get (l.contrEquiv_inl_inl_isSome i) := by
  rfl

@[simp]
lemma contrEquiv_inl_inl_eq (i : l.withUniqueDualLT) :
    (l.contrEquiv (Sum.inl (Sum.inl i))) = i := by
  rfl

lemma contrEquiv_colorMapIso :
    ColorMap.MapIso (Equiv.refl (Fin l.contr.length))
    (ColorMap.contr l.contrEquiv l.colorMap) l.contr.colorMap := by
  simp [ColorMap.MapIso, ColorMap.contr]
  funext i
  simp [contr]
  rfl

lemma contrEquiv_contrCond : ColorMap.ContrCond l.contrEquiv l.colorMap := by
  simp only [ColorMap.ContrCond]
  funext i
  simp only [Function.comp_apply, contrEquiv_inl_inl_eq, contrEquiv_inl_inr_eq]
  have h1 := l.dual_color
  rw [ColorCond.iff_on_isSome] at h1
  exact (h1 i.1 _).symm

@[simp]
lemma contrEquiv_on_withDual_empty (i : Fin l.contr.length) (h : l.withDual = ∅) :
    l.contrEquiv (Sum.inr i) = Fin.cast (by simp [h]) i := by
  simp [contrEquiv]
  change l.dualEquiv (Sum.inr ((Fin.castOrderIso _).toEquiv i)) = _
  simp [dualEquiv, withoutDualEquiv]
  have h : l.withoutDual = Finset.univ := by
    have hx := l.withDual_union_withoutDual
    simp_all
  simp [h]
  rw [orderEmbOfFin_univ]
  · rfl
  · rw [h]
    simp

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
