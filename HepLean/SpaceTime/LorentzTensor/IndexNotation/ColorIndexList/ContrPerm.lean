/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.ColorIndexList.Contraction
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.Subperm
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
/-!

## Permutation

Test whether two `ColorIndexList`s are permutations of each other.
To prevent choice problems, this has to be done after contraction.

-/

namespace IndexNotation

namespace ColorIndexList

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color] [DecidableEq 𝓒.Color]

variable (l l' : ColorIndexList 𝓒)
open IndexList TensorColor

/--
  Two `ColorIndexList`s are said to be related by contracted permutations, `ContrPerm`,
  if and only if:

    1) Their contractions are the same length.
    2) Every index in the contracted list of one has a unqiue dual in the contracted
      list of the other and that dual has a the same color.
-/
def ContrPerm : Prop :=
  l.contr.length = l'.contr.length ∧
  IndexList.Subperm l.contr l'.contr.toIndexList ∧
  l'.contr.colorMap' ∘ Subtype.val ∘ (l.contr.getDualInOtherEquiv l'.contr)
  = l.contr.colorMap' ∘ Subtype.val

namespace ContrPerm

variable {l l' l2 l3 : ColorIndexList 𝓒}

lemma getDualInOtherEquiv_eq (h : l.ContrPerm l2) (i : Fin l.contr.length) :
    l2.contr.val.get (l.contr.getDualInOtherEquiv l2.contr ⟨i, by
    rw [h.2.1]
    exact Finset.mem_univ i⟩).1 = l.contr.val.get i := by
  rw [Index.eq_iff_color_eq_and_id_eq]
  apply And.intro
  · trans (l2.contr.colorMap' ∘ Subtype.val ∘ (l.contr.getDualInOtherEquiv l2.contr)) ⟨i, by
      rw [h.2.1]
      exact Finset.mem_univ i⟩
    · rfl
    · simp only [h.2.2]
      rfl
  · trans l2.contr.idMap (l.contr.getDualInOtherEquiv l2.contr ⟨i, by
      rw [h.2.1]
      exact Finset.mem_univ i⟩).1
    · rfl
    · simp [getDualInOtherEquiv]
      rfl

lemma mem_snd_of_mem_snd (h : l.ContrPerm l2) {I : Index 𝓒.Color} (hI : I ∈ l.contr.val) :
    I ∈ l2.contr.val := by
  have h1 : l.contr.val.indexOf I < l.contr.val.length := List.indexOf_lt_length.mpr hI
  have h2 : I = l.contr.val.get ⟨l.contr.val.indexOf I, h1⟩ := (List.indexOf_get h1).symm
  rw [h2]
  rw [← getDualInOtherEquiv_eq h ⟨l.contr.val.indexOf I, h1⟩]
  simp only [List.get_eq_getElem]
  exact List.getElem_mem _ _ _

lemma countSelf_eq_one_snd_of_countSelf_eq_one_fst (h : l.ContrPerm l2) {I : Index 𝓒.Color}
    (h1 : l.contr.countSelf I = 1) : l2.contr.countSelf I = 1 := by
  refine countSelf_eq_one_of_countId_eq_one l2.contr I ?_ (mem_snd_of_mem_snd h ?_)
  · have h2 := h.2.1
    rw [Subperm.iff_countId] at h2
    refine (h2 I).2 ?_
    have h1 := h2 I
    have h2' := countSelf_le_countId l.contr.toIndexList I
    omega
  · rw [← countSelf_neq_zero, h1]
    exact Nat.one_ne_zero

lemma getDualInOtherEquiv_eq_of_countSelf
    (hn : IndexList.Subperm l.contr l2.contr.toIndexList) (i : Fin l.contr.length)
    (h1 : l2.contr.countId (l.contr.val.get i) = 1)
    (h2 : l2.contr.countSelf (l.contr.val.get i) = 1) :
    l2.contr.val.get (l.contr.getDualInOtherEquiv l2.contr ⟨i, by
      rw [hn]
      exact Finset.mem_univ i⟩).1 = l.contr.val.get i := by
  have h1' : (l.contr.val.get i) ∈ l2.contr.val := by
    rw [← countSelf_neq_zero, h2]
    exact Nat.one_ne_zero
  rw [← List.mem_singleton, ← filter_id_of_countId_eq_one_mem l2.contr.toIndexList h1' h1]
  simp only [List.get_eq_getElem, List.mem_filter, decide_eq_true_eq]
  apply And.intro (List.getElem_mem _ _ _)
  simp [getDualInOtherEquiv]
  change _ = l2.contr.idMap (l.contr.getDualInOtherEquiv l2.contr ⟨i, by
      rw [hn]
      exact Finset.mem_univ i⟩).1
  simp [getDualInOtherEquiv]
  rfl

lemma colorMap_eq_of_countSelf (hn : IndexList.Subperm l.contr l2.contr.toIndexList)
    (h2 : ∀ i, l.contr.countSelf (l.contr.val.get i) = 1
    → l2.contr.countSelf (l.contr.val.get i) = 1) :
    l2.contr.colorMap' ∘ Subtype.val ∘ (l.contr.getDualInOtherEquiv l2.contr)
    = l.contr.colorMap' ∘ Subtype.val := by
  funext a
  simp [colorMap', colorMap]
  change _ = (l.contr.val.get a.1).toColor
  rw [← getDualInOtherEquiv_eq_of_countSelf hn a.1]
  · rfl
  · rw [@Subperm.iff_countId_fin] at hn
    exact (hn a.1).2
  · refine h2 a.1
      (countSelf_eq_one_of_countId_eq_one l.contr.toIndexList (l.contr.val.get a.1) ?h1 ?hme)
    · rw [Subperm.iff_countId_fin] at hn
      exact (hn a.1).1
    · simp
      exact List.getElem_mem l.contr.val (↑↑a) a.1.isLt

lemma iff_count_fin : l.ContrPerm l2 ↔
    l.contr.length = l2.contr.length ∧ IndexList.Subperm l.contr l2.contr.toIndexList ∧
    ∀ i, l.contr.countSelf (l.contr.val.get i) = 1 →
    l2.contr.countSelf (l.contr.val.get i) = 1 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · refine And.intro h.1 (And.intro h.2.1 ?_)
    exact fun i a => countSelf_eq_one_snd_of_countSelf_eq_one_fst h a
  · refine And.intro h.1 (And.intro h.2.1 ?_)
    apply colorMap_eq_of_countSelf h.2.1 h.2.2

lemma iff_count' : l.ContrPerm l2 ↔
    l.contr.length = l2.contr.length ∧ IndexList.Subperm l.contr l2.contr.toIndexList ∧
    ∀ I, l.contr.countSelf I = 1 → l2.contr.countSelf I = 1 := by
  rw [iff_count_fin]
  simp_all only [List.get_eq_getElem, and_congr_right_iff]
  intro _ _
  apply Iff.intro
  · intro ha I hI1
    have hI : I ∈ l.contr.val := by
      rw [← countSelf_neq_zero, hI1]
      exact Nat.one_ne_zero
    have hId : l.contr.val.indexOf I < l.contr.val.length := List.indexOf_lt_length.mpr hI
    have hI' : I = l.contr.val.get ⟨l.contr.val.indexOf I, hId⟩ := (List.indexOf_get hId).symm
    rw [hI'] at hI1 ⊢
    exact ha ⟨l.contr.val.indexOf I, hId⟩ hI1
  · exact fun a i a_1 => a l.contr.val[↑i] a_1

lemma iff_count : l.ContrPerm l2 ↔ l.contr.length = l2.contr.length ∧
    ∀ I, l.contr.countSelf I = 1 → l2.contr.countSelf I = 1 := by
  rw [iff_count']
  refine Iff.intro (fun h => And.intro h.1 h.2.2) (fun h => And.intro h.1 (And.intro ?_ h.2))
  rw [Subperm.iff_countId]
  intro I
  apply And.intro (countId_contr_le_one l I)
  intro h'
  obtain ⟨I', hI1, hI2⟩ := countId_neq_zero_mem l.contr I (ne_zero_of_eq_one h')
  rw [countId_congr _ hI2] at h' ⊢
  have hi := h.2 I' (countSelf_eq_one_of_countId_eq_one l.contr.toIndexList I' h' hI1)
  have h1 := countSelf_le_countId l2.contr.toIndexList I'
  have h2 := countId_contr_le_one l2 I'
  omega

/-- The relation `ContrPerm` is symmetric. -/
@[symm]
lemma symm (h : ContrPerm l l') : ContrPerm l' l := by
  rw [ContrPerm] at h ⊢
  apply And.intro h.1.symm
  apply And.intro (Subperm.symm h.2.1 h.1)
  rw [← Function.comp.assoc, ← h.2.2, Function.comp.assoc, Function.comp.assoc]
  rw [show (l.contr.getDualInOtherEquiv l'.contr) =
    (l'.contr.getDualInOtherEquiv l.contr).symm from rfl]
  simp only [Equiv.symm_comp_self, CompTriple.comp_eq]

lemma iff_countSelf : l.ContrPerm l2 ↔ ∀ I, l.contr.countSelf I = l2.contr.countSelf I := by
  refine Iff.intro (fun h I => ?_) (fun h => ?_)
  · have hs := h.symm
    rw [iff_count] at hs h
    have ht := Iff.intro (fun h1 => h.2 I h1) (fun h2 => hs.2 I h2)
    have h1 : l.contr.countSelf I ≤ 1 := countSelf_contrIndexList_le_one l.toIndexList I
    have h2 : l2.contr.countSelf I ≤ 1 := countSelf_contrIndexList_le_one l2.toIndexList I
    omega
  · rw [iff_count]
    apply And.intro
    · have h1 : l.contr.val.Perm l2.contr.val := by
        rw [List.perm_iff_count]
        intro I
        rw [← countSelf_count, ← countSelf_count]
        exact h I
      exact List.Perm.length_eq h1
    · intro I
      rw [h I]
      exact fun a => a

lemma contr_perm (h : l.ContrPerm l2) : l.contr.val.Perm l2.contr.val := by
  rw [List.perm_iff_count]
  intro I
  rw [← countSelf_count, ← countSelf_count]
  exact iff_countSelf.mp h I

/-- The relation `ContrPerm` is reflexive. -/
@[simp]
lemma refl (l : ColorIndexList 𝓒) : ContrPerm l l :=
  iff_countSelf.mpr (congrFun rfl)

/-- The relation `ContrPerm` is transitive. -/
@[trans]
lemma trans (h1 : ContrPerm l l2) (h2 : ContrPerm l2 l3) : ContrPerm l l3 := by
  rw [iff_countSelf] at h1 h2 ⊢
  exact fun I => (h1 I).trans (h2 I)

/-- `ContrPerm` forms an equivalence relation. -/
lemma equivalence : Equivalence (@ContrPerm 𝓒 _ _) where
  refl := refl
  symm := symm
  trans := trans

lemma symm_trans (h1 : ContrPerm l l2) (h2 : ContrPerm l2 l3) :
    (h1.trans h2).symm = h2.symm.trans h1.symm := rfl

@[simp]
lemma contr_self : ContrPerm l l.contr := by
  rw [iff_countSelf]
  intro I
  simp

@[simp]
lemma self_contr : ContrPerm l.contr l := symm contr_self

lemma length_of_no_contr (h : l.ContrPerm l') (h1 : l.withDual = ∅) (h2 : l'.withDual = ∅) :
    l.length = l'.length := by
  simp only [ContrPerm] at h
  rw [contr_of_withDual_empty l h1, contr_of_withDual_empty l' h2] at h
  exact h.1

lemma mem_withUniqueDualInOther_of_no_contr (h : l.ContrPerm l') (h1 : l.withDual = ∅)
    (h2 : l'.withDual = ∅) : ∀ (x : Fin l.length), x ∈ l.withUniqueDualInOther l'.toIndexList := by
  simp only [ContrPerm] at h
  rw [contr_of_withDual_empty l h1, contr_of_withDual_empty l' h2] at h
  rw [h.2.1]
  exact fun x => Finset.mem_univ x

end ContrPerm

/-!

## Equivalences from `ContrPerm`

-/

open ContrPerm

/-- Given two `ColorIndexList` related by contracted permutations, the equivalence between
  the indices of the corresponding contracted index lists. This equivalence is the
  permutation between the contracted indices. -/
def contrPermEquiv {l l' : ColorIndexList 𝓒} (h : ContrPerm l l') :
    Fin l.contr.length ≃ Fin l'.contr.length :=
  (Equiv.subtypeUnivEquiv (by rw [h.2.1]; exact fun x => Finset.mem_univ x)).symm.trans <|
  (l.contr.getDualInOtherEquiv l'.contr.toIndexList).trans <|
  Equiv.subtypeUnivEquiv (by rw [h.symm.2.1]; exact fun x => Finset.mem_univ x)

lemma contrPermEquiv_colorMap_iso {l l' : ColorIndexList 𝓒} (h : ContrPerm l l') :
    ColorMap.MapIso (contrPermEquiv h).symm l'.contr.colorMap' l.contr.colorMap' := by
  simp [ColorMap.MapIso]
  funext i
  simp [contrPermEquiv, getDualInOtherEquiv]
  have h' := h.symm.2.2
  have hi : i ∈ (l'.contr.withUniqueDualInOther l.contr.toIndexList) := by
    rw [h.symm.2.1]
    exact Finset.mem_univ i
  exact (congrFun h' ⟨i, hi⟩).symm

lemma contrPermEquiv_colorMap_iso' {l l' : ColorIndexList 𝓒} (h : ContrPerm l l') :
    ColorMap.MapIso (contrPermEquiv h) l.contr.colorMap' l'.contr.colorMap' := by
  rw [ColorMap.MapIso.symm']
  exact contrPermEquiv_colorMap_iso h

@[simp]
lemma contrPermEquiv_refl : contrPermEquiv (ContrPerm.refl l) = Equiv.refl _ := by
  simp [contrPermEquiv, ContrPerm.refl]

@[simp]
lemma contrPermEquiv_symm {l l' : ColorIndexList 𝓒} (h : ContrPerm l l') :
    (contrPermEquiv h).symm = contrPermEquiv h.symm := by
  rfl

@[simp]
lemma contrPermEquiv_trans {l l2 l3 : ColorIndexList 𝓒}
    (h1 : ContrPerm l l2) (h2 : ContrPerm l2 l3) :
    (contrPermEquiv h1).trans (contrPermEquiv h2) = contrPermEquiv (h1.trans h2) := by
  simp [contrPermEquiv]
  ext x
  simp only [getDualInOtherEquiv, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply,
    Equiv.coe_fn_mk, Equiv.subtypeUnivEquiv_apply]
  apply congrArg
  have h1' : l.contr.countSelf (l.contr.val.get x) = 1 := by simp [contr]
  rw [iff_countSelf.mp h1, iff_countSelf.mp h2] at h1'
  have h3 : l3.contr.countId (l.contr.val.get x) = 1 := by
    have h' := countSelf_le_countId l3.contr.toIndexList (l.contr.val.get x)
    have h'' := countId_contr_le_one l3 (l.contr.val.get x)
    omega
  rw [countId_get_other, List.countP_eq_length_filter, List.length_eq_one] at h3
  obtain ⟨a, ha⟩ := h3
  trans a
  · rw [← List.mem_singleton, ← ha]
    simp [AreDualInOther]
  · symm
    rw [← List.mem_singleton, ← ha]
    simp [AreDualInOther]

@[simp]
lemma contrPermEquiv_self_contr {l : ColorIndexList 𝓒} :
    contrPermEquiv (contr_self : ContrPerm l l.contr) =
    (Fin.castOrderIso (by simp)).toEquiv := by
  simp [contrPermEquiv]
  ext1 x
  simp only [getDualInOtherEquiv, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply,
    Equiv.coe_fn_mk, Equiv.subtypeUnivEquiv_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
    Fin.coe_cast]
  symm
  have h1' : l.contr.countSelf (l.contr.val.get x) = 1 := by simp [contr]
  rw [iff_countSelf.mp contr_self] at h1'
  have h3 : l.contr.contr.countId (l.contr.val.get x) = 1 := by
    have h' := countSelf_le_countId l.contr.contr.toIndexList (l.contr.val.get x)
    have h'' := countId_contr_le_one l.contr (l.contr.val.get x)
    omega
  rw [countId_get_other, List.countP_eq_length_filter, List.length_eq_one] at h3
  obtain ⟨a, ha⟩ := h3
  trans a
  · rw [← List.mem_singleton, ← ha]
    simp [AreDualInOther]
  · symm
    rw [← List.mem_singleton, ← ha]
    simp only [AreDualInOther, List.mem_filter, List.mem_finRange,
      decide_eq_true_eq, true_and, getDualInOther?_id]

@[simp]
lemma contrPermEquiv_contr_self {l : ColorIndexList 𝓒} :
    contrPermEquiv (self_contr : ContrPerm l.contr l) =
    (Fin.castOrderIso (by simp)).toEquiv := by
  rw [← contrPermEquiv_symm, contrPermEquiv_self_contr]
  rfl

/-- Given two `ColorIndexList` related by permutations and without duals, the equivalence between
  the indices of the corresponding index lists. This equivalence is the
  permutation between the indices. -/
def permEquiv {l l' : ColorIndexList 𝓒} (h : ContrPerm l l')
    (h1 : l.withDual = ∅) (h2 : l'.withDual = ∅) : Fin l.length ≃ Fin l'.length :=
  (Equiv.subtypeUnivEquiv (mem_withUniqueDualInOther_of_no_contr h h1 h2)).symm.trans <|
  (l.getDualInOtherEquiv l'.toIndexList).trans <|
  Equiv.subtypeUnivEquiv (mem_withUniqueDualInOther_of_no_contr h.symm h2 h1)

lemma permEquiv_colorMap_iso {l l' : ColorIndexList 𝓒} (h : ContrPerm l l')
    (h1 : l.withDual = ∅) (h2 : l'.withDual = ∅) :
    ColorMap.MapIso (permEquiv h h1 h2).symm l'.colorMap' l.colorMap' := by
  funext i
  rw [Function.comp_apply]
  have h' := h.symm
  simp only [ContrPerm] at h'
  rw [contr_of_withDual_empty l h1, contr_of_withDual_empty l' h2] at h'
  exact (congrFun h'.2.2 ⟨i, _⟩).symm

end ColorIndexList

end IndexNotation
