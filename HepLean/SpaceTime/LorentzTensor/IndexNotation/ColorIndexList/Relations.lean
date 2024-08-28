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

# Index lists with color conditions

Here we consider `IndexListColor` which is a subtype of all lists of indices
on those where the elements to be contracted have consistent colors with respect to
a Tensor Color structure.

-/

namespace IndexNotation

namespace ColorIndexList

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

variable (l l' : ColorIndexList 𝓒)
open IndexList TensorColor
/-!

## Reindexing

-/

/--
  Two `ColorIndexList` are said to be reindexes of one another if they:
    1. have the same length.
    2. every corresponding index has the same color, and duals which correspond.

  Note: This does not allow for reordrings of indices.
-/
def Reindexing : Prop := l.length = l'.length ∧
  ∀ (h : l.length = l'.length), l.colorMap = l'.colorMap ∘ Fin.cast h ∧
    l.getDual? = Option.map (Fin.cast h.symm) ∘ l'.getDual? ∘ Fin.cast h

namespace Reindexing

variable {l l' l2 l3 : ColorIndexList 𝓒}

/-- The relation `Reindexing` is symmetric. -/
@[symm]
lemma symm (h : Reindexing l l') : Reindexing l' l := by
  apply And.intro h.1.symm
  intro h'
  have h2 := h.2 h.1
  apply And.intro
  · rw [h2.1]
    funext a
    simp only [Function.comp_apply, Fin.cast_trans, Fin.cast_eq_self]
  · rw [h2.2]
    funext a
    simp only [Function.comp_apply, Fin.cast_trans, Fin.cast_eq_self, Option.map_map]
    have h1 (h : l.length = l'.length) : Fin.cast h ∘ Fin.cast h.symm = id := by
      funext a
      simp only [Function.comp_apply, Fin.cast_trans, Fin.cast_eq_self, id_eq]
    rw [h1]
    simp only [Option.map_id', id_eq]

/-- The relation `Reindexing` is reflexive. -/
@[simp]
lemma refl (l : ColorIndexList 𝓒) : Reindexing l l := by
  apply And.intro rfl
  intro h
  apply And.intro
  · funext a
    rfl
  · funext a
    simp only [Fin.cast_refl, Option.map_id', CompTriple.comp_eq, Function.comp_apply, id_eq]

/-- The relation `Reindexing` is transitive. -/
@[trans]
lemma trans (h1 : Reindexing l l2) (h2 : Reindexing l2 l3) : Reindexing l l3 := by
  apply And.intro (h1.1.trans h2.1)
  intro h'
  have h1' := h1.2 h1.1
  have h2' := h2.2 h2.1
  apply And.intro
  · simp only [h1'.1, h2'.1]
    funext a
    rfl
  · simp only [h1'.2, h2'.2]
    funext a
    simp only [Function.comp_apply, Fin.cast_trans, Option.map_map]
    apply congrFun
    apply congrArg
    funext a
    rfl

/-- `Reindexing` forms an equivalence relation. -/
lemma equivalence : Equivalence (@Reindexing 𝓒 _) where
  refl := refl
  symm := symm
  trans := trans

/-! TODO: Prove that `Reindexing l l2` implies `Reindexing l.contr l2.contr`. -/
end Reindexing

/-!

## Permutation

Test whether two `ColorIndexList`s are permutations of each other.
To prevent choice problems, this has to be done after contraction.

-/

/--
  Two `ColorIndexList`s are said to be related by contracted permutations, `ContrPerm`,
  if and only if:

    1) Their contractions are the same length.
    2) Every index in the contracted list of one has a unqiue dual in the contracted
      list of the other and that dual has a the same color.
-/
def ContrPerm : Prop :=
  l.contr.length = l'.contr.length ∧
  IndexList.Subperm l.contr l'.contr.toIndexList  ∧
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
    · simp
      rfl
    · simp only [h.2.2]
      rfl
  · trans l2.contr.idMap (l.contr.getDualInOtherEquiv l2.contr ⟨i, by
      rw [h.2.1]
      exact Finset.mem_univ i⟩).1
    · simp
      rfl
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
  refine countSelf_eq_one_of_countId_eq_one l2.contr I ?_ (mem_snd_of_mem_snd h ?_ )
  · have h2 := h.2.1
    rw [Subperm.iff_countId] at h2
    refine (h2 I).2 ?_
    have h1 := h2 I
    have h2' := countSelf_le_countId l.contr.toIndexList I
    omega
  · rw [← countSelf_neq_zero, h1]
    simp

lemma getDualInOtherEquiv_eq_of_countSelf
    (hn : IndexList.Subperm l.contr l2.contr.toIndexList) (i : Fin l.contr.length)
    (h1 : l2.contr.countId (l.contr.val.get i) = 1)
    (h2 : l2.contr.countSelf (l.contr.val.get i) = 1) :
    l2.contr.val.get (l.contr.getDualInOtherEquiv l2.contr ⟨i, by
      rw [hn]
      exact Finset.mem_univ i⟩).1 = l.contr.val.get i := by
  have h1' : (l.contr.val.get i) ∈ l2.contr.val := by
    rw [← countSelf_neq_zero, h2]
    simp
  rw [← List.mem_singleton, ← filter_id_of_countId_eq_one_mem l2.contr.toIndexList h1' h1 ]
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
    l.contr.length = l2.contr.length  ∧ IndexList.Subperm l.contr l2.contr.toIndexList ∧
    ∀ i, l.contr.countSelf (l.contr.val.get i) = 1 →
    l2.contr.countSelf (l.contr.val.get i) = 1 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · refine And.intro h.1 (And.intro h.2.1 ?_)
    exact fun i a => countSelf_eq_one_snd_of_countSelf_eq_one_fst h a
  · refine And.intro h.1 (And.intro h.2.1 ?_)
    apply colorMap_eq_of_countSelf h.2.1 h.2.2

lemma iff_count' : l.ContrPerm l2 ↔
    l.contr.length = l2.contr.length ∧ IndexList.Subperm l.contr l2.contr.toIndexList ∧
    ∀ I, l.contr.countSelf I = 1 → l2.contr.countSelf I = 1  := by
  rw [iff_count_fin]
  simp_all only [List.get_eq_getElem, and_congr_right_iff]
  intro _ _
  apply Iff.intro
  · intro ha I hI1
    have hI : I ∈ l.contr.val := by
      rw [← countSelf_neq_zero, hI1]
      simp
    have hId : l.contr.val.indexOf I < l.contr.val.length := List.indexOf_lt_length.mpr hI
    have hI' : I = l.contr.val.get ⟨l.contr.val.indexOf I, hId⟩ := (List.indexOf_get hId).symm
    rw [hI'] at hI1 ⊢
    exact ha ⟨l.contr.val.indexOf I, hId⟩ hI1
  · intro a_2 i a_3
    simp_all only

lemma iff_count :  l.ContrPerm l2 ↔ l.contr.length = l2.contr.length ∧
    ∀ I, l.contr.countSelf I = 1 → l2.contr.countSelf I = 1 := by
  rw [iff_count']
  refine Iff.intro (fun h => And.intro h.1 h.2.2) (fun h => And.intro h.1 (And.intro ?_ h.2))
  rw [Subperm.iff_countId]
  intro I
  apply And.intro (countId_contr_le_one l I)
  intro h'
  obtain ⟨I', hI1, hI2⟩ := countId_neq_zero_mem l.contr I (by omega)
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
      exact List.Perm.length_eq  h1
    · intro I
      rw [h I]
      simp

lemma contr_perm (h : l.ContrPerm l2) : l.contr.val.Perm l2.contr.val := by
  rw [List.perm_iff_count]
  intro I
  rw [← countSelf_count, ← countSelf_count]
  exact iff_countSelf.mp h I

/-- The relation `ContrPerm` is reflexive. -/
@[simp]
lemma refl (l : ColorIndexList 𝓒) : ContrPerm l l := by
 rw [iff_countSelf]
 exact fun I => rfl

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
    (h1.trans h2).symm = h2.symm.trans h1.symm := by
  simp only

@[simp]
lemma contr_self : ContrPerm l l.contr := by
  rw [iff_countSelf]
  intro I
  simp

@[simp]
lemma self_contr : ContrPerm l.contr l := by
  symm
  simp

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
  intro x
  exact Finset.mem_univ x

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
  have hn := congrFun h' ⟨i, hi⟩
  simp at hn
  rw [← hn]
  rfl

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
  simp only [contrPermEquiv]
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
  have h3 : l3.contr.countId  (l.contr.val.get x) = 1 := by
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
  have h3 : l.contr.contr.countId  (l.contr.val.get x) = 1 := by
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
    contrPermEquiv (by simp : ContrPerm l.contr l) =
    (Fin.castOrderIso (by simp)).toEquiv := by
  rw [← contrPermEquiv_symm, contrPermEquiv_self_contr]
  simp

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
  simp [ColorMap.MapIso]
  funext i
  simp [contrPermEquiv, getDualInOtherEquiv]
  have h' := h.symm
  simp only [ContrPerm] at h'
  rw [contr_of_withDual_empty l h1, contr_of_withDual_empty l' h2] at h'
  have hi : i ∈ (l'.withUniqueDualInOther l.toIndexList) := by
    rw [h'.2.1]
    exact Finset.mem_univ i
  have hn := congrFun h'.2.2 ⟨i, hi⟩
  simp at hn
  rw [← hn]
  rfl

end ColorIndexList

end IndexNotation
