/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.ColorIndexList.Basic
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexList.Contraction
import HepLean.SpaceTime.LorentzTensor.Contraction
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
/-!

# Contraction of ColorIndexLists

We define the contraction of ColorIndexLists.

-/

namespace IndexNotation
namespace ColorIndexList

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
  (l l2 : ColorIndexList 𝓒)

open IndexList TensorColor

/-!

## Contracting an `ColorIndexList`

-/

/-- The contraction of a `ColorIndexList`, `l`.
  That is, the `ColorIndexList` obtained by taking only those indices in `l` which do not
  have a dual. This can be thought of as contracting all of those indices with a dual. -/
def contr : ColorIndexList 𝓒 where
  toIndexList := l.toIndexList.contrIndexList
  unique_duals := by
    simp [OnlyUniqueDuals]
  dual_color := ColorCond.contrIndexList

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
    exact (Finset.card_fin l.contrIndexList.length).symm

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
    exact (Finset.card_fin l.contrIndexList.length).symm

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

lemma contr_countId_eq_zero_of_countId_zero (I : Index 𝓒.Color)
    (h : l.countId I = 0) : l.contr.countId I = 0 := by
  simp [contr]
  exact countId_contrIndexList_zero_of_countId l.toIndexList I h

lemma contr_countId_eq_filter (I : Index 𝓒.Color) :
    l.contr.countId I =
    (l.val.filter (fun J => I.id = J.id)).countP
    (fun i => l.val.countP (fun j => i.id = j.id) = 1) := by
  simp [contr, contrIndexList, countId]
  rw [List.countP_filter, List.countP_filter]
  congr
  funext J
  simp only [decide_eq_true_eq, Bool.decide_and]
  exact Bool.and_comm (decide (I.id = J.id))
    (decide (List.countP (fun j => decide (J.id = j.id)) l.val = 1))

lemma countId_contr_le_one (I : Index 𝓒.Color) :
    l.contr.countId I ≤ 1 := by
  exact l.countId_contrIndexList_le_one I

lemma countId_contr_eq_zero_iff (I : Index 𝓒.Color) :
    l.contr.countId I = 0 ↔ l.countId I = 0 ∨ l.countId I = 2 := by
  by_cases hI : l.contr.countId I = 1
  · have hI' := hI
    erw [countId_contrIndexList_eq_one_iff_countId_eq_one] at hI'
    omega
  · have hI' := hI
    erw [countId_contrIndexList_eq_one_iff_countId_eq_one] at hI'
    have hI2 := l.countId_le_two I
    have hI3 := l.countId_contrIndexList_le_one I
    have hI3 : l.contr.countId I = 0 := by
      simp_all only [contr]
      omega
    omega

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
  rw [l.unique_duals]
  exact fun x => Eq.to_iff rfl))
    (Fin.castOrderIso l.contrIndexList_length).toEquiv).trans <|
  l.dualEquiv

lemma contrEquiv_inl_inl_isSome (i : l.withUniqueDualLT) :
    (l.getDual? (l.contrEquiv (Sum.inl (Sum.inl i)))).isSome :=
  mem_withUniqueDual_isSome l.toIndexList (↑i)
    (mem_withUniqueDual_of_mem_withUniqueDualLt l.toIndexList (↑i) i.2)

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
  simp only [ColorMap.MapIso, ColorMap.contr, Equiv.coe_refl, CompTriple.comp_eq]
  funext i
  simp only [contr, Function.comp_apply, contrIndexList_colorMap]
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
    exact (Finset.card_fin l.length).symm

end ColorIndexList
end IndexNotation
