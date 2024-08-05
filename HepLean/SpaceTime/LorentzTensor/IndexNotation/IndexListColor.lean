/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Basic
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Index lists with color conditions

Here we consider `IndexListColor` which is a subtype of all lists of indices
on those where the elements to be contracted have consistent colors with respect to
a Tensor Color structure.

-/

namespace IndexNotation

open IndexNotation

variable (𝓒 : TensorColor)
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

/-- An index list is allowed if every contracting index has exactly one dual,
  and the color of the dual is dual to the color of the index. -/
def IndexListColorProp (l : IndexList 𝓒.Color) : Prop :=
  (∀ (i j : l.contrSubtype), l.getDualProp i j.1 → j = l.getDual i) ∧
  (∀ (i : l.contrSubtype), l.colorMap i.1 = 𝓒.τ (l.colorMap (l.getDual i).1))

/-- The type of index lists which satisfy `IndexListColorProp`. -/
def IndexListColor : Type := {s : IndexList 𝓒.Color // IndexListColorProp 𝓒 s}

namespace IndexListColor

open IndexList

variable {𝓒 : TensorColor}
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
variable (l : IndexListColor 𝓒)
instance : Coe (IndexListColor 𝓒) (IndexList 𝓒.Color) := ⟨fun x => x.val⟩

lemma indexListColorProp_of_hasNoContr {s : IndexList 𝓒.Color} (h : s.HasNoContr) :
    IndexListColorProp 𝓒 s := by
  simp [IndexListColorProp]
  haveI : IsEmpty (s.contrSubtype) := s.contrSubtype_is_empty_of_hasNoContr h
  simp

/-!

## Contraction pairs for IndexListColor

-/

/-! TODO: Would be nice to get rid of all of the `.1` which appear here. -/
@[simp]
lemma getDual_getDual (i : l.1.contrSubtype) :
    l.1.getDual (l.1.getDual i) = i := by
  refine (l.prop.1 (l.1.getDual i) i ?_).symm
  simp [getDualProp]
  apply And.intro
  exact Subtype.coe_ne_coe.mpr (l.1.getDual_neq_self i).symm
  exact (l.1.getDual_id i).symm

lemma contrPairSet_fst_eq_dual_snd (x : l.1.contrPairSet) : x.1.1 = l.1.getDual x.1.2 :=
  (l.prop.1 (x.1.2) x.1.1 (And.intro (Fin.ne_of_gt x.2.1) x.2.2.symm))

lemma contrPairSet_snd_eq_dual_fst (x : l.1.contrPairSet) : x.1.2 = l.1.getDual x.1.1 := by
  rw [contrPairSet_fst_eq_dual_snd, getDual_getDual]

lemma contrPairSet_dual_snd_lt_self (x : l.1.contrPairSet) :
    (l.1.getDual x.1.2).1 < x.1.2.1 := by
  rw [← l.contrPairSet_fst_eq_dual_snd]
  exact x.2.1

/-- An equivalence between two coppies of `l.1.contrPairSet` and `l.1.contrSubtype`.
  This equivalence exists due to the ordering on pairs in `𝓒.contrPairSet s`. -/
def contrPairEquiv : l.1.contrPairSet ⊕ l.1.contrPairSet ≃ l.1.contrSubtype where
  toFun x :=
    match x with
    | Sum.inl p => p.1.2
    | Sum.inr p => p.1.1
  invFun x :=
    if h : (l.1.getDual x).1 < x.1 then
      Sum.inl ⟨(l.1.getDual x, x), l.1.getDual_lt_self_mem_contrPairSet h⟩
    else
      Sum.inr ⟨(x, l.1.getDual x), l.1.getDual_not_lt_self_mem_contrPairSet h⟩
  left_inv x := by
    match x with
    | Sum.inl x =>
      simp only [Subtype.coe_lt_coe]
      rw [dif_pos]
      simp [← l.contrPairSet_fst_eq_dual_snd]
      exact l.contrPairSet_dual_snd_lt_self _
    | Sum.inr x =>
      simp only [Subtype.coe_lt_coe]
      rw [dif_neg]
      simp only [← l.contrPairSet_snd_eq_dual_fst, Prod.mk.eta, Subtype.coe_eta]
      rw [← l.contrPairSet_snd_eq_dual_fst]
      have h1 := x.2.1
      simp only [not_lt, ge_iff_le]
      exact le_of_lt h1
  right_inv x := by
    by_cases h1 : (l.1.getDual x).1 < x.1
    simp only [h1, ↓reduceDIte]
    simp only [h1, ↓reduceDIte]

@[simp]
lemma contrPairEquiv_apply_inr (x : l.1.contrPairSet) : l.contrPairEquiv (Sum.inr x) = x.1.1 := by
  simp [contrPairEquiv]

@[simp]
lemma contrPairEquiv_apply_inl(x : l.1.contrPairSet) : l.contrPairEquiv (Sum.inl x) = x.1.2 := by
  simp [contrPairEquiv]

/-- An equivalence between `Fin s.length` and
  `(𝓒.contrPairSet s ⊕ 𝓒.contrPairSet s) ⊕ Fin (𝓒.noContrFinset s).card`, which
  can be used for contractions. -/
def splitContr : Fin l.1.length ≃
    (l.1.contrPairSet ⊕ l.1.contrPairSet) ⊕ Fin (l.1.noContrFinset).card :=
  (Equiv.sumCompl l.1.NoContr).symm.trans <|
  (Equiv.sumComm { i // l.1.NoContr i} { i // ¬ l.1.NoContr i}).trans <|
  Equiv.sumCongr l.contrPairEquiv.symm l.1.noContrSubtypeEquiv

lemma splitContr_map :
    l.1.colorMap ∘ l.splitContr.symm ∘ Sum.inl ∘ Sum.inl =
    𝓒.τ ∘ l.1.colorMap ∘ l.splitContr.symm ∘ Sum.inl ∘ Sum.inr := by
  funext x
  simp [splitContr, contrPairEquiv_apply_inr]
  erw [contrPairEquiv_apply_inr, contrPairEquiv_apply_inl]
  rw [contrPairSet_fst_eq_dual_snd _ _]
  exact l.prop.2 _

/-!

## The contracted index list

-/

/-- The contracted index list as a `IndexListColor`. -/
def contr : IndexListColor 𝓒 :=
  ⟨l.1.contrIndexList, indexListColorProp_of_hasNoContr l.1.contrIndexList_hasNoContr⟩

/-- Contracting twice is equivalent to contracting once. -/
@[simp]
lemma contr_contr : l.contr.contr = l.contr := by
  apply Subtype.ext
  exact l.1.contrIndexList_contrIndexList

@[simp]
lemma contr_numIndices : l.contr.1.numIndices = l.1.noContrFinset.card :=
  l.1.contrIndexList_numIndices

lemma contr_colorMap :
    l.1.colorMap ∘ l.splitContr.symm ∘ Sum.inr = l.contr.1.colorMap ∘
    (Fin.castOrderIso l.contr_numIndices.symm).toEquiv.toFun := by
  funext x
  simp only [Function.comp_apply, colorMap, List.get_eq_getElem, contr, contrIndexList, fromFinMap,
    Equiv.toFun_as_coe, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.coe_cast,
    List.getElem_map, Fin.getElem_list, Fin.cast_mk, Fin.eta]
  rfl

/-! TODO: Prove applying contr twice equals applying it once. -/
/-!

## Equivalence relation on IndexListColor due to permutation

-/

/-- Two index lists are related if there contracted lists have the same id's for indices,
  and the color of indices with the same id sit are the same.
  This will allow us to add and compare tensors. -/
def PermContr (s1 s2 : IndexListColor 𝓒) : Prop :=
  List.Perm (s1.contr.1.map Index.id) (s2.contr.1.map Index.id)
  ∧ ∀ (i : Fin s1.contr.1.length) (j : Fin s2.contr.1.length),
      s1.contr.1.idMap i = s2.contr.1.idMap j →
      s1.contr.1.colorMap i = s2.contr.1.colorMap j

lemma PermContr.refl : Reflexive (@PermContr 𝓒 _) := by
  intro l
  simp only [PermContr, List.Perm.refl, true_and]
  have h1 : l.contr.1.HasNoContr := l.1.contrIndexList_hasNoContr
  exact fun i j a => hasNoContr_color_eq_of_id_eq (↑l.contr) h1 i j a

lemma PermContr.symm : Symmetric (@PermContr 𝓒 _) :=
  fun _ _ h => And.intro (List.Perm.symm h.1) fun i j hij => (h.2 j i hij.symm).symm

/-- Given an index in `s1` the index in `s2` related by `PermContr` with the same id. -/
def PermContr.get {s1 s2 : IndexListColor 𝓒} (h : PermContr s1 s2) (i : Fin s1.contr.1.length) :
    Fin s2.contr.1.length :=
  (Fin.find (fun j => s1.contr.1.idMap i = s2.contr.1.idMap j)).get (by
    rw [Fin.isSome_find_iff]
    have h2 : s1.contr.1.idMap i ∈ (List.map Index.id s2.contr.1) := by
      rw [← List.Perm.mem_iff h.1]
      simp only [List.mem_map]
      use s1.contr.1.get i
      simp_all only [true_and, List.get_eq_getElem]
      apply And.intro
      · exact List.getElem_mem (s1.contr.1) (↑i) i.isLt
      · rfl
    simp only [List.mem_map] at h2
    obtain ⟨j, hj1, hj2⟩ := h2
    obtain ⟨j', hj'⟩ := List.mem_iff_get.mp hj1
    use j'
    rw [← hj2]
    simp [idMap, hj']
    change _ = (s2.contr.1.get j').id
    rw [hj'])

lemma PermContr.some_get_eq_find {s1 s2 : IndexListColor 𝓒} (h : PermContr s1 s2)
    (i : Fin s1.contr.1.length) :
    Fin.find (fun j => s1.contr.1.idMap i = s2.contr.1.idMap j) = some (h.get i) := by
  simp [PermContr.get]

lemma PermContr.get_id {s1 s2 : IndexListColor 𝓒} (h : PermContr s1 s2)
    (i : Fin s1.contr.1.length) :
    s2.contr.1.idMap (h.get i) = s1.contr.1.idMap i := by
  have h1 := h.some_get_eq_find i
  rw [Fin.find_eq_some_iff] at h1
  exact h1.1.symm

lemma PermContr.get_unique {s1 s2 : IndexListColor 𝓒} (h : PermContr s1 s2)
    {i : Fin s1.contr.1.length} {j : Fin s2.contr.1.length}
    (hij : s1.contr.1.idMap i = s2.contr.1.idMap j) :
    j = h.get i := by
  by_contra hn
  refine (?_ : ¬ s2.contr.1.NoContr j) (s2.1.contrIndexList_hasNoContr j)
  simp [NoContr]
  use PermContr.get h i
  apply And.intro hn
  rw [← hij, PermContr.get_id]

@[simp]
lemma PermContr.get_symm_apply_get_apply {s1 s2 : IndexListColor 𝓒} (h : PermContr s1 s2)
    (i : Fin s1.contr.1.length) : h.symm.get (h.get i) = i :=
  (h.symm.get_unique (h.get_id i)).symm

lemma PermContr.get_apply_get_symm_apply {s1 s2 : IndexListColor 𝓒} (h : PermContr s1 s2)
    (i : Fin s2.contr.1.length) : h.get (h.symm.get i) = i :=
  (h.get_unique (h.symm.get_id i)).symm

/-- Equivalence of indexing types for two `IndexListColor` related by `PermContr`. -/
def PermContr.toEquiv {s1 s2 : IndexListColor 𝓒} (h : PermContr s1 s2) :
    Fin s1.contr.1.length ≃ Fin s2.contr.1.length where
  toFun := h.get
  invFun := h.symm.get
  left_inv x := by
    simp
  right_inv x := by
    simp

lemma PermContr.toEquiv_symm {s1 s2 : IndexListColor 𝓒} (h : PermContr s1 s2) :
    h.toEquiv.symm = h.symm.toEquiv := by
  rfl

lemma PermContr.toEquiv_colorMap {s1 s2 : IndexListColor 𝓒} (h : PermContr s1 s2) :
    s2.contr.1.colorMap = s1.contr.1.colorMap ∘ h.toEquiv.symm := by
  funext x
  refine (h.2 _ _ ?_).symm
  simp [← h.get_id, toEquiv]

/-! TODO: Show that `rel` is indeed an equivalence relation. -/

/-!

## Appending two IndexListColor

-/

/-- Appending two `IndexListColor` whose correpsonding appended index list
  satisfies `IndexListColorProp`. -/
def prod (s1 s2 : IndexListColor 𝓒) (h : IndexListColorProp 𝓒 (s1.1 ++ s2.1)) :
    IndexListColor 𝓒 := ⟨s1.1 ++ s2.1, h⟩

lemma prod_numIndices {s1 s2 : IndexListColor 𝓒} :
    (s1.1 ++ s2.1).numIndices = s1.1.numIndices + s2.1.numIndices :=
  List.length_append s1.1 s2.1

lemma prod_colorMap {s1 s2 : IndexListColor 𝓒} (h : IndexListColorProp 𝓒 (s1.1 ++ s2.1)) :
    Sum.elim s1.1.colorMap s2.1.colorMap =
    (s1.prod s2 h).1.colorMap ∘ ((Fin.castOrderIso prod_numIndices).toEquiv.trans
    finSumFinEquiv.symm).symm := by
  funext x
  match x with
  | Sum.inl x =>
    simp [prod, colorMap, fromFinMap]
    rw [List.getElem_append_left]
  | Sum.inr x =>
    simp [prod, colorMap, fromFinMap]
    rw [List.getElem_append_right]
    simp [numIndices]
    simp [numIndices]
    simp [numIndices]
end IndexListColor

end IndexNotation
