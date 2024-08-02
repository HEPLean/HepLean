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
  haveI : IsEmpty (s.contrSubtype) := s.hasNoContr_is_empty h
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

/-- An equivalence between two coppies of `𝓒.contrPairSet s` and `𝓒.contrSubtype s`.
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

/-!

## Equivalence relation on IndexListColor

-/

/-- Two index lists are related if there contracted lists have the same id's for indices,
  and the color of indices with the same id sit are the same.
  This will allow us to add and compare tensors. -/
def rel (s1 s2 : IndexListColor 𝓒) : Prop :=
  List.Perm (s1.contr.1.map Index.id) (s2.contr.1.map Index.id)
  ∧ ∀ (l1 : s1.contr.1.toPosFinset)
      (l2 : s2.contr.1.toPosFinset),
      l1.1.2.id = l2.1.2.id → l1.1.2.toColor = l2.1.2.toColor

/-! TODO: Show that `rel` is indeed an equivalence relation. -/

/-!

## Appending two IndexListColor

-/

/-- Appending two `IndexListColor` whose correpsonding appended index list
  satisfies `IndexListColorProp`. -/
def append (s1 s2 : IndexListColor 𝓒) (h : IndexListColorProp 𝓒 (s1.1 ++ s2.1)) :
    IndexListColor 𝓒 := ⟨s1.1 ++ s2.1, h⟩

@[simp]
lemma append_length {s1 s2 : IndexListColor 𝓒} (h : IndexListColorProp 𝓒 (s1.1 ++ s2.1))
    (h1 : n = s1.1.length) (h2 : m = s2.1.length) :
    n + m = (append s1 s2 h).1.length := by
  erw [List.length_append]
  simp only [h1, h2]

end IndexListColor

end IndexNotation
