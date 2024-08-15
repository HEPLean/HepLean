/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Dual
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
import HepLean.SpaceTime.LorentzTensor.Contraction
/-!

# Index lists with color conditions

Here we consider `IndexListColor` which is a subtype of all lists of indices
on those where the elements to be contracted have consistent colors with respect to
a Tensor Color structure.

-/

namespace IndexNotation


namespace IndexList

variable {𝓒 : TensorColor}
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
variable (l l2 l3 : IndexList 𝓒.Color)

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
        simp
        exact  hi
      simp only [Function.comp_apply, h'', Option.map_some']
      rw [show l.getDual? ↑i = some ((l.getDual? i).get hi) by simp]
      rw [Option.map_some']
      simp
      have hii := h ⟨i, by simp [withDual, hi]⟩
      simp at hii
      rw [← hii]
      exact (𝓒.τ_involutive _).symm
    · simp [Option.guard, hi]
      exact Option.not_isSome_iff_eq_none.mp hi

lemma iff_on_isSome : l.ColorCond ↔ ∀ (i : Fin l.length) (h : (l.getDual? i).isSome), 𝓒.τ
    (l.colorMap ((l.getDual? i).get h)) = l.colorMap i := by
  rw [iff_withDual]
  simp

lemma assoc (h : ColorCond (l ++ l2 ++ l3)) :
    ColorCond (l ++ (l2 ++ l3)) := by
  rw [← append_assoc]
  exact h

lemma inl (h : ColorCond (l ++ l2)) : ColorCond l := by
  rw [iff_withDual] at h ⊢
  intro i
  have hi' := h ⟨appendEquiv (Sum.inl i), by
    simp_all⟩
  have hn : (Option.map (appendEquiv ∘ Sum.inl) (l.getDual? ↑i) : Option (Fin (l ++ l2).length)) =
        some (appendEquiv (Sum.inl ((l.getDual? i).get (l.withDual_isSome i)))) := by
    trans Option.map (appendEquiv ∘ Sum.inl) (some ((l.getDual? i).get (l.withDual_isSome i)))
    simp
    rw [Option.map_some']
    simp
  simpa [hn] using hi'

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
      simp at hk''
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
    · simp_all
      have hk'' := h (appendEquiv (Sum.inl k))
      simp at hk''
      simp_all
    · simp_all
      have hn' : (l.getDualInOther? l2 k).isSome := by
        simp_all
      have hk'' := h (appendEquiv (Sum.inl k))
      simp at hk''
      simp_all

lemma inr  (hu : (l ++ l2).withUniqueDual = (l ++ l2).withDual) (h : ColorCond (l ++ l2)) :
    ColorCond l2 := inl (symm hu h)

lemma triple_right  (hu : (l ++ l2 ++ l3).withUniqueDual = (l ++ l2 ++ l3).withDual)
    (h : ColorCond (l ++ l2 ++ l3)) : ColorCond (l2 ++ l3) := by
  have h1 := assoc h
  rw [append_assoc] at hu
  exact h1.inr hu

lemma triple_drop_mid (hu : (l ++ l2 ++ l3).withUniqueDual = (l ++ l2 ++ l3).withDual)
    (h : ColorCond (l ++ l2 ++ l3)) : ColorCond (l ++ l3) := by
  rw [append_assoc] at hu
  refine ((((assoc h).symm hu).assoc).inr ?_).symm ?_
  rw [append_withDual_eq_withUniqueDual_symm, append_assoc] at hu
  exact hu
  rw [append_withDual_eq_withUniqueDual_symm, append_assoc] at hu
  exact append_withDual_eq_withUniqueDual_inr _ _ hu


lemma swap  (hu : (l ++ l2 ++ l3).withUniqueDual = (l ++ l2 ++ l3).withDual)
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
        simp at hn
        simp
        have hL := triple_right hu' hC
        rw [iff_on_isSome] at hL
        have hL' := hL (appendEquiv (Sum.inl k')) (by simp [hn])
        simp_all only [Option.isNone_none, getDualInOther?_append_of_inl,
          getDual?_inl_of_getDual?_isNone_getDualInOther?_isSome, Option.isSome_some,
          getDual?_eq_none_append_inl_iff, Option.get_some, colorMap_append_inr,
          colorMap_append_inl]
      | Sum.inr k' =>
        simp at hn
        simp
        have hR := triple_drop_mid hu' hC
        rw [iff_on_isSome] at hR
        have hR' := hR (appendEquiv (Sum.inl k')) (by simp [hn])
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
    by_cases hk' :  (l3.getDual? k).isSome
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
      · simp_all
        rw [← @Option.not_isSome_iff_eq_none, not_not] at hn
        simp_all
        have hR := triple_drop_mid hu' hC
        rw [iff_on_isSome] at hR
        have hR' := hR (appendEquiv (Sum.inr k)) (by simp [hn])
        simp_all only [getDualInOther?_of_append_of_isNone_isSome, Option.isSome_some,
          getDual?_append_inr_getDualInOther?_isSome, Option.get_some, colorMap_append_inl,
          colorMap_append_inr]

/- l.getDual? = Option.map (𝓒.τ ∘ l.colorMap) ∘
  Option.guard fun i => (l.getDual? i).isSome -/
def bool (l : IndexList 𝓒.Color) : Bool :=
  if (∀ (i : l.withDual),  𝓒.τ
     (l.colorMap ((l.getDual? i).get (l.withDual_isSome i))) = l.colorMap i) then
    true
  else false

lemma iff_bool : l.ColorCond ↔ bool l := by
  rw [iff_withDual, bool]
  simp

end ColorCond



end IndexList


variable (𝓒 : TensorColor)
variable [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

structure ColorIndexList (𝓒 : TensorColor) [IndexNotation 𝓒.Color] extends IndexList 𝓒.Color where
  unique_duals : toIndexList.withDual = toIndexList.withUniqueDual
  dual_color : IndexList.ColorCond toIndexList

namespace ColorIndexList

variable {𝓒 : TensorColor} [IndexNotation 𝓒.Color] [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

variable (l l2 : ColorIndexList 𝓒)
open IndexList TensorColor

instance : Coe (ColorIndexList 𝓒) (IndexList 𝓒.Color) := ⟨fun l => l.toIndexList⟩
def empty : ColorIndexList 𝓒 where
  val := ∅
  unique_duals := by
    rfl
  dual_color := by
    rfl

def colorMap' : 𝓒.ColorMap (Fin l.length) :=
  l.colorMap

@[ext]
lemma ext {l l' : ColorIndexList 𝓒} (h : l.val = l'.val) : l = l' := by
  cases l
  cases l'
  simp_all
  apply IndexList.ext
  exact h


/-! TODO: `orderEmbOfFin_univ` should be replaced with a mathlib lemma if possible. -/
lemma orderEmbOfFin_univ (n m : ℕ) (h : n = m):
    Finset.orderEmbOfFin (Finset.univ : Finset (Fin n)) (by simp [h]: Finset.univ.card = m) =
    (Fin.castOrderIso h.symm).toOrderEmbedding := by
  symm
  have h1 : (Fin.castOrderIso h.symm).toFun =
     ( Finset.orderEmbOfFin (Finset.univ : Finset (Fin n)) (by simp [h]: Finset.univ.card = m)).toFun := by
    apply Finset.orderEmbOfFin_unique
    intro x
    exact Finset.mem_univ ((Fin.castOrderIso (Eq.symm h)).toFun x)
    exact fun ⦃a b⦄ a => a
  exact Eq.symm (Fin.orderEmbedding_eq (congrArg Set.range (id (Eq.symm h1))))


/-!

## Contracting an `ColorIndexList`

-/

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
  simp [contr]
  apply congrArg
  simp [withoutDualEquiv]
  have h1 : l.contrIndexList.withoutDual = Finset.univ := by
    have hx := l.contrIndexList.withDual_union_withoutDual
    have hx2 := l.contrIndexList_withDual
    simp_all
  simp [h1]
  rw [orderEmbOfFin_univ]
  rfl
  rw [h1]
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

def contrEquiv : (l.withUniqueDualLT ⊕ l.withUniqueDualLT) ⊕ Fin l.contr.length ≃ Fin l.length :=
  (Equiv.sumCongr (l.withUniqueLTGTEquiv) (Equiv.refl _)).trans <|
  (Equiv.sumCongr (Equiv.subtypeEquivRight (by
  simp [l.unique_duals])) (Fin.castOrderIso l.contrIndexList_length).toEquiv).trans <|
  l.dualEquiv

lemma contrEquiv_inl_inl_isSome (i : l.withUniqueDualLT) :
    (l.getDual? (l.contrEquiv (Sum.inl (Sum.inl i)))).isSome := by
  change (l.getDual? i).isSome
  have h1 : i.1 ∈ l.withUniqueDual := by
    have hi2 := i.2
    simp [withUniqueDualLT] at hi2
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
  simp [ColorMap.ContrCond]
  funext i
  simp
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
  rfl
  rw [h]
  simp

/-!

## Append

-/


def AppendCond : Prop :=
  (l.toIndexList ++ l2.toIndexList).withUniqueDual = (l.toIndexList ++ l2.toIndexList).withDual
  ∧ ColorCond (l.toIndexList ++ l2.toIndexList)

def append (h : AppendCond l l2) : ColorIndexList 𝓒 where
  toIndexList := l.toIndexList ++ l2.toIndexList
  unique_duals := h.1.symm
  dual_color := h.2

scoped[IndexNotation.ColorIndexList] notation l " ++["h"] " l2 => append l l2 h

@[simp]
lemma append_toIndexList (h : AppendCond l l2) :
    (l ++[h] l2).toIndexList = l.toIndexList ++ l2.toIndexList := by
  rfl

namespace AppendCond

variable {l l2 l3 : ColorIndexList 𝓒}

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
  · simp
    rw [← append_withDual_eq_withUniqueDual_swap]
    simpa using h'.1
  · exact ColorCond.swap h'.1 h'.2
/-
(l ++ l2).withUniqueDual = (l ++ l2).withDual ↔
    l.withUniqueDual = l.withDual ∧ l2.withUniqueDual = l2.withDual
    ∧ l.withUniqueDualInOther l2 = l.withDualInOther l2 ∧
    l2.withUniqueDualInOther l = l2.withDualInOther l -/
lemma appendCond_of_eq (h1 : l.withUniqueDual = l.withDual)
    (h2 : l2.withUniqueDual = l2.withDual)
    (h3 : l.withUniqueDualInOther l2 = l.withDualInOther l2)
    (h4 : l2.withUniqueDualInOther l = l2.withDualInOther l)
    (h5 : ColorCond.bool (l.toIndexList ++ l2.toIndexList)) :
    AppendCond l l2 := by
  rw [AppendCond]
  rw [append_withDual_eq_withUniqueDual_iff']
  simp_all
  exact ColorCond.iff_bool.mpr h5

def bool (l l2 : IndexList 𝓒.Color) : Bool :=
  if ¬  (l ++ l2).withUniqueDual = (l ++ l2).withDual then
    false
  else
    ColorCond.bool (l ++ l2)

lemma bool_iff (l l2 : IndexList 𝓒.Color) :
    bool l l2 ↔ (l ++ l2).withUniqueDual = (l ++ l2).withDual  ∧ ColorCond.bool (l ++ l2) := by
  simp [bool]

lemma iff_bool (l l2 : ColorIndexList 𝓒) : AppendCond l l2 ↔ bool l.toIndexList l2.toIndexList := by
  rw [AppendCond]
  simp [bool]
  rw [ColorCond.iff_bool]
  simp

end AppendCond


end ColorIndexList

end IndexNotation
