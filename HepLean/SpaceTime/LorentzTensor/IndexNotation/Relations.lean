/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Color
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

/-- Two `ColorIndexList` are said to be reindexes of one another if they:
  (1) have the same length and (2) every corresponding index has the same color,
    and duals which correspond.

  Note: This does not allow for reordrings of indices. -/
def Reindexing : Prop := l.length = l'.length ∧
  ∀ (h : l.length = l'.length), l.colorMap = l'.colorMap ∘ Fin.cast h ∧
    Option.map (Fin.cast h) ∘ l.getDual? = l'.getDual? ∘ Fin.cast h

/-!

## Permutation

Test whether two `ColorIndexList`s are permutations of each other.
To prevent choice problems, this has to be done after contraction.

-/

/-- Two `ColorIndexList` are said to be related by contracted permutations, `ContrPerm`,
  if and only if: 1) Their contractions are the same length.
    2) Every index in the contracted list of one has a unqiue dual in the contracted
      list of the other and that dual has a the same color. -/
def ContrPerm : Prop :=
  l.contr.length = l'.contr.length ∧
  l.contr.withUniqueDualInOther l'.contr = Finset.univ ∧
  l'.contr.colorMap' ∘ Subtype.val ∘ (l.contr.getDualInOtherEquiv l'.contr)
  = l.contr.colorMap' ∘ Subtype.val

namespace ContrPerm

variable {l l' l2 l3 : ColorIndexList 𝓒}

@[symm]
lemma symm (h : ContrPerm l l') : ContrPerm l' l := by
  rw [ContrPerm] at h ⊢
  apply And.intro h.1.symm
  apply And.intro (l.contr.withUniqueDualInOther_eq_univ_symm l'.contr h.1 h.2.1)
  rw [← Function.comp.assoc, ← h.2.2, Function.comp.assoc, Function.comp.assoc]
  rw [show (l.contr.getDualInOtherEquiv l'.contr) =
    (l'.contr.getDualInOtherEquiv l.contr).symm from rfl]
  simp

@[simp]
lemma refl : ContrPerm l l := by
  apply And.intro rfl
  apply And.intro l.withUniqueDualInOther_eq_univ_contr_refl
  simp only [getDualInOtherEquiv_self_refl, Equiv.coe_refl, CompTriple.comp_eq]

@[trans]
lemma trans (h1 : ContrPerm l l2) (h2 : ContrPerm l2 l3) : ContrPerm l l3 := by
  apply And.intro (h1.1.trans h2.1)
  apply And.intro (l.contr.withUniqueDualInOther_eq_univ_trans l2.contr l3.contr h1.2.1 h2.2.1)
  funext i
  simp only [Function.comp_apply]
  have h1' := congrFun h1.2.2 ⟨i, by simp [h1.2.1]⟩
  simp at h1'
  rw [← h1']
  have h2' := congrFun h2.2.2 ⟨
    ↑((l.contr.getDualInOtherEquiv l2.contr.toIndexList) ⟨↑i, by simp [h1.2.1]⟩), by simp [h2.2.1]⟩
  simp at h2'
  rw [← h2']
  apply congrArg
  simp only [getDualInOtherEquiv, Equiv.coe_fn_mk]
  rw [← eq_getDualInOther?_get_of_withUniqueDualInOther_iff]
  simp [AreDualInOther]
  rw [h2.2.1]
  simp

lemma symm_trans (h1 : ContrPerm l l2) (h2 : ContrPerm l2 l3) :
    (h1.trans h2).symm = h2.symm.trans h1.symm := by
  simp only

@[simp]
lemma contr_self : ContrPerm l l.contr := by
  rw [ContrPerm]
  simp only [contr_contr, true_and]
  have h1 := @refl _ _ l
  apply And.intro h1.2.1
  erw [contr_contr]
  exact h1.2.2

@[simp]
lemma self_contr : ContrPerm l.contr l := by
  symm
  simp

end ContrPerm

/-- Given two `ColorIndexList` related by contracted permutations, the equivalence between
  the indices of the corresponding contracted index lists. This equivalence is the
  permutation between the contracted indices. -/
def contrPermEquiv {l l' : ColorIndexList 𝓒} (h : ContrPerm l l') :
    Fin l.contr.length ≃ Fin l'.contr.length :=
  (Equiv.subtypeUnivEquiv (by simp [h.2])).symm.trans <|
  (l.contr.getDualInOtherEquiv l'.contr.toIndexList).trans <|
  Equiv.subtypeUnivEquiv (by simp [h.symm.2])

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
lemma contrPermEquiv_refl : contrPermEquiv (@ContrPerm.refl 𝓒 _ l) = Equiv.refl _ := by
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
  rw [← eq_getDualInOther?_get_of_withUniqueDualInOther_iff]
  simp [AreDualInOther]
  rw [(h1.trans h2).2.1]
  simp

@[simp]
lemma contrPermEquiv_self_contr {l : ColorIndexList 𝓒} :
    contrPermEquiv (by simp : ContrPerm l l.contr) =
    (Fin.castOrderIso (by simp)).toEquiv := by
  simp [contrPermEquiv]
  ext1 x
  simp only [getDualInOtherEquiv, Equiv.trans_apply, Equiv.subtypeUnivEquiv_symm_apply,
    Equiv.coe_fn_mk, Equiv.subtypeUnivEquiv_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
    Fin.coe_cast]
  symm
  rw [← eq_getDualInOther?_get_of_withUniqueDualInOther_iff]
  simp only [AreDualInOther, contr_contr_idMap, Fin.cast_trans, Fin.cast_eq_self]
  have h1 : ContrPerm l l.contr := by simp
  rw [h1.2.1]
  simp

@[simp]
lemma contrPermEquiv_contr_self {l : ColorIndexList 𝓒} :
    contrPermEquiv (by simp : ContrPerm l.contr l) =
    (Fin.castOrderIso (by simp)).toEquiv := by
  rw [← contrPermEquiv_symm, contrPermEquiv_self_contr]
  simp

end ColorIndexList

end IndexNotation
