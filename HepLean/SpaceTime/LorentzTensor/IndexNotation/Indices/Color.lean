/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.UniqueDual
import HepLean.SpaceTime.LorentzTensor.IndexNotation.Indices.Append
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.Data.List.Lemmas
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
    rw [inl_mem_withDual_append_iff]
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
    · simp_all
      have hk'' := h (appendEquiv (Sum.inr k))
      simp at hk''
      simp_all
    · simp_all
      have hn' : (l2.getDualInOther? l k).isSome := by
        simp_all
      have hk'' := h (appendEquiv (Sum.inr k))
      simp at hk''
      simp_all
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
open IndexList

def empty : ColorIndexList 𝓒 where
  val := ∅
  unique_duals := by
    rfl
  dual_color := by
    rfl

@[simp]
def colorMap' : 𝓒.ColorMap (Fin l.length) :=
  l.colorMap

@[ext]
lemma ext {l l' : ColorIndexList 𝓒} (h : l.val = l'.val) : l = l' := by
  cases l
  cases l'
  simp_all
  apply IndexList.ext
  exact h

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

/-!

## Contract equiv

-/

def contrEquiv : (l.withUniqueDualLT ⊕ l.withUniqueDualLT) ⊕ Fin l.contr.length ≃ Fin l.length :=
  (Equiv.sumCongr (l.withUniqueLTGTEquiv) (Equiv.refl _)).trans <|
  (Equiv.sumCongr (Equiv.subtypeEquivRight (by
  simp [l.unique_duals])) (Fin.castOrderIso l.contrIndexList_length).toEquiv).trans <|
  l.dualEquiv

/-!

## Append

-/


def AppendCond : Prop :=
  (l.toIndexList ++ l2.toIndexList).withUniqueDual = (l.toIndexList ++ l2.toIndexList).withDual
  ∧ ColorCond (l.toIndexList ++ l2.toIndexList)

namespace AppendCond

variable {l l2 l3 : ColorIndexList 𝓒}

lemma symm (h : AppendCond l l2) : AppendCond l2 l := by
  apply And.intro _ (h.2.symm h.1)
  rw [append_withDual_eq_withUniqueDual_symm]
  exact h.1

end AppendCond

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


end AppendCond

end ColorIndexList

end IndexNotation
