/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.IndexNotation.IndexList.Color
import HepLean.Tensors.IndexNotation.ColorIndexList.ContrPerm
import HepLean.Tensors.IndexNotation.ColorIndexList.Append
import HepLean.Tensors.Basic
import HepLean.Tensors.RisingLowering
import HepLean.Tensors.Contraction
/-!

# The structure of a tensor with a string of indices

-/

/-! TODO: Introduce a way to change an index from e.g. `ᵘ¹` to `ᵘ²`.
  Would be nice to have a tactic that did this automatically. -/

namespace TensorStructure
noncomputable section

open TensorColor
open IndexNotation

variable {R : Type} [CommSemiring R] (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color}
  {cW : W → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν η : 𝓣.Color}

variable [IndexNotation 𝓣.Color]

/-- The structure an tensor with a index specification e.g. `ᵘ¹ᵤ₂`. -/
structure TensorIndex extends ColorIndexList 𝓣.toTensorColor where
  /-- The underlying tensor. -/
  tensor : 𝓣.Tensor toColorIndexList.colorMap'

namespace TensorIndex

open TensorColor ColorIndexList

variable {𝓣 : TensorStructure R} [IndexNotation 𝓣.Color] [DecidableEq 𝓣.Color]
variable {n m : ℕ} {cn : Fin n → 𝓣.Color} {cm : Fin m → 𝓣.Color}

instance : Coe 𝓣.TensorIndex (ColorIndexList 𝓣.toTensorColor) where
  coe T := T.toColorIndexList

omit [DecidableEq 𝓣.Color] in
lemma colormap_mapIso {T₁ T₂ : 𝓣.TensorIndex} (hi : T₁.toColorIndexList = T₂.toColorIndexList) :
    ColorMap.MapIso (Fin.castOrderIso (congrArg IndexList.length (congrArg toIndexList hi))).toEquiv
    T₁.colorMap' T₂.colorMap' := by
  cases T₁; cases T₂
  simp [ColorMap.MapIso]
  simp at hi
  rename_i a b c d
  cases a
  cases c
  rename_i a1 a2 a3 a4 a5 a6
  cases a1
  cases a4
  simp_all
  simp at hi
  subst hi
  rfl

omit [DecidableEq 𝓣.Color] in
lemma ext {T₁ T₂ : 𝓣.TensorIndex} (hi : T₁.toColorIndexList = T₂.toColorIndexList)
    (h : T₁.tensor = 𝓣.mapIso (Fin.castOrderIso (by simp [IndexList.length, hi])).toEquiv
    (colormap_mapIso hi.symm) T₂.tensor) : T₁ = T₂ := by
  cases T₁; cases T₂
  simp at h
  simp_all
  simp at hi
  subst hi
  simp_all

omit [DecidableEq 𝓣.Color] in
lemma index_eq_of_eq {T₁ T₂ : 𝓣.TensorIndex} (h : T₁ = T₂) :
    T₁.toColorIndexList = T₂.toColorIndexList := by
  cases h
  rfl

/-- Given an equality of `TensorIndex`, the isomorphism taking one underlying
  tensor to the other. -/
@[simp]
def tensorIso {T₁ T₂ : 𝓣.TensorIndex} (h : T₁ = T₂) :
    𝓣.Tensor T₂.colorMap' ≃ₗ[R] 𝓣.Tensor T₁.colorMap' :=
  𝓣.mapIso (Fin.castOrderIso (by rw [index_eq_of_eq h])).toEquiv
    (colormap_mapIso (index_eq_of_eq h).symm)

omit [DecidableEq 𝓣.Color] in
@[simp]
lemma tensor_eq_of_eq {T₁ T₂ : 𝓣.TensorIndex} (h : T₁ = T₂) :
    T₁.tensor = tensorIso h T₂.tensor := by
  have hi := index_eq_of_eq h
  cases T₁
  cases T₂
  simp at hi
  subst hi
  simpa using h

/-- The construction of a `TensorIndex` from a tensor, a IndexListColor, and a condition
  on the dual maps. -/
def mkDualMap (T : 𝓣.Tensor cn) (l : ColorIndexList 𝓣.toTensorColor) (hn : n = l.1.length)
    (hd : ColorMap.DualMap l.colorMap' (cn ∘ Fin.cast hn.symm)) :
    𝓣.TensorIndex where
  toColorIndexList := l
  tensor :=
      𝓣.mapIso (Equiv.refl _) (ColorMap.DualMap.split_dual' (by simpa using hd)) <|
      𝓣.dualize (ColorMap.DualMap.split l.colorMap' (cn ∘ Fin.cast hn.symm)) <|
      (𝓣.mapIso (Fin.castOrderIso hn).toEquiv rfl T : 𝓣.Tensor (cn ∘ Fin.cast hn.symm))

/-!

## The contraction of indices

-/

/-- The contraction of indices in a `TensorIndex`. -/
def contr (T : 𝓣.TensorIndex) : 𝓣.TensorIndex where
  toColorIndexList := T.toColorIndexList.contr
  tensor := 𝓣.mapIso (Equiv.refl _) T.contrEquiv_colorMapIso <|
      𝓣.contr T.toColorIndexList.contrEquiv T.contrEquiv_contrCond T.tensor

omit [DecidableEq 𝓣.Color] in
@[simp]
lemma contr_tensor (T : 𝓣.TensorIndex) :
    T.contr.tensor = ((𝓣.mapIso (Equiv.refl _) T.contrEquiv_colorMapIso <|
      𝓣.contr T.toColorIndexList.contrEquiv T.contrEquiv_contrCond T.tensor)) := by
  rfl

omit [DecidableEq 𝓣.Color] in
/-- Applying contr to a tensor whose indices has no contracts does not do anything. -/
@[simp]
lemma contr_of_withDual_empty (T : 𝓣.TensorIndex) (h : T.withDual = ∅) :
    T.contr = T := by
  refine ext ?_ ?_
  · simp only [contr, ColorIndexList.contr]
    have hx := T.contrIndexList_of_withDual_empty h
    apply ColorIndexList.ext
    simp only [hx]
  · simp only [contr]
    cases T
    rename_i i T
    simp only
    refine PiTensorProduct.induction_on' T ?_ (by
      intro a b hx hy
      simp [map_add, add_mul, hx, hy])
    intro r f
    simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, LinearMapClass.map_smul, mapIso_tprod,
      id_eq, eq_mpr_eq_cast, OrderIso.toEquiv_symm, RelIso.coe_fn_toEquiv]
    apply congrArg
    have hEm : IsEmpty { x // x ∈ i.withUniqueDualLT } := by
      rw [Finset.isEmpty_coe_sort]
      rw [Finset.eq_empty_iff_forall_not_mem]
      intro x hx
      have hx' : x ∈ i.withUniqueDual := by
        exact Finset.mem_of_mem_filter x hx
      rw [← i.unique_duals] at h
      rw [h] at hx'
      simp_all only [Finset.not_mem_empty]
    erw [TensorStructure.contr_tprod_isEmpty]
    erw [mapIso_tprod]
    simp only [Equiv.refl_symm, Equiv.refl_apply, colorMap', mapIso_tprod, id_eq,
      OrderIso.toEquiv_symm, RelIso.coe_fn_toEquiv]
    apply congrArg
    funext l
    rw [← LinearEquiv.symm_apply_eq]
    simp only [colorModuleCast, Equiv.cast_symm, OrderIso.toEquiv_symm, RelIso.coe_fn_toEquiv,
      Function.comp_apply, LinearEquiv.coe_mk, Equiv.cast_apply, LinearEquiv.coe_symm_mk, cast_cast]
    apply cast_eq_iff_heq.mpr
    let hl := i.contrEquiv_on_withDual_empty l h
    exact let_value_heq f hl

omit [DecidableEq 𝓣.Color] in
lemma contr_tensor_of_withDual_empty (T : 𝓣.TensorIndex) (h : T.withDual = ∅) :
    T.contr.tensor = tensorIso (contr_of_withDual_empty T h) T.tensor := by
  exact tensor_eq_of_eq (contr_of_withDual_empty T h)

omit [DecidableEq 𝓣.Color] in
@[simp]
lemma contr_contr (T : 𝓣.TensorIndex) : T.contr.contr = T.contr :=
  T.contr.contr_of_withDual_empty (by simp [contr, ColorIndexList.contr])

omit [DecidableEq 𝓣.Color] in
@[simp]
lemma contr_toColorIndexList (T : 𝓣.TensorIndex) :
    T.contr.toColorIndexList = T.toColorIndexList.contr := rfl

omit [DecidableEq 𝓣.Color] in
lemma contr_toIndexList (T : 𝓣.TensorIndex) :
    T.contr.toIndexList = T.toIndexList.contrIndexList := rfl

/-!

## Equivalence relation on `TensorIndex`

-/

/-- An (equivalence) relation on two `TensorIndex`.
  The point in this equivalence relation is that certain things (like the
  permutation of indices, the contraction of indices, or rising or lowering indices) can be placed
  in the indices or moved to the tensor itself. These two descriptions are equivalent. -/
def Rel (T₁ T₂ : 𝓣.TensorIndex) : Prop :=
  T₁.ContrPerm T₂ ∧ ∀ (h : T₁.ContrPerm T₂),
  T₁.contr.tensor = 𝓣.mapIso (contrPermEquiv h).symm (contrPermEquiv_colorMap_iso h) T₂.contr.tensor

namespace Rel

/-- Rel is reflexive. -/
lemma refl (T : 𝓣.TensorIndex) : Rel T T := by
  apply And.intro
  · simp only [ContrPerm.refl]
  · simp only [ContrPerm.refl, contr_toColorIndexList, contr_tensor, contrPermEquiv_refl,
    Equiv.refl_symm, mapIso_refl, LinearEquiv.refl_apply, imp_self]

/-- Rel is symmetric. -/
lemma symm {T₁ T₂ : 𝓣.TensorIndex} (h : Rel T₁ T₂) : Rel T₂ T₁ := by
  apply And.intro h.1.symm
  intro h'
  rw [← mapIso_symm]
  · symm
    erw [LinearEquiv.symm_apply_eq]
    rw [h.2]
    · rfl
    exact h'.symm

/-- Rel is transitive. -/
lemma trans {T₁ T₂ T₃ : 𝓣.TensorIndex} (h1 : Rel T₁ T₂) (h2 : Rel T₂ T₃) : Rel T₁ T₃ := by
  apply And.intro ((h1.1.trans h2.1))
  intro h
  change _ = (𝓣.mapIso (contrPermEquiv (h1.1.trans h2.1)).symm _) T₃.contr.tensor
  trans (𝓣.mapIso ((contrPermEquiv h1.1).trans (contrPermEquiv h2.1)).symm (by
    simp only [contrPermEquiv_trans, contrPermEquiv_symm, contr_toColorIndexList]
    have h1 := contrPermEquiv_colorMap_iso (ContrPerm.symm (ContrPerm.trans h1.left h2.left))
    rw [← ColorMap.MapIso.symm'] at h1
    exact h1)) T₃.contr.tensor
  · erw [← mapIso_trans]
    · simp only [LinearEquiv.trans_apply]
      apply (h1.2 h1.1).trans
      · apply congrArg
        exact h2.2 h2.1
  · congr 1
    simp only [contrPermEquiv_trans, contrPermEquiv_symm]

/-- Rel forms an equivalence relation. -/
lemma isEquivalence : Equivalence (@Rel _ _ 𝓣 _ _) where
  refl := Rel.refl
  symm := Rel.symm
  trans := Rel.trans

/-- The equality of tensors corresponding to related tensor indices. -/
lemma to_eq {T₁ T₂ : 𝓣.TensorIndex} (h : Rel T₁ T₂) :
    T₁.contr.tensor = 𝓣.mapIso (contrPermEquiv h.1).symm
    (contrPermEquiv_colorMap_iso h.1) T₂.contr.tensor := h.2 h.1

lemma of_withDual_empty {T₁ T₂ : 𝓣.TensorIndex} (h : T₁.ContrPerm T₂)
    (h1 : T₁.withDual = ∅) (h2 : T₂.withDual = ∅)
    (hT : T₁.tensor =
    𝓣.mapIso (permEquiv h h1 h2).symm (permEquiv_colorMap_iso h h1 h2) T₂.tensor) : Rel T₁ T₂ := by
  apply And.intro h
  intro h'
  rw [contr_tensor_of_withDual_empty T₁ h1, contr_tensor_of_withDual_empty T₂ h2, hT]
  simp only [contr_toColorIndexList, tensorIso, mapIso_mapIso, contrPermEquiv_symm]
  apply congrFun
  apply congrArg
  apply mapIso_ext
  ext i
  simp [permEquiv, contrPermEquiv]
  have hn := congrArg (fun x => x.toIndexList) (contr_of_withDual_empty T₁ h1)
  have hn2 := congrArg (fun x => x.toIndexList) (contr_of_withDual_empty T₂ h2)
  simp only [contr_toColorIndexList] at hn hn2
  rw [IndexList.getDualInOtherEquiv_cast hn2 hn]
  rfl

end Rel

/-- The structure of a Setoid on `𝓣.TensorIndex` induced by `Rel`. -/
instance asSetoid : Setoid 𝓣.TensorIndex := ⟨Rel, Rel.isEquivalence⟩

/-- A tensor index is equivalent to its contraction. -/
lemma rel_contr (T : 𝓣.TensorIndex) : T ≈ T.contr := by
  apply And.intro
  · simp only [contr_toColorIndexList, ContrPerm.contr_self]
  · intro h
    rw [tensor_eq_of_eq T.contr_contr]
    simp only [contr_toColorIndexList, colorMap', contrPermEquiv_self_contr, OrderIso.toEquiv_symm,
      Fin.symm_castOrderIso, mapIso_mapIso, tensorIso]
    trans 𝓣.mapIso (Equiv.refl _) (by rfl) T.contr.tensor
    · simp only [contr_toColorIndexList, mapIso_refl, LinearEquiv.refl_apply]
    · rfl

/-!

## Scalar multiplication of

-/

/-- The scalar multiplication of a `TensorIndex` by an element of `R`. -/
instance : SMul R 𝓣.TensorIndex where
  smul := fun r T => {
    toColorIndexList := T.toColorIndexList
    tensor := r • T.tensor}

omit [DecidableEq 𝓣.Color] in
@[simp]
lemma smul_index (r : R) (T : 𝓣.TensorIndex) : (r • T).toColorIndexList = T.toColorIndexList := rfl

omit [DecidableEq 𝓣.Color] in
@[simp]
lemma smul_tensor (r : R) (T : 𝓣.TensorIndex) : (r • T).tensor = r • T.tensor := rfl

omit [DecidableEq 𝓣.Color] in
@[simp]
lemma smul_contr (r : R) (T : 𝓣.TensorIndex) : (r • T).contr = r • T.contr := by
  refine ext rfl ?_
  simp only [contr, smul_index, smul_tensor, LinearMapClass.map_smul, Fin.castOrderIso_refl,
    OrderIso.refl_toEquiv, mapIso_refl, LinearEquiv.refl_apply]

lemma smul_rel {T₁ T₂ : 𝓣.TensorIndex} (h : T₁ ≈ T₂) (r : R) : r • T₁ ≈ r • T₂ := by
  apply And.intro h.1
  intro h1
  rw [tensor_eq_of_eq (smul_contr r T₁), tensor_eq_of_eq (smul_contr r T₂)]
  simp only [contr_toColorIndexList, smul_index, Fin.castOrderIso_refl, OrderIso.refl_toEquiv,
    mapIso_refl, smul_tensor, map_smul, LinearEquiv.refl_apply, contrPermEquiv_symm, tensorIso]
  apply congrArg
  exact h.2 h1

/-!

## Addition of allowed `TensorIndex`

-/

/-- The condition on tensors with indices for their addition to exists.
  This condition states that the the indices of one tensor are exact permutations of indices
  of another after contraction. This includes the id of the index and the color.

  This condition is general enough to allow addition of e.g. `ψᵤ₁ᵤ₂ + φᵤ₂ᵤ₁`, but
  will NOT allow e.g. `ψᵤ₁ᵤ₂ + φᵘ²ᵤ₁`. -/
def AddCond (T₁ T₂ : 𝓣.TensorIndex) : Prop := T₁.ContrPerm T₂

namespace AddCond

lemma to_PermContr {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) :
    T₁.toColorIndexList.ContrPerm T₂.toColorIndexList := h

@[symm]
lemma symm {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) : AddCond T₂ T₁ := by
  rw [AddCond] at h
  exact h.symm

lemma refl (T : 𝓣.TensorIndex) : AddCond T T := ContrPerm.refl T.toColorIndexList

lemma trans {T₁ T₂ T₃ : 𝓣.TensorIndex} (h1 : AddCond T₁ T₂) (h2 : AddCond T₂ T₃) :
    AddCond T₁ T₃ := by
  rw [AddCond] at h1 h2
  exact h1.trans h2

lemma rel_left {T₁ T₁' T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) (h' : T₁ ≈ T₁') :
    AddCond T₁' T₂ := h'.1.symm.trans h

lemma rel_right {T₁ T₂ T₂' : 𝓣.TensorIndex} (h : AddCond T₁ T₂) (h' : T₂ ≈ T₂') :
    AddCond T₁ T₂' := h.trans h'.1

end AddCond

/-- The equivalence between indices after contraction given a `AddCond`. -/
@[simp]
def addCondEquiv {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) :
    Fin T₁.contr.length ≃ Fin T₂.contr.length := contrPermEquiv h

lemma addCondEquiv_colorMap {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) :
    ColorMap.MapIso (addCondEquiv h) T₁.contr.colorMap' T₂.contr.colorMap' :=
    contrPermEquiv_colorMap_iso' h

/-- The addition of two `TensorIndex` given the condition that, after contraction,
  their index lists are the same. -/
def add (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    𝓣.TensorIndex where
  toColorIndexList := T₂.toColorIndexList.contr
  tensor := (𝓣.mapIso (addCondEquiv h) (addCondEquiv_colorMap h) T₁.contr.tensor) + T₂.contr.tensor

/-- Notation for addition of tensor indices. -/
notation:71 T₁ "+["h"]" T₂:72 => add T₁ T₂ h

namespace AddCond

lemma add_right {T₁ T₂ T₃ : 𝓣.TensorIndex} (h : AddCond T₁ T₃) (h' : AddCond T₂ T₃) :
    AddCond T₁ (T₂ +[h'] T₃) := by
  simpa only [AddCond, add] using h.rel_right T₃.rel_contr

lemma add_left {T₁ T₂ T₃ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) (h' : AddCond T₂ T₃) :
    AddCond (T₁ +[h] T₂) T₃ :=
  (add_right h'.symm h).symm

lemma of_add_right' {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₂ T₃} (h : AddCond T₁ (T₂ +[h'] T₃)) :
    AddCond T₁ T₃ := by
  change T₁.AddCond T₃.contr at h
  exact h.rel_right T₃.rel_contr.symm

lemma of_add_right {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₂ T₃} (h : AddCond T₁ (T₂ +[h'] T₃)) :
    AddCond T₁ T₂ := h.of_add_right'.trans h'.symm

lemma of_add_left {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₁ T₂}
    (h : AddCond (T₁ +[h'] T₂) T₃) : AddCond T₂ T₃ :=
  (of_add_right' h.symm).symm

lemma of_add_left' {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₁ T₂}
    (h : AddCond (T₁ +[h'] T₂) T₃) : AddCond T₁ T₃ :=
  (of_add_right h.symm).symm

lemma add_left_of_add_right {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₂ T₃}
    (h : AddCond T₁ (T₂ +[h'] T₃)) : AddCond (T₁ +[of_add_right h] T₂) T₃ := by
  have h0 := ((of_add_right' h).trans h'.symm)
  exact (h'.symm.add_right h0).symm

lemma add_right_of_add_left {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₁ T₂}
    (h : AddCond (T₁ +[h'] T₂) T₃) : AddCond T₁ (T₂ +[of_add_left h] T₃) :=
  (add_left (of_add_left h) (of_add_left' h).symm).symm

lemma add_comm {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) :
    AddCond (T₁ +[h] T₂) (T₂ +[h.symm] T₁) := by
  apply add_right
  apply add_left
  exact h.symm

end AddCond

@[simp]
lemma add_toColorIndexList (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (add T₁ T₂ h).toColorIndexList = T₂.toColorIndexList.contr := rfl

@[simp]
lemma add_tensor (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (add T₁ T₂ h).tensor =
    (𝓣.mapIso (addCondEquiv h) (addCondEquiv_colorMap h) T₁.contr.tensor) + T₂.contr.tensor := rfl

/-- Scalar multiplication commutes with addition. -/
lemma smul_add (r : R) (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    r • (T₁ +[h] T₂) = r • T₁ +[h] r • T₂ := by
  refine ext rfl ?_
  simp only [add, contr_toColorIndexList, addCondEquiv, smul_index, smul_tensor, _root_.smul_add,
    Fin.castOrderIso_refl, OrderIso.refl_toEquiv, mapIso_refl, map_add, LinearEquiv.refl_apply,
    tensorIso]
  rw [tensor_eq_of_eq (smul_contr r T₁), tensor_eq_of_eq (smul_contr r T₂)]
  simp only [smul_index, contr_toColorIndexList, Fin.castOrderIso_refl, OrderIso.refl_toEquiv,
    mapIso_refl, smul_tensor, map_smul, LinearEquiv.refl_apply, tensorIso]

lemma add_withDual_empty (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (T₁ +[h] T₂).withDual = ∅ := by
  simp only [add_toColorIndexList]
  change T₂.toColorIndexList.contr.withDual = ∅
  simp only [ColorIndexList.contr, IndexList.contrIndexList_withDual]

@[simp]
lemma contr_add (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (T₁ +[h] T₂).contr = T₁ +[h] T₂ :=
  contr_of_withDual_empty (T₁ +[h] T₂) (add_withDual_empty T₁ T₂ h)

lemma contr_add_tensor (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (T₁ +[h] T₂).contr.tensor =
    𝓣.mapIso (Fin.castOrderIso (by rw [index_eq_of_eq (contr_add T₁ T₂ h)])).toEquiv
    (colormap_mapIso (by simp)) (T₁ +[h] T₂).tensor :=
  tensor_eq_of_eq (contr_add T₁ T₂ h)

lemma add_comm {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) : T₁ +[h] T₂ ≈ T₂ +[h.symm] T₁ := by
  apply And.intro h.add_comm
  intro h
  simp only [contr_toColorIndexList, add_toColorIndexList, contr_add_tensor, add_tensor,
    addCondEquiv, map_add, mapIso_mapIso, colorMap', contrPermEquiv_symm]
  rw [_root_.add_comm]
  apply Mathlib.Tactic.LinearCombination.add_pf
  · apply congrFun
    apply congrArg
    apply mapIso_ext
    rw [← contrPermEquiv_self_contr, ← contrPermEquiv_self_contr, contrPermEquiv_trans,
      contrPermEquiv_trans]
  · apply congrFun
    apply congrArg
    apply mapIso_ext
    rw [← contrPermEquiv_self_contr, ← contrPermEquiv_self_contr, contrPermEquiv_trans,
      contrPermEquiv_trans]

open AddCond in
lemma add_rel_left {T₁ T₁' T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) (h' : T₁ ≈ T₁') :
    T₁ +[h] T₂ ≈ T₁' +[h.rel_left h'] T₂ := by
  apply And.intro (ContrPerm.refl _)
  intro h
  simp only [contr_add_tensor, add_tensor, map_add]
  apply Mathlib.Tactic.LinearCombination.add_pf
  · rw [h'.to_eq]
    simp only [contr_toColorIndexList, add_toColorIndexList, colorMap', addCondEquiv,
      contrPermEquiv_symm, mapIso_mapIso, contrPermEquiv_trans, contrPermEquiv_refl,
      Equiv.refl_symm, mapIso_refl, LinearEquiv.refl_apply]
  · simp only [contr_toColorIndexList, add_toColorIndexList, colorMap', contrPermEquiv_refl,
      Equiv.refl_symm, mapIso_refl, LinearEquiv.refl_apply]

open AddCond in
lemma add_rel_right {T₁ T₂ T₂' : 𝓣.TensorIndex} (h : AddCond T₁ T₂) (h' : T₂ ≈ T₂') :
    T₁ +[h] T₂ ≈ T₁ +[h.rel_right h'] T₂' :=
  (add_comm _).trans ((add_rel_left _ h').trans (add_comm _))

open AddCond in
lemma add_assoc' {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₂ T₃} (h : AddCond T₁ (T₂ +[h'] T₃)) :
    T₁ +[h] (T₂ +[h'] T₃) = T₁ +[h'.of_add_right h] T₂ +[h'.add_left_of_add_right h] T₃ := by
  refine ext ?_ ?_
  · simp only [add_toColorIndexList, ColorIndexList.contr_contr]
  · simp only [add_toColorIndexList, add_tensor, contr_toColorIndexList, addCondEquiv,
      contr_add_tensor, map_add, mapIso_mapIso]
    rw [_root_.add_assoc]
    apply Mathlib.Tactic.LinearCombination.add_pf
    · apply congrFun
      apply congrArg
      apply mapIso_ext
      rw [← contrPermEquiv_self_contr, ← contrPermEquiv_self_contr]
      rw [contrPermEquiv_trans, contrPermEquiv_trans, contrPermEquiv_trans]
    · apply Mathlib.Tactic.LinearCombination.add_pf _ rfl
      apply congrFun
      apply congrArg
      apply mapIso_ext
      rw [← contrPermEquiv_self_contr, contrPermEquiv_trans, ← contrPermEquiv_self_contr,
        contrPermEquiv_trans, contrPermEquiv_trans]

open AddCond in
lemma add_assoc {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₁ T₂} (h : AddCond (T₁ +[h'] T₂) T₃) :
    T₁ +[h'] T₂ +[h] T₃ = T₁ +[h'.add_right_of_add_left h] (T₂ +[h'.of_add_left h] T₃) := by
  rw [add_assoc']

/-!

## Product of `TensorIndex` when allowed

-/

/-! TODO: Show that the product is well defined with respect to Rel. -/

/-- The condition on two `TensorIndex` which is true if and only if their `ColorIndexList`s
  are related by the condition `AppendCond`. That is, they can be appended to form a
  `ColorIndexList`. -/
def ProdCond (T₁ T₂ : 𝓣.TensorIndex) : Prop :=
  AppendCond T₁.toColorIndexList T₂.toColorIndexList

namespace ProdCond

variable {T₁ T₁' T₂ T₂' : 𝓣.TensorIndex}

omit [DecidableEq 𝓣.Color] in
lemma to_AppendCond (h : ProdCond T₁ T₂) :
    T₁.AppendCond T₂ := h

@[symm]
lemma symm (h : ProdCond T₁ T₂) : ProdCond T₂ T₁ := h.to_AppendCond.symm

/-! TODO: Prove properties regarding the interaction of `ProdCond` and `Rel`. -/

end ProdCond

/-- The tensor product of two `TensorIndex`.

  Note: By defualt contraction is NOT done before taking the products. -/
def prod (T₁ T₂ : 𝓣.TensorIndex) (h : ProdCond T₁ T₂) : 𝓣.TensorIndex where
  toColorIndexList := T₁ ++[h] T₂
  tensor := 𝓣.mapIso IndexList.appendEquiv (T₁.colorMap_sumELim T₂) <|
      𝓣.tensoratorEquiv _ _ (T₁.tensor ⊗ₜ[R] T₂.tensor)

omit [DecidableEq 𝓣.Color] in
@[simp]
lemma prod_toColorIndexList (T₁ T₂ : 𝓣.TensorIndex) (h : ProdCond T₁ T₂) :
    (prod T₁ T₂ h).toColorIndexList = T₁.toColorIndexList ++[h] T₂.toColorIndexList := rfl

omit [DecidableEq 𝓣.Color] in
@[simp]
lemma prod_toIndexList (T₁ T₂ : 𝓣.TensorIndex) (h : ProdCond T₁ T₂) :
    (prod T₁ T₂ h).toIndexList = T₁.toIndexList ++ T₂.toIndexList := rfl

end TensorIndex
end
end TensorStructure
