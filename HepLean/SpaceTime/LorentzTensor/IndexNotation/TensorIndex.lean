/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexListColor
import HepLean.SpaceTime.LorentzTensor.Basic
import HepLean.SpaceTime.LorentzTensor.RisingLowering
import HepLean.SpaceTime.LorentzTensor.Contraction
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

variable [IndexNotation 𝓣.Color] [Fintype 𝓣.Color] [DecidableEq 𝓣.Color]

/-- The structure an tensor with a index specification e.g. `ᵘ¹ᵤ₂`. -/
structure TensorIndex where
  /-- The list of indices. -/
  index : IndexListColor 𝓣.toTensorColor
  /-- The underlying tensor. -/
  tensor : 𝓣.Tensor index.1.colorMap

namespace TensorIndex
open TensorColor IndexListColor
variable {𝓣 : TensorStructure R} [IndexNotation 𝓣.Color] [Fintype 𝓣.Color] [DecidableEq 𝓣.Color]
variable {n m : ℕ} {cn : Fin n → 𝓣.Color} {cm : Fin m → 𝓣.Color}

lemma index_eq_colorMap_eq {T₁ T₂ : 𝓣.TensorIndex} (hi : T₁.index = T₂.index) :
    (T₂.index).1.colorMap = (T₁.index).1.colorMap ∘ (Fin.castOrderIso (by rw [hi])).toEquiv := by
  funext i
  congr 1
  rw [hi]
  simp only [RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply]
  exact
    (Fin.heq_ext_iff (congrArg IndexList.numIndices (congrArg Subtype.val (id (Eq.symm hi))))).mpr
      rfl

lemma ext (T₁ T₂ : 𝓣.TensorIndex) (hi : T₁.index = T₂.index)
    (h : T₁.tensor = 𝓣.mapIso (Fin.castOrderIso (by rw [hi])).toEquiv
    (index_eq_colorMap_eq hi) T₂.tensor) : T₁ = T₂ := by
  cases T₁; cases T₂
  simp at hi
  subst hi
  simp_all

lemma index_eq_of_eq {T₁ T₂ : 𝓣.TensorIndex} (h : T₁ = T₂) : T₁.index = T₂.index := by
  cases h
  rfl

@[simp]
lemma tensor_eq_of_eq {T₁ T₂ : 𝓣.TensorIndex} (h : T₁ = T₂) : T₁.tensor =
    𝓣.mapIso (Fin.castOrderIso (by rw [index_eq_of_eq h])).toEquiv
    (index_eq_colorMap_eq (index_eq_of_eq h)) T₂.tensor := by
  have hi := index_eq_of_eq h
  cases T₁
  cases T₂
  simp at hi
  subst hi
  simpa using h

/-- The construction of a `TensorIndex` from a tensor, a IndexListColor, and a condition
  on the dual maps. -/
def mkDualMap (T : 𝓣.Tensor cn) (l : IndexListColor 𝓣.toTensorColor) (hn : n = l.1.length)
    (hd : ColorMap.DualMap l.1.colorMap (cn ∘ Fin.cast hn.symm)) :
    𝓣.TensorIndex where
  index := l
  tensor :=
      𝓣.mapIso (Equiv.refl _) (ColorMap.DualMap.split_dual' (by simp [hd])) <|
      𝓣.dualize (ColorMap.DualMap.split l.1.colorMap (cn ∘ Fin.cast hn.symm)) <|
      (𝓣.mapIso (Fin.castOrderIso hn).toEquiv rfl T : 𝓣.Tensor (cn ∘ Fin.cast hn.symm))

/-!

## The contraction of indices

-/

/-- The contraction of indices in a `TensorIndex`. -/
def contr (T : 𝓣.TensorIndex) : 𝓣.TensorIndex where
  index := T.index.contr
  tensor :=
      𝓣.mapIso (Fin.castOrderIso T.index.contr_numIndices.symm).toEquiv
      T.index.contr_colorMap <|
      𝓣.contr (T.index.splitContr).symm T.index.splitContr_map T.tensor

/-- Applying contr to a tensor whose indices has no contracts does not do anything. -/
@[simp]
lemma contr_of_hasNoContr (T : 𝓣.TensorIndex) (h : T.index.1.HasNoContr) :
    T.contr = T := by
  refine ext _ _ ?_ ?_
  exact Subtype.eq (T.index.1.contr_of_hasNoContr h)
  simp only [contr]
  have h1 : IsEmpty T.index.1.contrPairSet := T.index.1.contrPairSet_isEmpty_of_hasNoContr h
  cases T
  rename_i i T
  simp only
  refine PiTensorProduct.induction_on' T ?_ (by
    intro a b hx hy
    simp [map_add, add_mul, hx, hy])
  intro r f
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, LinearMapClass.map_smul, mapIso_tprod, id_eq,
    eq_mpr_eq_cast, OrderIso.toEquiv_symm, RelIso.coe_fn_toEquiv]
  apply congrArg
  erw [TensorStructure.contr_tprod_isEmpty]
  erw [mapIso_tprod]
  apply congrArg
  funext l
  rw [← LinearEquiv.symm_apply_eq]
  simp only [colorModuleCast, Equiv.cast_symm, OrderIso.toEquiv_symm, RelIso.coe_fn_toEquiv,
    Function.comp_apply, LinearEquiv.coe_mk, Equiv.cast_apply, LinearEquiv.coe_symm_mk, cast_cast]
  apply cast_eq_iff_heq.mpr
  rw [splitContr_symm_apply_of_hasNoContr _ h]
  rfl

@[simp]
lemma contr_contr (T : 𝓣.TensorIndex) : T.contr.contr = T.contr :=
  T.contr.contr_of_hasNoContr T.index.1.contr_hasNoContr

@[simp]
lemma contr_index (T : 𝓣.TensorIndex) : T.contr.index = T.index.contr := rfl


/-!

## Scalar multiplication of

-/

/-- The scalar multiplication of a `TensorIndex` by an element of `R`. -/
instance : SMul R 𝓣.TensorIndex where
  smul := fun r T => {
    index := T.index
    tensor := r • T.tensor}

@[simp]
lemma smul_index (r : R) (T : 𝓣.TensorIndex) : (r • T).index = T.index := rfl

@[simp]
lemma smul_tensor (r : R) (T : 𝓣.TensorIndex) : (r • T).tensor = r • T.tensor := rfl

@[simp]
lemma smul_contr (r : R) (T : 𝓣.TensorIndex) : (r • T).contr = r • T.contr := by
  refine ext _ _ rfl ?_
  simp only [contr, smul_index, smul_tensor, LinearMapClass.map_smul, Fin.castOrderIso_refl,
    OrderIso.refl_toEquiv, mapIso_refl, LinearEquiv.refl_apply]

/-!

## Equivalence relation on `TensorIndex`

-/

/-- An (equivalence) relation on two `TensorIndex`.
  The point in this equivalence relation is that certain things (like the
  permutation of indices, the contraction of indices, or rising or lowering indices) can be placed
  in the indices or moved to the tensor itself. These two descriptions are equivalent. -/
def Rel (T₁ T₂ : 𝓣.TensorIndex) : Prop :=
  T₁.index.PermContr T₂.index ∧ ∀ (h : T₁.index.PermContr T₂.index),
  T₁.contr.tensor = 𝓣.mapIso h.toEquiv.symm h.toEquiv_colorMap T₂.contr.tensor

namespace Rel

/-- Rel is reflexive. -/
lemma refl (T : 𝓣.TensorIndex) : Rel T T := by
  apply And.intro
  exact IndexListColor.PermContr.refl T.index
  intro h
  simp [PermContr.toEquiv_refl']

/-- Rel is symmetric. -/
lemma symm {T₁ T₂ : 𝓣.TensorIndex} (h : Rel T₁ T₂) : Rel T₂ T₁ := by
  apply And.intro h.1.symm
  intro h'
  rw [← mapIso_symm]
  symm
  erw [LinearEquiv.symm_apply_eq]
  rw [h.2]
  apply congrFun
  congr
  exact h'.symm

/-- Rel is transitive. -/
lemma trans {T₁ T₂ T₃ : 𝓣.TensorIndex} (h1 : Rel T₁ T₂) (h2 : Rel T₂ T₃) : Rel T₁ T₃ := by
  apply And.intro (h1.1.trans h2.1)
  intro h
  change _ = (𝓣.mapIso (h1.1.trans h2.1).toEquiv.symm _) T₃.contr.tensor
  trans (𝓣.mapIso ((h1.1).toEquiv.trans (h2.1).toEquiv).symm (by
    rw [PermContr.toEquiv_trans]
    exact proof_2 T₁ T₃ h)) T₃.contr.tensor
  swap
  congr
  rw [PermContr.toEquiv_trans]
  erw [← mapIso_trans]
  simp only [LinearEquiv.trans_apply]
  apply (h1.2 h1.1).trans
  apply congrArg
  exact h2.2 h2.1

/-- Rel forms an equivalence relation. -/
lemma isEquivalence : Equivalence (@Rel _ _ 𝓣 _) where
  refl := Rel.refl
  symm := Rel.symm
  trans := Rel.trans

/-- The equality of tensors corresponding to related tensor indices. -/
lemma to_eq {T₁ T₂ : 𝓣.TensorIndex} (h : Rel T₁ T₂) :
    T₁.contr.tensor = 𝓣.mapIso h.1.toEquiv.symm h.1.toEquiv_colorMap T₂.contr.tensor := h.2 h.1

end Rel

/-- The structure of a Setoid on `𝓣.TensorIndex` induced by `Rel`. -/
instance asSetoid : Setoid 𝓣.TensorIndex := ⟨Rel, Rel.isEquivalence⟩

/-- A tensor index is equivalent to its contraction. -/
lemma rel_contr (T : 𝓣.TensorIndex) : T ≈ T.contr := by
  apply And.intro
  simp only [PermContr, contr_index, IndexListColor.contr_contr, List.Perm.refl, true_and]
  rw [IndexListColor.contr_contr]
  exact T.index.contr.1.hasNoContr_color_eq_of_id_eq T.index.1.contr_hasNoContr
  intro h
  rw [tensor_eq_of_eq T.contr_contr]
  simp only [contr_index, mapIso_mapIso]
  trans 𝓣.mapIso (Equiv.refl _) (by rfl) T.contr.tensor
  simp only [contr_index, mapIso_refl, LinearEquiv.refl_apply]
  congr
  apply Equiv.ext
  intro x
  rw [PermContr.toEquiv_contr_eq T.index.contr_contr.symm]
  rfl

lemma smul_equiv {T₁ T₂ : 𝓣.TensorIndex} (h : T₁ ≈ T₂) (r : R) : r • T₁ ≈ r • T₂ := by
  apply And.intro h.1
  intro h1
  rw [tensor_eq_of_eq (smul_contr r T₁), tensor_eq_of_eq (smul_contr r T₂)]
  simp only [contr_index, smul_index, Fin.castOrderIso_refl, OrderIso.refl_toEquiv, mapIso_refl,
    smul_tensor, LinearMapClass.map_smul, LinearEquiv.refl_apply]
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
def AddCond (T₁ T₂ : 𝓣.TensorIndex) : Prop :=
  T₁.index.PermContr T₂.index

namespace AddCond

lemma to_PermContr {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) : T₁.index.PermContr T₂.index := h

@[symm]
lemma symm {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) : AddCond T₂ T₁ := by
  rw [AddCond] at h
  exact h.symm

lemma refl (T : 𝓣.TensorIndex) : AddCond T T := by
  exact PermContr.refl _

lemma trans {T₁ T₂ T₃ : 𝓣.TensorIndex} (h1 : AddCond T₁ T₂) (h2 : AddCond T₂ T₃) :
    AddCond T₁ T₃ := by
  rw [AddCond] at h1 h2
  exact h1.trans h2

lemma rel_left {T₁ T₁' T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) (h' : T₁ ≈ T₁') :
    AddCond T₁' T₂ := h'.1.symm.trans h

lemma rel_right {T₁ T₂ T₂' : 𝓣.TensorIndex} (h : AddCond T₁ T₂) (h' : T₂ ≈ T₂') :
    AddCond T₁ T₂' := h.trans h'.1

/-- The equivalence between indices after contraction given a `AddCond`. -/
@[simp]
def toEquiv {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) :
    Fin T₁.contr.index.1.length ≃ Fin T₂.contr.index.1.length := h.to_PermContr.toEquiv

lemma toEquiv_colorMap {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) :
    ColorMap.MapIso h.toEquiv (T₁.contr.index).1.colorMap (T₂.contr.index).1.colorMap :=
    h.to_PermContr.toEquiv_colorMap'

end AddCond

/-- The addition of two `TensorIndex` given the condition that, after contraction,
  their index lists are the same. -/
def add (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    𝓣.TensorIndex where
  index := T₂.index.contr
  tensor := (𝓣.mapIso h.toEquiv h.toEquiv_colorMap T₁.contr.tensor) + T₂.contr.tensor

/-- Notation for addition of tensor indices. -/
notation:71 T₁ "+["h"]" T₂:72 => add T₁ T₂ h

namespace AddCond

lemma add_right {T₁ T₂ T₃ : 𝓣.TensorIndex} (h : AddCond T₁ T₃) (h' : AddCond T₂ T₃) :
    AddCond T₁ (T₂ +[h'] T₃) := by
  simpa only [AddCond, add, contr_index] using h.rel_right T₃.rel_contr

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
lemma add_index (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (add T₁ T₂ h).index = T₂.index.contr := rfl

@[simp]
lemma add_tensor (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (add T₁ T₂ h).tensor =
    (𝓣.mapIso h.toEquiv h.toEquiv_colorMap T₁.contr.tensor) + T₂.contr.tensor := by rfl

/-- Scalar multiplication commutes with addition. -/
lemma smul_add (r : R) (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    r • (T₁ +[h] T₂) = r • T₁ +[h] r • T₂ := by
  refine ext _ _ rfl ?_
  simp [add]
  rw [tensor_eq_of_eq (smul_contr r T₁), tensor_eq_of_eq (smul_contr r T₂)]
  simp only [smul_index, contr_index, Fin.castOrderIso_refl, OrderIso.refl_toEquiv, mapIso_refl,
    smul_tensor, AddCond.toEquiv, LinearMapClass.map_smul, LinearEquiv.refl_apply]

lemma add_hasNoContr (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (T₁ +[h] T₂).index.1.HasNoContr := by
  simpa using T₂.index.1.contr_hasNoContr

@[simp]
lemma contr_add (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (T₁ +[h] T₂).contr = T₁ +[h] T₂ :=
  contr_of_hasNoContr (T₁ +[h] T₂) (add_hasNoContr T₁ T₂ h)

@[simp]
lemma contr_add_tensor (T₁ T₂ : 𝓣.TensorIndex) (h : AddCond T₁ T₂) :
    (T₁ +[h] T₂).contr.tensor =
    𝓣.mapIso (Fin.castOrderIso (by rw [index_eq_of_eq (contr_add T₁ T₂ h)])).toEquiv
    (index_eq_colorMap_eq (index_eq_of_eq (contr_add T₁ T₂ h))) (T₁ +[h] T₂).tensor :=
  tensor_eq_of_eq (contr_add T₁ T₂ h)

lemma add_comm {T₁ T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) : T₁ +[h] T₂ ≈ T₂ +[h.symm] T₁ := by
  apply And.intro h.add_comm
  intro h
  simp only [contr_index, add_index, contr_add_tensor, add_tensor, AddCond.toEquiv, map_add,
    mapIso_mapIso]
  rw [_root_.add_comm]
  congr 1
  all_goals
    apply congrFun
    apply congrArg
    congr 1
    rw [← PermContr.toEquiv_contr_eq, ← PermContr.toEquiv_contr_eq,
      PermContr.toEquiv_trans, PermContr.toEquiv_symm, PermContr.toEquiv_trans]
    simp only [IndexListColor.contr_contr]
    simp only [IndexListColor.contr_contr]

open AddCond in
lemma add_rel_left {T₁ T₁' T₂ : 𝓣.TensorIndex} (h : AddCond T₁ T₂) (h' : T₁ ≈ T₁') :
    T₁ +[h] T₂ ≈ T₁' +[h.rel_left h'] T₂ := by
  apply And.intro (PermContr.refl _)
  intro h
  simp only [contr_index, add_index, contr_add_tensor, add_tensor, toEquiv, map_add, mapIso_mapIso,
    PermContr.toEquiv_refl, Equiv.refl_symm, mapIso_refl, LinearEquiv.refl_apply]
  congr 1
  rw [h'.to_eq]
  simp only [mapIso_mapIso]
  congr 1
  congr 1
  rw [PermContr.toEquiv_symm, ← PermContr.toEquiv_contr_eq, PermContr.toEquiv_trans,
    PermContr.toEquiv_trans, PermContr.toEquiv_trans]
  simp only [IndexListColor.contr_contr]

open AddCond in
lemma add_rel_right {T₁ T₂ T₂' : 𝓣.TensorIndex} (h : AddCond T₁ T₂) (h' : T₂ ≈ T₂') :
    T₁ +[h] T₂ ≈ T₁ +[h.rel_right h'] T₂' :=
  (add_comm _).trans ((add_rel_left _ h').trans (add_comm _))

open AddCond in
lemma add_assoc' {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₂ T₃} (h : AddCond T₁ (T₂ +[h'] T₃)) :
    T₁ +[h] (T₂ +[h'] T₃) = T₁ +[h'.of_add_right h] T₂ +[h'.add_left_of_add_right h] T₃ := by
  refine ext _ _ ?_ ?_
  simp only [add_index, IndexListColor.contr_contr]
  simp only [add_index, add_tensor, contr_index, toEquiv, contr_add_tensor, map_add, mapIso_mapIso]
  rw [_root_.add_assoc]
  congr
  rw [← PermContr.toEquiv_contr_eq, ← PermContr.toEquiv_contr_eq]
  rw [PermContr.toEquiv_trans, PermContr.toEquiv_trans, PermContr.toEquiv_trans]
  simp only [IndexListColor.contr_contr]
  simp only [IndexListColor.contr_contr]
  rw [← PermContr.toEquiv_contr_eq, PermContr.toEquiv_trans]
  simp only [IndexListColor.contr_contr]

open AddCond in
lemma add_assoc {T₁ T₂ T₃ : 𝓣.TensorIndex} {h' : AddCond T₁ T₂} (h : AddCond (T₁ +[h'] T₂) T₃) :
    T₁ +[h'] T₂ +[h] T₃ = T₁ +[h'.add_right_of_add_left h] (T₂ +[h'.of_add_left h] T₃) := by
  rw [add_assoc']

/-! TODO: Show that the product is well defined with respect to Rel. -/

/-!

## Product of `TensorIndex` allowed

-/

/-- The condition on two tensors with indices determining if it possible to
  take their product.

  This condition says that the indices of the two tensors can contract nicely,
  after the contraction of indivdual indices has taken place. Note that
  it is required to take the contraction of indivdual tensors before taking the product
  to ensure that the product is well-defined under the `Rel` equivalence relation.

  For example, indices with the same id have dual colors, and no more then two indices
  have the same id (after contraction). For example, the product of `ψᵘ¹ᵤ₂ᵘ²` could be taken with
  `φᵤ₁ᵤ₃ᵘ³` or `φᵤ₄ᵤ₃ᵘ³` or `φᵤ₁ᵤ₂ᵘ²` or `φᵤ₂ᵤ₁ᵘ¹`
  (since contraction is done before taking the product)
   but not with `φᵤ₁ᵤ₃ᵘ³` or `φᵤ₁ᵤ₂ᵘ²` or  `φᵤ₃ᵤ₂ᵘ²`. -/
def ProdCond (T₁ T₂ : 𝓣.TensorIndex) : Prop :=
  IndexListColorProp 𝓣.toTensorColor (T₁.contr.index.1 ++ T₂.contr.index.1)

namespace ProdCond

lemma to_indexListColorProp {T₁ T₂ : 𝓣.TensorIndex} (h : ProdCond T₁ T₂) :
    IndexListColorProp 𝓣.toTensorColor (T₁.contr.index.1 ++ T₂.contr.index.1) := h

end ProdCond

/-- The tensor product of two `TensorIndex`. -/
def prod (T₁ T₂ : 𝓣.TensorIndex)
    (h : ProdCond T₁ T₂) : 𝓣.TensorIndex where
  index := T₁.contr.index.prod T₂.contr.index h.to_indexListColorProp
  tensor :=
      𝓣.mapIso ((Fin.castOrderIso (IndexListColor.prod_numIndices)).toEquiv.trans
        (finSumFinEquiv.symm)).symm
      (IndexListColor.prod_colorMap h) <|
      𝓣.tensoratorEquiv _ _ (T₁.contr.tensor ⊗ₜ[R] T₂.contr.tensor)

@[simp]
lemma prod_index (T₁ T₂ : 𝓣.TensorIndex) (h : ProdCond T₁ T₂) :
    (prod T₁ T₂ h).index = T₁.contr.index.prod T₂.contr.index h.to_indexListColorProp := rfl


end TensorIndex
end
end TensorStructure
