/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.DFinsupp
/-!

# Structure of Tensors

This file sets up the structure `TensorStructure` which contains
data of types (or `colors`) of indices, the dual of colors, the associated module,
contraction between color modules, and the unit of contraction.

This structure is extended to `DualizeTensorStructure` which adds a metric to the tensor structure,
allowing a vector to be taken to its dual vector by contraction with a specified metric.
The definition of `DualizeTensorStructure` can be found in
`HepLean.SpaceTime.LorentzTensor.RisingLowering`.

The structure `DualizeTensorStructure` is further extended in
`HepLean.SpaceTime.LorentzTensor.LorentzTensorStruct` to add a group action on the tensor space,
under which contraction and rising and lowering etc, are invariant.

## References

-- For modular operads see: [Raynor][raynor2021graphical]

-/

open TensorProduct

variable {R : Type} [CommSemiring R]

/-- The index color data associated with a tensor structure.
    This corresponds to a type with an involution. -/
structure TensorColor where
  /-- The allowed colors of indices.
    For example for a real Lorentz tensor these are `{up, down}`. -/
  Color : Type
  /-- A map taking every color to its dual color. -/
  τ : Color → Color
  /-- The map `τ` is an involution. -/
  τ_involutive : Function.Involutive τ

namespace TensorColor

variable (𝓒 : TensorColor) [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]
variable {d : ℕ} {X X' Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]

/-- A relation on colors which is true if the two colors are equal or are duals. -/
def colorRel (μ ν : 𝓒.Color) : Prop := μ = ν ∨ μ = 𝓒.τ ν

instance : Decidable (colorRel 𝓒 μ ν) :=
  Or.decidable

/-- An equivalence relation on colors which is true if the two colors are equal or are duals. -/
lemma colorRel_equivalence : Equivalence 𝓒.colorRel where
  refl := by
    intro x
    left
    rfl
  symm := by
    intro x y h
    rcases h with h | h
    · left
      exact h.symm
    · right
      subst h
      exact (𝓒.τ_involutive y).symm
  trans := by
    intro x y z hxy hyz
    rcases hxy with hxy | hxy <;>
      rcases hyz with hyz | hyz <;>
      subst hxy hyz
    · left
      rfl
    · right
      rfl
    · right
      rfl
    · left
      exact 𝓒.τ_involutive z

/-- The structure of a setoid on colors, two colors are related if they are equal,
  or dual. -/
instance colorSetoid : Setoid 𝓒.Color := ⟨𝓒.colorRel, 𝓒.colorRel_equivalence⟩

/-- A map taking a color to its equivalence class in `colorSetoid`. -/
def colorQuot (μ : 𝓒.Color) : Quotient 𝓒.colorSetoid :=
  Quotient.mk 𝓒.colorSetoid μ

instance (μ ν : 𝓒.Color) : Decidable (μ ≈ ν) :=
  Or.decidable

instance : DecidableEq (Quotient 𝓒.colorSetoid) :=
  instDecidableEqQuotientOfDecidableEquiv

/-- The types of maps from an `X` to `𝓒.Color`. -/
def ColorMap (X : Type) := X → 𝓒.Color

namespace ColorMap

variable {𝓒 : TensorColor} [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

variable (cX : ColorMap 𝓒 X) (cY : ColorMap 𝓒 Y) (cZ : ColorMap 𝓒 Z)

/-- A relation, given an equivalence of types, between ColorMap which is true
  if related by composition of the equivalence. -/
def MapIso (e : X ≃ Y) (cX : ColorMap 𝓒 X) (cY : ColorMap 𝓒 Y) : Prop := cX = cY ∘ e

/-- The sum of two color maps, formed by `Sum.elim`. -/
def sum (cX : ColorMap 𝓒 X) (cY : ColorMap 𝓒 Y) : ColorMap 𝓒 (Sum X Y) :=
  Sum.elim cX cY

/-- The dual of a color map, formed by composition with `𝓒.τ`. -/
def dual (cX : ColorMap 𝓒 X) : ColorMap 𝓒 X := 𝓒.τ ∘ cX

namespace MapIso

variable {e : X ≃ Y} {e' : Y ≃ Z} {cX : ColorMap 𝓒 X} {cY : ColorMap 𝓒 Y} {cZ : ColorMap 𝓒 Z}
variable {cX' : ColorMap 𝓒 X'} {cY' : ColorMap 𝓒 Y'}

lemma symm (h : cX.MapIso e cY) : cY.MapIso e.symm cX := by
  rw [MapIso] at h
  exact (Equiv.eq_comp_symm e cY cX).mpr h.symm

lemma symm' : cX.MapIso e cY ↔ cY.MapIso e.symm cX := by
  refine ⟨symm, symm⟩

lemma trans (h : cX.MapIso e cY) (h' : cY.MapIso e' cZ) :
    cX.MapIso (e.trans e') cZ:= by
  funext a
  subst h h'
  rfl

lemma sum {eX : X ≃ X'} {eY : Y ≃ Y'} (hX : cX.MapIso eX cX') (hY : cY.MapIso eY cY') :
    (cX.sum cY).MapIso (eX.sumCongr eY) (cX'.sum cY') := by
  funext x
  subst hX hY
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

lemma dual {e : X ≃ Y} (h : cX.MapIso e cY) :
    cX.dual.MapIso e cY.dual := by
  subst h
  rfl

end MapIso

end ColorMap

end TensorColor

noncomputable section
namespace TensorStructure

/-- An auxillary function to contract the vector space `V1` and `V2` in `V1 ⊗[R] V2 ⊗[R] V3`. -/
def contrLeftAux {V1 V2 V3 : Type} [AddCommMonoid V1] [AddCommMonoid V2] [AddCommMonoid V3]
    [Module R V1] [Module R V2] [Module R V3] (f : V1 ⊗[R] V2 →ₗ[R] R) :
    V1 ⊗[R] V2 ⊗[R] V3 →ₗ[R] V3 :=
  (TensorProduct.lid R _).toLinearMap ∘ₗ
  TensorProduct.map (f) (LinearEquiv.refl R V3).toLinearMap
  ∘ₗ (TensorProduct.assoc R _ _ _).symm.toLinearMap

/-- An auxillary function to contract the vector space `V1` and `V2` in `(V3 ⊗[R] V1) ⊗[R] V2`. -/
def contrRightAux {V1 V2 V3 : Type} [AddCommMonoid V1] [AddCommMonoid V2] [AddCommMonoid V3]
    [Module R V1] [Module R V2] [Module R V3] (f : V1 ⊗[R] V2 →ₗ[R] R) :
    (V3 ⊗[R] V1) ⊗[R] V2 →ₗ[R] V3 :=
  (TensorProduct.rid R _).toLinearMap ∘ₗ
  TensorProduct.map (LinearEquiv.refl R V3).toLinearMap f ∘ₗ
  (TensorProduct.assoc R _ _ _).toLinearMap

/-- An auxillary function to contract the vector space `V1` and `V2` in
  `V4 ⊗[R] V1 ⊗[R] V2 ⊗[R] V3`. -/
def contrMidAux {V1 V2 V3 V4 : Type} [AddCommMonoid V1] [AddCommMonoid V2] [AddCommMonoid V3]
    [AddCommMonoid V4] [Module R V1] [Module R V2] [Module R V3] [Module R V4]
    (f : V1 ⊗[R] V2 →ₗ[R] R) : (V4 ⊗[R] V1) ⊗[R] (V2 ⊗[R] V3) →ₗ[R] V4 ⊗[R] V3 :=
  (TensorProduct.map (LinearEquiv.refl R V4).toLinearMap (contrLeftAux f)) ∘ₗ
  (TensorProduct.assoc R _ _ _).toLinearMap

lemma contrRightAux_comp {V1 V2 V3 V4 V5 : Type} [AddCommMonoid V1] [AddCommMonoid V2]
    [AddCommMonoid V3] [AddCommMonoid V4] [AddCommMonoid V5] [Module R V1] [Module R V3]
    [Module R V2] [Module R V4] [Module R V5] (f : V2 ⊗[R] V3 →ₗ[R] R) (g : V4 ⊗[R] V5 →ₗ[R] R) :
    (contrRightAux f ∘ₗ TensorProduct.map (LinearMap.id : V1 ⊗[R] V2 →ₗ[R] V1 ⊗[R] V2)
      (contrRightAux g)) =
    (contrRightAux g) ∘ₗ TensorProduct.map (contrMidAux f) LinearMap.id
    ∘ₗ (TensorProduct.assoc R _ _ _).symm.toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  refine TensorProduct.induction_on x (by simp) ?_ (fun x z h1 h2 =>
    by simp [add_tmul, LinearMap.map_add, h1, h2])
  intro x1 x2
  refine TensorProduct.induction_on y (by simp) ?_ (fun x z h1 h2 =>
    by simp [add_tmul, tmul_add, LinearMap.map_add, h1, h2])
  intro y x5
  refine TensorProduct.induction_on y (by simp) ?_ (fun x z h1 h2 =>
    by simp [add_tmul, tmul_add, LinearMap.map_add, h1, h2])
  intro x3 x4
  simp [contrRightAux, contrMidAux, contrLeftAux]
  rfl

end TensorStructure

/-- An initial structure specifying a tensor system (e.g. a system in which you can
  define real Lorentz tensors or Einstein notation convention). -/
structure TensorStructure (R : Type) [CommSemiring R] extends TensorColor where
  /-- To each color we associate a module. -/
  ColorModule : Color → Type
  /-- Each `ColorModule` has the structure of an additive commutative monoid. -/
  colorModule_addCommMonoid : ∀ μ, AddCommMonoid (ColorModule μ)
  /-- Each `ColorModule` has the structure of a module over `R`. -/
  colorModule_module : ∀ μ, Module R (ColorModule μ)
  /-- The contraction of a vector with a vector with dual color. -/
  contrDual : ∀ μ, ColorModule μ ⊗[R] ColorModule (τ μ) →ₗ[R] R
  /-- The contraction is symmetric. -/
  contrDual_symm : ∀ μ x y, (contrDual μ) (x ⊗ₜ[R] y) =
    (contrDual (τ μ)) (y ⊗ₜ[R] (Equiv.cast (congrArg ColorModule (τ_involutive μ).symm) x))
  /-- The unit of the contraction. -/
  unit : (μ : Color) → ColorModule (τ μ) ⊗[R] ColorModule μ
  /-- The unit is a right identity. -/
  unit_rid : ∀ μ (x : ColorModule μ),
    TensorStructure.contrLeftAux (contrDual μ) (x ⊗ₜ[R] unit μ) = x
  /-- The metric for a given color. -/
  metric : (μ : Color) → ColorModule μ ⊗[R] ColorModule μ
  /-- The metric contracted with its dual is the unit. -/
  metric_dual : ∀ (μ : Color), (TensorStructure.contrMidAux (contrDual μ)
    (metric μ ⊗ₜ[R] metric (τ μ))) = TensorProduct.comm _ _ _ (unit μ)

namespace TensorStructure

variable (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  {cX cX2 : 𝓣.ColorMap X} {cY : 𝓣.ColorMap Y} {cZ : 𝓣.ColorMap Z}
  {cW : 𝓣.ColorMap W} {cY' : 𝓣.ColorMap Y'} {μ ν η : 𝓣.Color}

instance : AddCommMonoid (𝓣.ColorModule μ) := 𝓣.colorModule_addCommMonoid μ

instance : Module R (𝓣.ColorModule μ) := 𝓣.colorModule_module μ

/-- The type of tensors given a map from an indexing set `X` to the type of colors,
  specifying the color of that index. -/
def Tensor (c : 𝓣.ColorMap X) : Type := ⨂[R] x, 𝓣.ColorModule (c x)

instance : AddCommMonoid (𝓣.Tensor cX) :=
  PiTensorProduct.instAddCommMonoid fun i => 𝓣.ColorModule (cX i)

instance : Module R (𝓣.Tensor cX) := PiTensorProduct.instModule

/-!

## Color

Recall the `color` of an index describes the type of the index.

For example, in a real Lorentz tensor the colors are `{up, down}`.

-/

/-- Equivalence of `ColorModule` given an equality of colors. -/
def colorModuleCast (h : μ = ν) : 𝓣.ColorModule μ ≃ₗ[R] 𝓣.ColorModule ν where
  toFun := Equiv.cast (congrArg 𝓣.ColorModule h)
  invFun := (Equiv.cast (congrArg 𝓣.ColorModule h)).symm
  map_add' x y := by
    subst h
    rfl
  map_smul' x y := by
    subst h
    rfl
  left_inv x := Equiv.symm_apply_apply (Equiv.cast (congrArg 𝓣.ColorModule h)) x
  right_inv x := Equiv.apply_symm_apply (Equiv.cast (congrArg 𝓣.ColorModule h)) x

lemma tensorProd_piTensorProd_ext {M : Type} [AddCommMonoid M] [Module R M]
    {f g : 𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY →ₗ[R] M}
    (h : ∀ p q, f (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q)
    = g (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q)) : f = g := by
  apply TensorProduct.ext'
  refine fun x ↦
  PiTensorProduct.induction_on' x ?_ (by
    intro a b hx hy y
    simp [map_add, add_tmul, hx, hy])
  intro rx fx
  refine fun y ↦
    PiTensorProduct.induction_on' y ?_ (by
      intro a b hx hy
      simp at hx hy
      simp [map_add, tmul_add, hx, hy])
  intro ry fy
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, tmul_smul, LinearMapClass.map_smul]
  apply congrArg
  simp only [smul_tmul, tmul_smul, LinearMapClass.map_smul]
  exact congrArg (HSMul.hSMul rx) (h fx fy)

/-!

## Mapping isomorphisms

-/

/-- An linear equivalence of tensor spaces given a color-preserving equivalence of indexing sets. -/
def mapIso {c : 𝓣.ColorMap X} {d : 𝓣.ColorMap Y} (e : X ≃ Y) (h : c.MapIso e d) :
    𝓣.Tensor c ≃ₗ[R] 𝓣.Tensor d :=
  (PiTensorProduct.reindex R _ e) ≪≫ₗ
  (PiTensorProduct.congr (fun y => 𝓣.colorModuleCast (by rw [h]; simp)))

lemma mapIso_ext {c : 𝓣.ColorMap X} {d : 𝓣.ColorMap Y} (e e' : X ≃ Y) (h : c.MapIso e d)
    (h' : c.MapIso e' d) (he : e = e') : 𝓣.mapIso e h = 𝓣.mapIso e' h' := by
  simp [he]

@[simp]
lemma mapIso_trans (e : X ≃ Y) (e' : Y ≃ Z) (h : cX.MapIso e cY) (h' : cY.MapIso e' cZ) :
    (𝓣.mapIso e h ≪≫ₗ 𝓣.mapIso e' h') = 𝓣.mapIso (e.trans e') (h.trans h') := by
  refine LinearEquiv.toLinearMap_inj.mp ?_
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [mapIso, LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod, Equiv.symm_trans_apply]
  change (PiTensorProduct.congr fun y => 𝓣.colorModuleCast _)
    ((PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (cY x)) e')
    ((PiTensorProduct.congr fun y => 𝓣.colorModuleCast _) _)) =
    (PiTensorProduct.congr fun y => 𝓣.colorModuleCast _)
    ((PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (cX x)) (e.trans e')) _)
  rw [PiTensorProduct.congr_tprod, PiTensorProduct.reindex_tprod,
    PiTensorProduct.congr_tprod, PiTensorProduct.reindex_tprod, PiTensorProduct.congr]
  simp [colorModuleCast]

@[simp]
lemma mapIso_mapIso (e : X ≃ Y) (e' : Y ≃ Z) (h : cX.MapIso e cY) (h' : cY.MapIso e' cZ)
    (T : 𝓣.Tensor cX) :
    (𝓣.mapIso e' h') (𝓣.mapIso e h T) = 𝓣.mapIso (e.trans e') (h.trans h') T := by
  rw [← LinearEquiv.trans_apply, mapIso_trans]

@[simp]
lemma mapIso_symm (e : X ≃ Y) (h : cX.MapIso e cY) :
    (𝓣.mapIso e h).symm = 𝓣.mapIso e.symm (h.symm) := by
  refine LinearEquiv.toLinearMap_inj.mp ?_
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp [mapIso, LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, PiTensorProduct.reindex_tprod]
  change (PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (cX x)) e).symm
    ((PiTensorProduct.congr fun y => 𝓣.colorModuleCast _).symm ((PiTensorProduct.tprod R) x)) =
    (PiTensorProduct.congr fun y => 𝓣.colorModuleCast _)
    ((PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (cY x)) e.symm)
    ((PiTensorProduct.tprod R) x))
  rw [PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod, PiTensorProduct.congr_symm_tprod,
    LinearEquiv.symm_apply_eq, PiTensorProduct.reindex_tprod]
  apply congrArg
  funext i
  simp only [colorModuleCast, Equiv.cast_symm, LinearEquiv.coe_symm_mk,
    Equiv.symm_symm_apply, LinearEquiv.coe_mk]
  rw [← Equiv.symm_apply_eq]
  simp only [Equiv.cast_symm, Equiv.cast_apply, cast_cast]
  apply cast_eq_iff_heq.mpr
  rw [Equiv.apply_symm_apply]

@[simp]
lemma mapIso_refl : 𝓣.mapIso (Equiv.refl X) (rfl : cX = cX) = LinearEquiv.refl R _ := by
  refine LinearEquiv.toLinearMap_inj.mp ?_
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [mapIso, Equiv.refl_symm, Equiv.refl_apply, PiTensorProduct.reindex_refl,
    LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    LinearEquiv.refl_apply, LinearEquiv.refl_toLinearMap, LinearMap.id, LinearMap.coe_mk,
    AddHom.coe_mk, id_eq]
  change (PiTensorProduct.congr fun y => 𝓣.colorModuleCast _) ((PiTensorProduct.tprod R) x) = _
  rw [PiTensorProduct.congr_tprod]
  rfl

@[simp]
lemma mapIso_tprod {c : 𝓣.ColorMap X} {d : 𝓣.ColorMap Y} (e : X ≃ Y) (h : c.MapIso e d)
    (f : (i : X) → 𝓣.ColorModule (c i)) : (𝓣.mapIso e h) (PiTensorProduct.tprod R f) =
    (PiTensorProduct.tprod R (fun i => 𝓣.colorModuleCast (by rw [h]; simp) (f (e.symm i)))) := by
  simp only [mapIso, LinearEquiv.trans_apply]
  change (PiTensorProduct.congr fun y => 𝓣.colorModuleCast _)
    ((PiTensorProduct.reindex R _ e) ((PiTensorProduct.tprod R) f)) = _
  rw [PiTensorProduct.reindex_tprod]
  exact PiTensorProduct.congr_tprod (fun y => 𝓣.colorModuleCast _) fun i => f (e.symm i)

/-!

## Pure tensors

This section is needed since: `PiTensorProduct.tmulEquiv` is not defined for dependent types.
Hence we need to construct a version of it here.

-/

/-- The type of pure tensors, i.e. of the form `v1 ⊗ v2 ⊗ v3 ⊗ ...`. -/
abbrev PureTensor (c : X → 𝓣.Color) := (x : X) → 𝓣.ColorModule (c x)

/-- A pure tensor in `𝓣.PureTensor (Sum.elim cX cY)` constructed from a pure tensor
  in `𝓣.PureTensor cX` and a pure tensor in `𝓣.PureTensor cY`. -/
def elimPureTensor (p : 𝓣.PureTensor cX) (q : 𝓣.PureTensor cY) : 𝓣.PureTensor (Sum.elim cX cY) :=
  fun x =>
    match x with
    | Sum.inl x => p x
    | Sum.inr x => q x

@[simp]
lemma elimPureTensor_update_right (p : 𝓣.PureTensor cX) (q : 𝓣.PureTensor cY)
    (y : Y) (r : 𝓣.ColorModule (cY y)) : 𝓣.elimPureTensor p (Function.update q y r) =
    Function.update (𝓣.elimPureTensor p q) (Sum.inr y) r := by
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x =>
    change Function.update q y r x = _
    simp only [Function.update, Sum.inr.injEq, Sum.elim_inr]
    split_ifs
    · rename_i h
      subst h
      simp_all only
    · rfl

@[simp]
lemma elimPureTensor_update_left (p : 𝓣.PureTensor cX) (q : 𝓣.PureTensor cY)
    (x : X) (r : 𝓣.ColorModule (cX x)) : 𝓣.elimPureTensor (Function.update p x r) q =
    Function.update (𝓣.elimPureTensor p q) (Sum.inl x) r := by
  funext y
  match y with
  | Sum.inl y =>
    change (Function.update p x r) y = _
    simp only [Function.update, Sum.inl.injEq, Sum.elim_inl]
    split_ifs
    · rename_i h
      subst h
      rfl
    · rfl
  | Sum.inr y => rfl

/-- The projection of a pure tensor in `𝓣.PureTensor (Sum.elim cX cY)` onto a pure tensor in
  `𝓣.PureTensor cX`. -/
def inlPureTensor (p : 𝓣.PureTensor (Sum.elim cX cY)) : 𝓣.PureTensor cX := fun x => p (Sum.inl x)

/-- The projection of a pure tensor in `𝓣.PureTensor (Sum.elim cX cY)` onto a pure tensor in
  `𝓣.PureTensor cY`. -/
def inrPureTensor (p : 𝓣.PureTensor (Sum.elim cX cY)) : 𝓣.PureTensor cY := fun y => p (Sum.inr y)

@[simp]
lemma inlPureTensor_update_left [DecidableEq (X ⊕ Y)] (f : 𝓣.PureTensor (Sum.elim cX cY)) (x : X)
    (v1 : 𝓣.ColorModule (Sum.elim cX cY (Sum.inl x))) :
    𝓣.inlPureTensor (Function.update f (Sum.inl x) v1) =
    Function.update (𝓣.inlPureTensor f) x v1 := by
  funext y
  simp [inlPureTensor, Function.update, Sum.inl.injEq, Sum.elim_inl]
  split
  · rename_i h
    subst h
    rfl
  · rfl

@[simp]
lemma inrPureTensor_update_left [DecidableEq (X ⊕ Y)] (f : 𝓣.PureTensor (Sum.elim cX cY)) (x : X)
    (v1 : 𝓣.ColorModule (Sum.elim cX cY (Sum.inl x))) :
    𝓣.inrPureTensor (Function.update f (Sum.inl x) v1) = (𝓣.inrPureTensor f) := by
  funext x
  simp [inrPureTensor, Function.update]

@[simp]
lemma inrPureTensor_update_right [DecidableEq (X ⊕ Y)] (f : 𝓣.PureTensor (Sum.elim cX cY)) (y : Y)
    (v1 : 𝓣.ColorModule (Sum.elim cX cY (Sum.inr y))) :
    𝓣.inrPureTensor (Function.update f (Sum.inr y) v1) =
    Function.update (𝓣.inrPureTensor f) y v1 := by
  funext y
  simp [inrPureTensor, Function.update, Sum.inl.injEq, Sum.elim_inl]
  split
  · rename_i h
    subst h
    rfl
  · rfl

@[simp]
lemma inlPureTensor_update_right [DecidableEq (X ⊕ Y)] (f : 𝓣.PureTensor (Sum.elim cX cY)) (y : Y)
    (v1 : 𝓣.ColorModule (Sum.elim cX cY (Sum.inr y))) :
    𝓣.inlPureTensor (Function.update f (Sum.inr y) v1) = (𝓣.inlPureTensor f) := by
  funext x
  simp [inlPureTensor, Function.update]

/-- The multilinear map taking pure tensors a `𝓣.PureTensor cX` and a pure tensor in
  `𝓣.PureTensor cY`, and constructing a tensor in `𝓣.Tensor (Sum.elim cX cY))`. -/
def elimPureTensorMulLin : MultilinearMap R (fun i => 𝓣.ColorModule (cX i))
    (MultilinearMap R (fun x => 𝓣.ColorModule (cY x)) (𝓣.Tensor (Sum.elim cX cY))) where
  toFun p := {
    toFun := fun q => PiTensorProduct.tprod R (𝓣.elimPureTensor p q)
    map_add' := fun m x v1 v2 => by
      simp [Sum.elim_inl, Sum.elim_inr]
    map_smul' := fun m x r v => by
      simp [Sum.elim_inl, Sum.elim_inr]}
  map_add' p x v1 v2 := by
    apply MultilinearMap.ext
    intro y
    simp
  map_smul' p x r v := by
    apply MultilinearMap.ext
    intro y
    simp

/-!

## tensorator

-/

/-! TODO: Replace with dependent type version of `MultilinearMap.domCoprod` when in Mathlib. -/
/-- The multi-linear map taking a pure tensor in `𝓣.PureTensor (Sum.elim cX cY)` and constructing
  a vector in `𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY`. -/
def domCoprod : MultilinearMap R (fun x => 𝓣.ColorModule (Sum.elim cX cY x))
    (𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY) where
  toFun f := (PiTensorProduct.tprod R (𝓣.inlPureTensor f)) ⊗ₜ
    (PiTensorProduct.tprod R (𝓣.inrPureTensor f))
  map_add' f xy v1 v2:= by
    match xy with
    | Sum.inl x => simp [← TensorProduct.add_tmul]
    | Sum.inr y => simp [← TensorProduct.tmul_add]
  map_smul' f xy r p := by
    match xy with
    | Sum.inl x => simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul]
    | Sum.inr y => simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul]

/-- The linear map combining two tensors into a single tensor
  via the tensor product i.e. `v1 v2 ↦ v1 ⊗ v2`. -/
def tensoratorSymm : 𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY →ₗ[R] 𝓣.Tensor (Sum.elim cX cY) := by
  refine TensorProduct.lift {
    toFun := fun a ↦
      PiTensorProduct.lift <|
          PiTensorProduct.lift (𝓣.elimPureTensorMulLin) a,
    map_add' := fun a b ↦ by simp
    map_smul' := fun r a ↦ by simp}

/-! TODO: Replace with dependent type version of `PiTensorProduct.tmulEquiv` when in Mathlib. -/
/-- Splitting a tensor in `𝓣.Tensor (Sum.elim cX cY)` into the tensor product of two tensors. -/
def tensorator : 𝓣.Tensor (Sum.elim cX cY) →ₗ[R] 𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY :=
  PiTensorProduct.lift 𝓣.domCoprod

/-- An equivalence formed by taking the tensor product of tensors. -/
def tensoratorEquiv (c : X → 𝓣.Color) (d : Y → 𝓣.Color) :
    𝓣.Tensor c ⊗[R] 𝓣.Tensor d ≃ₗ[R] 𝓣.Tensor (Sum.elim c d) :=
  LinearEquiv.ofLinear (𝓣.tensoratorSymm) (𝓣.tensorator)
  (by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro p
    simp [tensorator, tensoratorSymm, domCoprod]
    change (PiTensorProduct.lift _) ((PiTensorProduct.tprod R) _) =
      LinearMap.id ((PiTensorProduct.tprod R) p)
    rw [PiTensorProduct.lift.tprod]
    simp [elimPureTensorMulLin, elimPureTensor]
    change (PiTensorProduct.tprod R) _ = _
    apply congrArg
    funext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl)
  (by
    apply tensorProd_piTensorProd_ext
    intro p q
    simp [tensorator, tensoratorSymm]
    change (PiTensorProduct.lift 𝓣.domCoprod)
      ((PiTensorProduct.lift (𝓣.elimPureTensorMulLin p)) ((PiTensorProduct.tprod R) q)) =_
    rw [PiTensorProduct.lift.tprod]
    simp [elimPureTensorMulLin]
    rfl)

@[simp]
lemma tensoratorEquiv_tmul_tprod (p : 𝓣.PureTensor cX) (q : 𝓣.PureTensor cY) :
    (𝓣.tensoratorEquiv cX cY) ((PiTensorProduct.tprod R) p ⊗ₜ[R] (PiTensorProduct.tprod R) q) =
    (PiTensorProduct.tprod R) (𝓣.elimPureTensor p q) := by
  simp only [tensoratorEquiv, tensoratorSymm, tensorator, domCoprod, LinearEquiv.ofLinear_apply,
    lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, PiTensorProduct.lift.tprod]
  exact PiTensorProduct.lift.tprod q

@[simp]
lemma tensoratorEquiv_symm_tprod (f : 𝓣.PureTensor (Sum.elim cX cY)) :
    (𝓣.tensoratorEquiv cX cY).symm ((PiTensorProduct.tprod R) f) =
    (PiTensorProduct.tprod R) (𝓣.inlPureTensor f) ⊗ₜ[R]
    (PiTensorProduct.tprod R) (𝓣.inrPureTensor f) := by
  simp [tensoratorEquiv, tensorator]
  change (PiTensorProduct.lift 𝓣.domCoprod) ((PiTensorProduct.tprod R) f) = _
  simp [domCoprod]

@[simp]
lemma tensoratorEquiv_mapIso (e' : Z ≃ Y) (e'' : W ≃ X)
    (h' : cZ.MapIso e' cY) (h'' : cW.MapIso e'' cX) :
    (TensorProduct.congr (𝓣.mapIso e'' h'') (𝓣.mapIso e' h')) ≪≫ₗ (𝓣.tensoratorEquiv cX cY)
    = (𝓣.tensoratorEquiv cW cZ) ≪≫ₗ (𝓣.mapIso (Equiv.sumCongr e'' e') (h''.sum h')) := by
  apply LinearEquiv.toLinearMap_inj.mp
  apply tensorProd_piTensorProd_ext
  intro p q
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, congr_tmul, mapIso_tprod,
    tensoratorEquiv_tmul_tprod]
  erw [LinearEquiv.trans_apply]
  simp only [tensoratorEquiv_tmul_tprod, mapIso_tprod, Equiv.sumCongr_symm, Equiv.sumCongr_apply]
  apply congrArg
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

@[simp]
lemma tensoratorEquiv_mapIso_apply (e' : Z ≃ Y) (e'' : W ≃ X)
    (h' : cZ.MapIso e' cY) (h'' : cW.MapIso e'' cX)
    (x : 𝓣.Tensor cW ⊗[R] 𝓣.Tensor cZ) :
    (𝓣.tensoratorEquiv cX cY) ((TensorProduct.congr (𝓣.mapIso e'' h'') (𝓣.mapIso e' h')) x) =
    (𝓣.mapIso (Equiv.sumCongr e'' e') (h''.sum h'))
    ((𝓣.tensoratorEquiv cW cZ) x) := by
  trans ((TensorProduct.congr (𝓣.mapIso e'' h'') (𝓣.mapIso e' h')) ≪≫ₗ
    (𝓣.tensoratorEquiv cX cY)) x
  · rfl
  · rw [tensoratorEquiv_mapIso]
    rfl

lemma tensoratorEquiv_mapIso_tmul (e' : Z ≃ Y) (e'' : W ≃ X)
    (h' : cZ.MapIso e' cY) (h'' : cW.MapIso e'' cX)
    (x : 𝓣.Tensor cW) (y : 𝓣.Tensor cZ) :
    (𝓣.tensoratorEquiv cX cY) ((𝓣.mapIso e'' h'' x) ⊗ₜ[R] (𝓣.mapIso e' h' y)) =
    (𝓣.mapIso (Equiv.sumCongr e'' e') (h''.sum h'))
    ((𝓣.tensoratorEquiv cW cZ) (x ⊗ₜ y)) := by
  rw [← tensoratorEquiv_mapIso_apply]
  rfl

/-!

## contrDual properties

-/

lemma contrDual_cast (h : μ = ν) (x : 𝓣.ColorModule μ) (y : 𝓣.ColorModule (𝓣.τ μ)) :
    𝓣.contrDual μ (x ⊗ₜ[R] y) = 𝓣.contrDual ν (𝓣.colorModuleCast h x ⊗ₜ[R]
      𝓣.colorModuleCast (congrArg 𝓣.τ h) y) := by
  subst h
  rfl

/-- `𝓣.contrDual (𝓣.τ μ)` in terms of `𝓣.contrDual μ`. -/
@[simp]
lemma contrDual_symm' (μ : 𝓣.Color) (x : 𝓣.ColorModule (𝓣.τ μ))
    (y : 𝓣.ColorModule (𝓣.τ (𝓣.τ μ))) : 𝓣.contrDual (𝓣.τ μ) (x ⊗ₜ[R] y) =
    (𝓣.contrDual μ) ((𝓣.colorModuleCast (𝓣.τ_involutive μ) y) ⊗ₜ[R] x) := by
  rw [𝓣.contrDual_symm, 𝓣.contrDual_cast (𝓣.τ_involutive μ)]
  congr
  exact (LinearEquiv.eq_symm_apply (𝓣.colorModuleCast (congrArg 𝓣.τ (𝓣.τ_involutive μ)))).mp rfl

lemma contrDual_symm_contrRightAux (h : ν = η) :
    (𝓣.colorModuleCast h) ∘ₗ contrRightAux (𝓣.contrDual μ) =
    contrRightAux (𝓣.contrDual (𝓣.τ (𝓣.τ μ))) ∘ₗ
    (TensorProduct.congr (
      TensorProduct.congr (𝓣.colorModuleCast h) (𝓣.colorModuleCast (𝓣.τ_involutive μ).symm))
    (𝓣.colorModuleCast ((𝓣.τ_involutive (𝓣.τ μ)).symm))).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  refine TensorProduct.induction_on x (by simp) ?_ ?_
  · intro x z
    simp [contrRightAux]
    congr
    · exact (LinearEquiv.symm_apply_eq (𝓣.colorModuleCast (𝓣.τ_involutive μ))).mp rfl
    · exact (LinearEquiv.symm_apply_eq (𝓣.colorModuleCast (𝓣.τ_involutive (𝓣.τ μ)))).mp rfl
  · intro x z h1 h2
    simp [add_tmul, LinearMap.map_add, h1, h2]

lemma contrDual_symm_contrRightAux_apply_tmul (h : ν = η)
    (m : 𝓣.ColorModule ν ⊗[R] 𝓣.ColorModule μ) (x : 𝓣.ColorModule (𝓣.τ μ)) :
    𝓣.colorModuleCast h (contrRightAux (𝓣.contrDual μ) (m ⊗ₜ[R] x)) =
    contrRightAux (𝓣.contrDual (𝓣.τ (𝓣.τ μ))) ((TensorProduct.congr
    (𝓣.colorModuleCast h) (𝓣.colorModuleCast (𝓣.τ_involutive μ).symm) (m)) ⊗ₜ
    (𝓣.colorModuleCast (𝓣.τ_involutive (𝓣.τ μ)).symm x)) := by
  trans ((𝓣.colorModuleCast h) ∘ₗ contrRightAux (𝓣.contrDual μ)) (m ⊗ₜ[R] x)
  · rfl
  · rw [contrDual_symm_contrRightAux]
    rfl

/-!

## Of empty

-/

/-- The equivalence between `𝓣.Tensor cX` and `R` when the indexing set `X` is empty. -/
def isEmptyEquiv [IsEmpty X] : 𝓣.Tensor cX ≃ₗ[R] R :=
  PiTensorProduct.isEmptyEquiv X

@[simp]
lemma isEmptyEquiv_tprod [IsEmpty X] (f : 𝓣.PureTensor cX) :
    𝓣.isEmptyEquiv (PiTensorProduct.tprod R f) = 1 := by
  simp only [isEmptyEquiv]
  erw [PiTensorProduct.isEmptyEquiv_apply_tprod]
/-!

## Splitting tensors into tensor products

-/
/-! TODO: Delete the content of this section. -/

/-- The decomposition of a set into a direct sum based on the image of an injection. -/
def decompEmbedSet (f : Y ↪ X) :
    X ≃ {x // x ∈ (Finset.image f Finset.univ)ᶜ} ⊕ Y :=
  (Equiv.Set.sumCompl (Set.range ⇑f)).symm.trans <|
  (Equiv.sumComm _ _).trans <|
  Equiv.sumCongr ((Equiv.subtypeEquivRight (by simp))) <|
  (Function.Embedding.toEquivRange f).symm

/-- The restriction of a map from an indexing set to the space to the complement of the image
  of an embedding. -/
def decompEmbedColorLeft (c : X → 𝓣.Color) (f : Y ↪ X) :
    {x // x ∈ (Finset.image f Finset.univ)ᶜ} → 𝓣.Color :=
  (c ∘ (decompEmbedSet f).symm) ∘ Sum.inl

/-- The restriction of a map from an indexing set to the space to the image
  of an embedding. -/
def decompEmbedColorRight (c : X → 𝓣.Color) (f : Y ↪ X) : Y → 𝓣.Color :=
  (c ∘ (decompEmbedSet f).symm) ∘ Sum.inr

lemma decompEmbed_cond (c : X → 𝓣.Color) (f : Y ↪ X) : c =
    (Sum.elim (𝓣.decompEmbedColorLeft c f) (𝓣.decompEmbedColorRight c f)) ∘ decompEmbedSet f := by
  simpa [decompEmbedColorLeft, decompEmbedColorRight] using (Equiv.comp_symm_eq _ _ _).mp rfl

/-- Decomposes a tensor into a tensor product of two tensors
  one which has indices in the image of the given embedding, and the other has indices in
  the complement of that image. -/
def decompEmbed (f : Y ↪ X) :
    𝓣.Tensor cX ≃ₗ[R] 𝓣.Tensor (𝓣.decompEmbedColorLeft cX f) ⊗[R] 𝓣.Tensor (cX ∘ f) :=
  (𝓣.mapIso (decompEmbedSet f) (𝓣.decompEmbed_cond cX f)) ≪≫ₗ
  (𝓣.tensoratorEquiv (𝓣.decompEmbedColorLeft cX f) (𝓣.decompEmbedColorRight cX f)).symm

end TensorStructure

end
