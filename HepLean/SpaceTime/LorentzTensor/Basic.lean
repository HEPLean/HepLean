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

noncomputable section

open TensorProduct

variable {R : Type} [CommSemiring R]

def contrDualLeftAux {V1 V2 V3 : Type} [AddCommMonoid V1] [AddCommMonoid V2] [AddCommMonoid V3]
    [Module R V1] [Module R V2] [Module R V3] (f : V1 ⊗[R] V2 →ₗ[R] R) :
    V1 ⊗[R] V2 ⊗[R] V3 →ₗ[R] V3 :=
  (TensorProduct.lid R _).toLinearMap ∘ₗ
  TensorProduct.map (f) (LinearEquiv.refl R V3).toLinearMap
  ∘ₗ (TensorProduct.assoc R _ _ _).symm.toLinearMap

def contrDualMidAux {V1 V2 V3 V4 : Type} [AddCommMonoid V1] [AddCommMonoid V2] [AddCommMonoid V3]
    [AddCommMonoid V4] [Module R V1] [Module R V2] [Module R V3] [Module R V4] (f : V1 ⊗[R] V2 →ₗ[R] R) :
    (V4 ⊗[R] V1) ⊗[R] (V2 ⊗[R] V3) →ₗ[R] V4 ⊗[R] V3 :=
  (TensorProduct.map (LinearEquiv.refl R V4).toLinearMap (contrDualLeftAux f)) ∘ₗ
  (TensorProduct.assoc R _ _ _).toLinearMap

/-- An initial structure specifying a tensor system (e.g. a system in which you can
  define real Lorentz tensors or Einstein notation convention). -/
structure TensorStructure (R : Type) [CommSemiring R] where
  /-- The allowed colors of indices.
    For example for a real Lorentz tensor these are `{up, down}`. -/
  Color : Type
  /-- To each color we associate a module. -/
  ColorModule : Color → Type
  /-- A map taking every color to its dual color. -/
  τ : Color → Color
  /-- The map `τ` is an involution. -/
  τ_involutive : Function.Involutive τ
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
  unit : (μ : Color) → ColorModule μ ⊗[R] ColorModule (τ μ)
  /-- The unit is a right identity. -/
  unit_lid : ∀ μ (x : ColorModule μ),
    TensorProduct.rid R _
    (TensorProduct.map (LinearEquiv.refl R (ColorModule μ)).toLinearMap
    (contrDual μ ∘ₗ (TensorProduct.comm R _ _).toLinearMap)
    ((TensorProduct.assoc R _ _ _) (unit μ ⊗ₜ[R] x))) = x
  /-- The metric for a given color. -/
  metric : (μ : Color) → ColorModule μ ⊗[R] ColorModule μ
  /-- The metric contracted with its dual is the unit. -/
  metric_dual : ∀ (μ : Color), (contrDualMidAux (contrDual μ)
    (metric μ ⊗ₜ[R] metric (τ μ))) = unit μ

namespace TensorStructure

variable (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color}
  {cW : W → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}

instance : AddCommMonoid (𝓣.ColorModule μ) := 𝓣.colorModule_addCommMonoid μ

instance : Module R (𝓣.ColorModule μ) := 𝓣.colorModule_module μ

/-- The type of tensors given a map from an indexing set `X` to the type of colors,
  specifying the color of that index. -/
def Tensor (c : X → 𝓣.Color) : Type := ⨂[R] x, 𝓣.ColorModule (c x)

instance : AddCommMonoid (𝓣.Tensor cX) :=
  PiTensorProduct.instAddCommMonoid fun i => 𝓣.ColorModule (cX i)

instance : Module R (𝓣.Tensor cX) := PiTensorProduct.instModule

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
def mapIso {c : X → 𝓣.Color} {d : Y → 𝓣.Color} (e : X ≃ Y) (h : c = d ∘ e) :
    𝓣.Tensor c ≃ₗ[R] 𝓣.Tensor d :=
  (PiTensorProduct.reindex R _ e) ≪≫ₗ
  (PiTensorProduct.congr (fun y => 𝓣.colorModuleCast (by rw [h]; simp)))

lemma mapIso_trans_cond {e : X ≃ Y} {e' : Y ≃ Z} (h : cX = cY ∘ e) (h' : cY = cZ ∘ e') :
    cX = cZ ∘ (e.trans e') := by
  funext a
  subst h h'
  simp

@[simp]
lemma mapIso_trans (e : X ≃ Y) (e' : Y ≃ Z) (h : cX = cY ∘ e) (h' : cY = cZ ∘ e') :
    (𝓣.mapIso e h ≪≫ₗ 𝓣.mapIso e' h') = 𝓣.mapIso (e.trans e') (𝓣.mapIso_trans_cond h h') := by
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
lemma mapIso_mapIso (e : X ≃ Y) (e' : Y ≃ Z) (h : cX = cY ∘ e) (h' : cY = cZ ∘ e')
    (T : 𝓣.Tensor cX) :
    (𝓣.mapIso e' h') (𝓣.mapIso e h T) = 𝓣.mapIso (e.trans e') (𝓣.mapIso_trans_cond h h') T := by
  rw [← LinearEquiv.trans_apply, mapIso_trans]

@[simp]
lemma mapIso_symm (e : X ≃ Y) (h : cX = cY ∘ e) :
    (𝓣.mapIso e h).symm = 𝓣.mapIso e.symm ((Equiv.eq_comp_symm e cY cX).mpr h.symm) := by
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
lemma mapIso_tprod {c : X → 𝓣.Color} {d : Y → 𝓣.Color} (e : X ≃ Y) (h : c = d ∘ e)
    (f : (i : X) → 𝓣.ColorModule (c i)) : (𝓣.mapIso e h) (PiTensorProduct.tprod R f) =
    (PiTensorProduct.tprod R (fun i => 𝓣.colorModuleCast (by rw [h]; simp) (f (e.symm i)))) := by
  simp [mapIso]
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
    rename_i h
    subst h
    simp_all only
    rfl

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
    rename_i h
    subst h
    simp_all only
    rfl
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
  next h =>
    subst h
    simp_all only
  rfl

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
  next h =>
    subst h
    simp_all only
  rfl

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

lemma tensoratorEquiv_mapIso_cond {e : X ≃ Y} {e' : Z ≃ Y} {e'' : W ≃ X}
    (h : cX = 𝓣.τ ∘ cY ∘ e) (h' : cZ = cY ∘ e') (h'' : bW = cX ∘ e'') :
    Sum.elim bW cZ = Sum.elim cX cY ∘ ⇑(e''.sumCongr e') := by
  subst h h' h''
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

@[simp]
lemma tensoratorEquiv_mapIso (e : X ≃ Y) (e' : Z ≃ Y) (e'' : W ≃ X)
    (h : cX = 𝓣.τ ∘ cY ∘ e) (h' : cZ = cY ∘ e') (h'' : bW = cX ∘ e'') :
    (TensorProduct.congr (𝓣.mapIso e'' h'') (𝓣.mapIso e' h')) ≪≫ₗ (𝓣.tensoratorEquiv cX cY)
    = (𝓣.tensoratorEquiv bW cZ)
    ≪≫ₗ (𝓣.mapIso (Equiv.sumCongr e'' e') (𝓣.tensoratorEquiv_mapIso_cond h h' h'')) := by
  apply LinearEquiv.toLinearMap_inj.mp
  apply tensorProd_piTensorProd_ext
  intro p q
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, congr_tmul, mapIso_tprod,
    tensoratorEquiv_tmul_tprod, Equiv.sumCongr_symm, Equiv.sumCongr_apply]
  apply congrArg
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

@[simp]
lemma tensoratorEquiv_mapIso_apply (e : X ≃ Y) (e' : Z ≃ Y) (e'' : W ≃ X)
    (h : cX = 𝓣.τ ∘ cY ∘ e) (h' : cZ = cY ∘ e') (h'' : cW = cX ∘ e'')
    (x : 𝓣.Tensor cW ⊗[R] 𝓣.Tensor cZ) :
    (𝓣.tensoratorEquiv cX cY) ((TensorProduct.congr (𝓣.mapIso e'' h'') (𝓣.mapIso e' h')) x) =
    (𝓣.mapIso (Equiv.sumCongr e'' e') (𝓣.tensoratorEquiv_mapIso_cond h h' h''))
    ((𝓣.tensoratorEquiv cW cZ) x) := by
  trans ((TensorProduct.congr (𝓣.mapIso e'' h'') (𝓣.mapIso e' h')) ≪≫ₗ
    (𝓣.tensoratorEquiv cX cY)) x
  rfl
  rw [tensoratorEquiv_mapIso]
  rfl
  exact e
  exact h

lemma tensoratorEquiv_mapIso_tmul (e : X ≃ Y) (e' : Z ≃ Y) (e'' : W ≃ X)
    (h : cX = 𝓣.τ ∘ cY ∘ e) (h' : cZ = cY ∘ e') (h'' : cW = cX ∘ e'')
    (x : 𝓣.Tensor cW) (y : 𝓣.Tensor cZ) :
    (𝓣.tensoratorEquiv cX cY) ((𝓣.mapIso e'' h'' x) ⊗ₜ[R] (𝓣.mapIso e' h' y)) =
    (𝓣.mapIso (Equiv.sumCongr e'' e') (𝓣.tensoratorEquiv_mapIso_cond h h' h''))
    ((𝓣.tensoratorEquiv cW cZ) (x ⊗ₜ y)) := by
  rw [← tensoratorEquiv_mapIso_apply]
  rfl
  exact e
  exact h

/-!

## Splitting tensors into tensor products

-/

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
