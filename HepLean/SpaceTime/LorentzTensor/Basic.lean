/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.RepresentationTheory.Basic
/-!

# Structure of Lorentz Tensors

In this file we set up the basic structures we will use to define Lorentz tensors.

## References

-- For modular operads see: [Raynor][raynor2021graphical]

-/

noncomputable section

open TensorProduct

variable {R : Type} [CommSemiring R]

/-- An initial structure specifying a tensor system (e.g. a system in which you can
  define real Lorentz tensors). -/
structure PreTensorStructure (R : Type) [CommSemiring R] where
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

namespace PreTensorStructure

variable (𝓣 : PreTensorStructure R)

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
  toFun x := Equiv.cast (congrArg 𝓣.ColorModule h) x
  invFun x := (Equiv.cast (congrArg 𝓣.ColorModule h)).symm x
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

/-!

## Contraction

-/

/-- A linear map taking tensors mapped with the same index set to the product of paired tensors. -/
def pairProd : 𝓣.Tensor cX ⊗[R] 𝓣.Tensor cX2 →ₗ[R]
    ⨂[R] x, 𝓣.ColorModule (cX x) ⊗[R] 𝓣.ColorModule (cX2 x) :=
  TensorProduct.lift (
    PiTensorProduct.map₂ (fun x =>
      TensorProduct.mk R (𝓣.ColorModule (cX x)) (𝓣.ColorModule (cX2 x))))

lemma mkPiAlgebra_equiv (e : X ≃ Y) :
    (PiTensorProduct.lift (MultilinearMap.mkPiAlgebra R X R)) =
    (PiTensorProduct.lift (MultilinearMap.mkPiAlgebra R Y R)) ∘ₗ
    (PiTensorProduct.reindex R _ e).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.lift.tprod,
    MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    PiTensorProduct.reindex_tprod, Equiv.prod_comp]

/-- Given a tensor in `𝓣.Tensor cX` and a tensor in `𝓣.Tensor (𝓣.τ ∘ cX)`, the element of
  `R` formed by contracting all of their indices. -/
def contrAll' : 𝓣.Tensor cX ⊗[R] 𝓣.Tensor (𝓣.τ ∘ cX) →ₗ[R] R :=
  (PiTensorProduct.lift (MultilinearMap.mkPiAlgebra R X R)) ∘ₗ
  (PiTensorProduct.map (fun x => 𝓣.contrDual (cX x))) ∘ₗ
  (𝓣.pairProd)

lemma contrAll'_mapIso_cond {e : X ≃ Y} (h : cX = cY ∘ e) :
    𝓣.τ ∘ cY = (𝓣.τ ∘ cX) ∘ ⇑e.symm := by
  subst h
  exact (Equiv.eq_comp_symm e (𝓣.τ ∘ cY) (𝓣.τ ∘ cY ∘ ⇑e)).mpr rfl

@[simp]
lemma contrAll'_mapIso (e : X ≃ Y) (h : c = cY ∘ e) :
    𝓣.contrAll' ∘ₗ
      (TensorProduct.congr (𝓣.mapIso e h) (LinearEquiv.refl R _)).toLinearMap =
    𝓣.contrAll' ∘ₗ (TensorProduct.congr (LinearEquiv.refl R _)
      (𝓣.mapIso e.symm (𝓣.contrAll'_mapIso_cond h))).toLinearMap := by
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
  simp [contrAll']
  rw [mkPiAlgebra_equiv e]
  apply congrArg
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  apply congrArg
  rw [← LinearEquiv.symm_apply_eq]
  rw [PiTensorProduct.reindex_symm]
  rw [← PiTensorProduct.map_reindex]
  subst h
  simp only [Equiv.symm_symm_apply, Function.comp_apply]
  apply congrArg
  rw [pairProd, pairProd]
  simp only [Function.comp_apply, lift.tmul, LinearMapClass.map_smul, LinearMap.smul_apply]
  apply congrArg
  change _ = ((PiTensorProduct.map₂ fun x => TensorProduct.mk R (𝓣.ColorModule (cY (e x)))
      (𝓣.ColorModule (𝓣.τ (cY (e x)))))
      ((PiTensorProduct.tprod R) fx))
    ((𝓣.mapIso e.symm _) ((PiTensorProduct.tprod R) fy))
  rw [mapIso_tprod]
  simp only [Equiv.symm_symm_apply, Function.comp_apply]
  rw [PiTensorProduct.map₂_tprod_tprod]
  change PiTensorProduct.reindex R _ e.symm
    ((PiTensorProduct.map₂ _
        ((PiTensorProduct.tprod R) fun i => (𝓣.colorModuleCast _) (fx (e.symm i))))
      ((PiTensorProduct.tprod R) fy)) = _
  rw [PiTensorProduct.map₂_tprod_tprod]
  simp only [Equiv.symm_symm_apply, Function.comp_apply, mk_apply]
  erw [PiTensorProduct.reindex_tprod]
  apply congrArg
  funext i
  simp only [Equiv.symm_symm_apply]
  congr
  simp [colorModuleCast]
  apply cast_eq_iff_heq.mpr
  rw [Equiv.symm_apply_apply]

@[simp]
lemma contrAll'_mapIso_tmul (e : X ≃ Y) (h : c = cY ∘ e) (x : 𝓣.Tensor c)
    (y : 𝓣.Tensor (𝓣.τ ∘ cY)) : 𝓣.contrAll' ((𝓣.mapIso e h) x ⊗ₜ[R] y) =
    𝓣.contrAll' (x ⊗ₜ[R] (𝓣.mapIso e.symm (𝓣.contrAll'_mapIso_cond h) y)) := by
  change (𝓣.contrAll' ∘ₗ
    (TensorProduct.congr (𝓣.mapIso e h) (LinearEquiv.refl R _)).toLinearMap) (x ⊗ₜ[R] y) = _
  rw [contrAll'_mapIso]
  rfl

/-- The contraction of all the indices of two tensors with dual colors. -/
def contrAll {c : X → 𝓣.Color} {d : Y → 𝓣.Color}
    (e : X ≃ Y) (h : c = 𝓣.τ ∘ d ∘ e) : 𝓣.Tensor c ⊗[R] 𝓣.Tensor d →ₗ[R] R :=
  𝓣.contrAll' ∘ₗ (TensorProduct.congr (LinearEquiv.refl _ _)
    (𝓣.mapIso e.symm (by subst h; funext a; simp; rw [𝓣.τ_involutive]))).toLinearMap

lemma contrAll_symm_cond {e : X ≃ Y} (h : c = 𝓣.τ ∘ cY ∘ e) :
    cY = 𝓣.τ ∘ c ∘ ⇑e.symm := by
  subst h
  ext1 x
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  rw [𝓣.τ_involutive]

lemma contrAll_mapIso_right_cond {e : X ≃ Y} {e' : Z ≃ Y}
    (h : c = 𝓣.τ ∘ cY ∘ e) (h' : cZ = cY ∘ e') : c = 𝓣.τ ∘ cZ ∘ ⇑(e.trans e'.symm) := by
  subst h h'
  ext1 x
  simp only [Function.comp_apply, Equiv.coe_trans, Equiv.apply_symm_apply]

@[simp]
lemma contrAll_mapIso_right_tmul (e : X ≃ Y) (e' : Z ≃ Y)
    (h : c = 𝓣.τ ∘ cY ∘ e) (h' : cZ = cY ∘ e') (x : 𝓣.Tensor c) (z : 𝓣.Tensor cZ) :
    𝓣.contrAll e h (x ⊗ₜ[R] (𝓣.mapIso e' h' z)) =
    𝓣.contrAll (e.trans e'.symm) (𝓣.contrAll_mapIso_right_cond h h') (x ⊗ₜ[R] z) := by
  rw [contrAll, contrAll]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, congr_tmul,
    LinearEquiv.refl_apply, mapIso_mapIso]
  congr

@[simp]
lemma contrAll_comp_mapIso_right (e : X ≃ Y) (e' : Z ≃ Y)
    (h : c = 𝓣.τ ∘ cY ∘ e) (h' : cZ = cY ∘ e') : 𝓣.contrAll e h ∘ₗ
    (TensorProduct.congr (LinearEquiv.refl R (𝓣.Tensor c)) (𝓣.mapIso e' h')).toLinearMap
    = 𝓣.contrAll (e.trans e'.symm) (𝓣.contrAll_mapIso_right_cond h h') := by
  apply TensorProduct.ext'
  intro x y
  exact 𝓣.contrAll_mapIso_right_tmul e e' h h' x y

lemma contrAll_mapIso_left_cond {e : X ≃ Y} {e' : Z ≃ X}
    (h : c = 𝓣.τ ∘ cY ∘ e) (h' : cZ = c ∘ e') : cZ = 𝓣.τ ∘ cY ∘ ⇑(e'.trans e) := by
  subst h h'
  ext1 x
  simp only [Function.comp_apply, Equiv.coe_trans, Equiv.apply_symm_apply]

@[simp]
lemma contrAll_mapIso_left_tmul {e : X ≃ Y} {e' : Z ≃ X}
    (h : c = 𝓣.τ ∘ cY ∘ e) (h' : cZ = c ∘ e') (x : 𝓣.Tensor cZ) (y : 𝓣.Tensor cY) :
    𝓣.contrAll e h ((𝓣.mapIso e' h' x) ⊗ₜ[R] y) =
    𝓣.contrAll (e'.trans e) (𝓣.contrAll_mapIso_left_cond h h') (x ⊗ₜ[R] y) := by
  rw [contrAll, contrAll]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, congr_tmul,
    LinearEquiv.refl_apply, contrAll'_mapIso_tmul, mapIso_mapIso]
  congr

@[simp]
lemma contrAll_mapIso_left {e : X ≃ Y} {e' : Z ≃ X}
    (h : c = 𝓣.τ ∘ cY ∘ e) (h' : cZ = c ∘ e') :
    𝓣.contrAll e h ∘ₗ
    (TensorProduct.congr (𝓣.mapIso e' h') (LinearEquiv.refl R (𝓣.Tensor cY))).toLinearMap
    = 𝓣.contrAll (e'.trans e) (𝓣.contrAll_mapIso_left_cond h h') := by
  apply TensorProduct.ext'
  intro x y
  exact 𝓣.contrAll_mapIso_left_tmul h h' x y

end PreTensorStructure

/-! TODO: Add unit here. -/
/-- A `PreTensorStructure` with the additional constraint that `contrDua` is symmetric. -/
structure TensorStructure (R : Type) [CommSemiring R] extends PreTensorStructure R where
  /-- The symmetry condition on `contrDua`. -/
  contrDual_symm : ∀ μ,
    (contrDual μ) ∘ₗ (TensorProduct.comm R (ColorModule (τ μ)) (ColorModule μ)).toLinearMap =
    (contrDual (τ μ)) ∘ₗ (TensorProduct.congr (LinearEquiv.refl _ _)
    (toPreTensorStructure.colorModuleCast (by rw[toPreTensorStructure.τ_involutive]))).toLinearMap

namespace TensorStructure

open PreTensorStructure

variable (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  {c c₂ : X → 𝓣.Color} {d : Y → 𝓣.Color} {b : Z → 𝓣.Color} {d' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}

end TensorStructure

/-- A `TensorStructure` with a group action. -/
structure GroupTensorStructure (R : Type) [CommSemiring R]
    (G : Type) [Group G] extends TensorStructure R where
  /-- For each color `μ` a representation of `G` on `ColorModule μ`. -/
  repColorModule : (μ : Color) → Representation R G (ColorModule μ)
  /-- The contraction of a vector with its dual is invariant under the group action. -/
  contrDual_inv : ∀ μ g, contrDual μ ∘ₗ
    TensorProduct.map (repColorModule μ g) (repColorModule (τ μ) g) = contrDual μ

namespace GroupTensorStructure
open TensorStructure
open PreTensorStructure

variable {G : Type} [Group G]

variable (𝓣 : GroupTensorStructure R G)

variable {d : ℕ} {X Y Y' Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}

/-- The representation of the group `G` on the vector space of tensors. -/
def rep : Representation R G (𝓣.Tensor cX) where
  toFun g := PiTensorProduct.map (fun x => 𝓣.repColorModule (cX x) g)
  map_one' := by
    simp_all only [_root_.map_one, PiTensorProduct.map_one]
  map_mul' g g' := by
    simp_all only [_root_.map_mul]
    exact PiTensorProduct.map_mul _ _

local infixl:78 " • " => 𝓣.rep

lemma repColorModule_colorModuleCast_apply (h : μ = ν) (g : G) (x : 𝓣.ColorModule μ) :
    (𝓣.repColorModule ν g) ((𝓣.colorModuleCast h) x) =
    (𝓣.colorModuleCast h) ((𝓣.repColorModule μ g) x) := by
  subst h
  simp [colorModuleCast]

@[simp]
lemma repColorModule_colorModuleCast (h : μ = ν) (g : G) :
    (𝓣.repColorModule ν g) ∘ₗ (𝓣.colorModuleCast h).toLinearMap =
    (𝓣.colorModuleCast h).toLinearMap ∘ₗ (𝓣.repColorModule μ g) := by
  apply LinearMap.ext
  intro x
  simp [repColorModule_colorModuleCast_apply]

@[simp]
lemma rep_mapIso (e : X ≃ Y) (h : cX = cY ∘ e) (g : G) :
    (𝓣.rep g) ∘ₗ (𝓣.mapIso e h).toLinearMap = (𝓣.mapIso e h).toLinearMap ∘ₗ 𝓣.rep g := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  erw [mapIso_tprod]
  simp [rep, repColorModule_colorModuleCast_apply]
  change (PiTensorProduct.map fun x => (𝓣.repColorModule (cY x)) g)
    ((PiTensorProduct.tprod R) fun i => (𝓣.colorModuleCast _) (x (e.symm i))) =
    (𝓣.mapIso e h) ((PiTensorProduct.map _) ((PiTensorProduct.tprod R) x))
  rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
  rw [mapIso_tprod]
  apply congrArg
  funext i
  subst h
  simp [repColorModule_colorModuleCast_apply]

@[simp]
lemma rep_mapIso_apply (e : X ≃ Y) (h : cX = cY ∘ e) (g : G) (x : 𝓣.Tensor cX) :
    g • (𝓣.mapIso e h x) = (𝓣.mapIso e h) (g • x) := by
  trans ((𝓣.rep g) ∘ₗ (𝓣.mapIso e h).toLinearMap) x
  rfl
  simp

@[simp]
lemma rep_tprod (g : G) (f : (i : X) → 𝓣.ColorModule (cX i)) :
    g • (PiTensorProduct.tprod R f) = PiTensorProduct.tprod R (fun x =>
      𝓣.repColorModule (cX x) g (f x)) := by
  simp [rep]
  change (PiTensorProduct.map _) ((PiTensorProduct.tprod R) f) = _
  rw [PiTensorProduct.map_tprod]

/-!

## Group acting on tensor products

-/

lemma rep_tensoratorEquiv (g : G) :
    (𝓣.tensoratorEquiv cX cY) ∘ₗ (TensorProduct.map (𝓣.rep g) (𝓣.rep g)) = 𝓣.rep g ∘ₗ
    (𝓣.tensoratorEquiv cX cY).toLinearMap := by
  apply tensorProd_piTensorProd_ext
  intro p q
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, map_tmul, rep_tprod,
    tensoratorEquiv_tmul_tprod]
  apply congrArg
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

lemma rep_tensoratorEquiv_apply (g : G) (x : 𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY) :
    (𝓣.tensoratorEquiv cX cY) ((TensorProduct.map (𝓣.rep g) (𝓣.rep g)) x)
    = (𝓣.rep g) ((𝓣.tensoratorEquiv cX cY) x) := by
  trans ((𝓣.tensoratorEquiv cX cY) ∘ₗ (TensorProduct.map (𝓣.rep g) (𝓣.rep g))) x
  rfl
  rw [rep_tensoratorEquiv]
  rfl

lemma rep_tensoratorEquiv_tmul (g : G) (x : 𝓣.Tensor cX) (y : 𝓣.Tensor cY) :
    (𝓣.tensoratorEquiv cX cY) ((g • x) ⊗ₜ[R] (g • y)) =
    g • ((𝓣.tensoratorEquiv cX cY) (x ⊗ₜ[R] y)) := by
  nth_rewrite 1 [← rep_tensoratorEquiv_apply]
  rfl

/-!

## Group acting on contraction

-/

@[simp]
lemma contrAll_rep {c : X → 𝓣.Color} {d : Y → 𝓣.Color} (e : X ≃ Y) (h : c = 𝓣.τ ∘ d ∘ e) (g : G) :
    𝓣.contrAll e h ∘ₗ (TensorProduct.map (𝓣.rep g) (𝓣.rep g)) = 𝓣.contrAll e h := by
  apply TensorProduct.ext'
  refine fun x ↦ PiTensorProduct.induction_on' x ?_ (by
      intro a b hx hy y
      simp [map_add, add_tmul, hx, hy])
  intro rx fx
  refine fun y ↦ PiTensorProduct.induction_on' y ?_ (by
      intro a b hx hy
      simp at hx hy
      simp [map_add, tmul_add, hx, hy])
  intro ry fy
  simp [contrAll, TensorProduct.smul_tmul]
  apply congrArg
  apply congrArg
  simp [contrAll']
  apply congrArg
  simp [pairProd]
  change (PiTensorProduct.map _) ((PiTensorProduct.map₂ _ _) _) =
    (PiTensorProduct.map _) ((PiTensorProduct.map₂ _ _) _)
  rw [PiTensorProduct.map₂_tprod_tprod, PiTensorProduct.map₂_tprod_tprod, PiTensorProduct.map_tprod,
  PiTensorProduct.map_tprod]
  simp only [mk_apply]
  apply congrArg
  funext x
  rw [← repColorModule_colorModuleCast_apply]
  nth_rewrite 2 [← 𝓣.contrDual_inv (c x) g]
  rfl

@[simp]
lemma contrAll_rep_apply {c : X → 𝓣.Color} {d : Y → 𝓣.Color} (e : X ≃ Y) (h : c = 𝓣.τ ∘ d ∘ e)
    (g : G) (x : 𝓣.Tensor c ⊗ 𝓣.Tensor d) :
    𝓣.contrAll e h (TensorProduct.map (𝓣.rep g) (𝓣.rep g) x) = 𝓣.contrAll e h x := by
  change (𝓣.contrAll e h ∘ₗ (TensorProduct.map (𝓣.rep g) (𝓣.rep g))) x = _
  rw [contrAll_rep]

@[simp]
lemma contrAll_rep_tmul {c : X → 𝓣.Color} {d : Y → 𝓣.Color} (e : X ≃ Y) (h : c = 𝓣.τ ∘ d ∘ e)
    (g : G) (x : 𝓣.Tensor c) (y : 𝓣.Tensor d) :
    𝓣.contrAll e h ((g • x) ⊗ₜ[R] (g • y)) = 𝓣.contrAll e h (x ⊗ₜ[R] y) := by
  nth_rewrite 2 [← contrAll_rep_apply]
  rfl

end GroupTensorStructure

end
