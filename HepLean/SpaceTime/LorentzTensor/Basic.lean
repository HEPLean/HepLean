/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Logic.Function.CompTypeclasses
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
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
  ColorModule : Color → Type
  τ : Color → Color
  τ_involutive : Function.Involutive τ
  colorModule_addCommMonoid : ∀ μ, AddCommMonoid (ColorModule μ)
  colorModule_module : ∀ μ, Module R (ColorModule μ)
  contrDual : ∀ μ, ColorModule μ ⊗[R] ColorModule (τ μ) →ₗ[R] R

namespace PreTensorStructure


variable (𝓣 : PreTensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]  [Fintype W] [DecidableEq W]
  {c c₂ : X → 𝓣.Color}  {d : Y → 𝓣.Color} {b : Z → 𝓣.Color}
  {bw : W → 𝓣.Color} {d' : Y' → 𝓣.Color}  {μ ν: 𝓣.Color}

instance : AddCommMonoid (𝓣.ColorModule μ) := 𝓣.colorModule_addCommMonoid μ

instance : Module R (𝓣.ColorModule μ) := 𝓣.colorModule_module μ

def Tensor (c : X → 𝓣.Color): Type := ⨂[R] x, 𝓣.ColorModule (c x)

instance : AddCommMonoid (𝓣.Tensor c) :=
  PiTensorProduct.instAddCommMonoid fun i => 𝓣.ColorModule (c i)

instance : Module R (𝓣.Tensor c) := PiTensorProduct.instModule

def colorModuleCast (h : μ = ν) : 𝓣.ColorModule μ ≃ₗ[R] 𝓣.ColorModule ν where
  toFun x := Equiv.cast (congrArg 𝓣.ColorModule h) x
  invFun x := (Equiv.cast (congrArg 𝓣.ColorModule h)).symm x
  map_add' x y := by
    subst h
    rfl
  map_smul' x y := by
    subst h
    rfl
  left_inv x := by
    subst h
    rfl
  right_inv x := by
    subst h
    rfl

lemma tensorProd_piTensorProd_ext {M : Type} [AddCommMonoid M] [Module R M] {f g : 𝓣.Tensor c ⊗[R] 𝓣.Tensor d →ₗ[R] M}
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
  simp
  apply congrArg
  simp [TensorProduct.smul_tmul]
  apply congrArg
  exact h fx fy

/-!

## Mapping isomorphisms

-/

def mapIso {c : X → 𝓣.Color} {d : Y → 𝓣.Color} (e : X ≃ Y) (h : c = d ∘ e) :
    𝓣.Tensor c ≃ₗ[R] 𝓣.Tensor d :=
  (PiTensorProduct.reindex R _ e) ≪≫ₗ
  (PiTensorProduct.congr (fun y => 𝓣.colorModuleCast (by rw [h]; simp)))

lemma mapIso_trans_cond {e : X ≃ Y} {e' : Y ≃ Z} (h : c = d ∘ e) (h' : d = b ∘ e') :
    c = b ∘ (e.trans e') := by
  funext a
  subst h h'
  simp

@[simp]
lemma mapIso_trans (e : X ≃ Y) (e' : Y ≃ Z) (h : c = d ∘ e) (h' : d = b ∘ e') :
    (𝓣.mapIso e h ≪≫ₗ 𝓣.mapIso e' h') = 𝓣.mapIso (e.trans e') (𝓣.mapIso_trans_cond h h') := by
  refine LinearEquiv.toLinearMap_inj.mp ?_
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [mapIso, LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod, Equiv.symm_trans_apply]
  change (PiTensorProduct.congr fun y => 𝓣.colorModuleCast (_))
    ((PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (d x)) e')
    ((PiTensorProduct.congr fun y => 𝓣.colorModuleCast (_)) _)) =
    (PiTensorProduct.congr fun y => 𝓣.colorModuleCast _)
    ((PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (c x)) (e.trans e')) _)
  rw [PiTensorProduct.congr_tprod, PiTensorProduct.reindex_tprod,
    PiTensorProduct.congr_tprod, PiTensorProduct.reindex_tprod, PiTensorProduct.congr]
  simp [colorModuleCast]

@[simp]
lemma mapIso_mapIso (e : X ≃ Y) (e' : Y ≃ Z) (h : c = d ∘ e) (h' : d = b ∘ e')
    (T : 𝓣.Tensor c) :
    (𝓣.mapIso e' h') (𝓣.mapIso e h T) = 𝓣.mapIso (e.trans e') (𝓣.mapIso_trans_cond h h') T := by
  rw [← LinearEquiv.trans_apply, mapIso_trans]

@[simp]
lemma mapIso_symm (e : X ≃ Y) (h : c = d ∘ e) :
    (𝓣.mapIso e h).symm = 𝓣.mapIso e.symm ((Equiv.eq_comp_symm e d c).mpr h.symm) := by
  refine LinearEquiv.toLinearMap_inj.mp ?_
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp  [mapIso, LinearMap.compMultilinearMap_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, PiTensorProduct.reindex_tprod]
  change (PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (c x)) e).symm
    ((PiTensorProduct.congr fun y => 𝓣.colorModuleCast _).symm ((PiTensorProduct.tprod R) x)) =
  (PiTensorProduct.congr fun y => 𝓣.colorModuleCast _)
    ((PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (d x)) e.symm) ((PiTensorProduct.tprod R) x))
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
lemma mapIso_refl : 𝓣.mapIso (Equiv.refl X) (rfl : c = c) = LinearEquiv.refl R _ := by
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
lemma mapIso_tprod {c : X → 𝓣.Color} {d : Y → 𝓣.Color} (e : X ≃ Y) (h : c = d ∘ e) (f : (i : X) → 𝓣.ColorModule (c i)) :
    (𝓣.mapIso e h) (PiTensorProduct.tprod R f) =
    (PiTensorProduct.tprod R (fun i => 𝓣.colorModuleCast (by rw [h]; simp) (f (e.symm i)))) := by
  simp [mapIso]
  change (PiTensorProduct.congr fun y => 𝓣.colorModuleCast _)
    ((PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (c x)) e) ((PiTensorProduct.tprod R) f)) = _
  rw [PiTensorProduct.reindex_tprod]
  simp only [PiTensorProduct.congr_tprod]

/-!

## Pure tensors

This section is needed since: `PiTensorProduct.tmulEquiv` is not defined for dependent types.
Hence we need to construct a version of it here.

-/

abbrev PureTensor (c : X → 𝓣.Color) := (x : X) → 𝓣.ColorModule (c x)

def elimPureTensor (p : 𝓣.PureTensor c) (q : 𝓣.PureTensor d) : 𝓣.PureTensor (Sum.elim c d) :=
  fun x =>
    match x with
    | Sum.inl x => p x
    | Sum.inr x => q x

@[simp]
lemma elimPureTensor_update_right (p : 𝓣.PureTensor c) (q : 𝓣.PureTensor d)
    (y : Y) (r : 𝓣.ColorModule (d y)) : 𝓣.elimPureTensor p (Function.update q y r) =
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
lemma elimPureTensor_update_left (p : 𝓣.PureTensor c) (q : 𝓣.PureTensor d)
    (x : X) (r : 𝓣.ColorModule (c x)) : 𝓣.elimPureTensor (Function.update p x r) q =
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


def inlPureTensor (p : 𝓣.PureTensor (Sum.elim c d)) : 𝓣.PureTensor c := fun xy => p (Sum.inl xy)

def inrPureTensor (p : 𝓣.PureTensor (Sum.elim c d)) : 𝓣.PureTensor d := fun xy => p (Sum.inr xy)

@[simp]
lemma inlPureTensor_update_left [DecidableEq (X ⊕ Y)] (f : 𝓣.PureTensor (Sum.elim c d)) (x : X)
    (v1  : 𝓣.ColorModule (Sum.elim c d (Sum.inl x)))  :
    𝓣.inlPureTensor (Function.update f (Sum.inl x) v1) =Function.update (𝓣.inlPureTensor f) x v1 := by
  funext y
  simp [inlPureTensor, Function.update, Sum.inl.injEq, Sum.elim_inl]
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only

@[simp]
lemma inrPureTensor_update_left [DecidableEq (X ⊕ Y)] (f : 𝓣.PureTensor (Sum.elim c d)) (x : X)
    (v1  : 𝓣.ColorModule (Sum.elim c d (Sum.inl x)))  :
    𝓣.inrPureTensor (Function.update f (Sum.inl x) v1) = (𝓣.inrPureTensor f) := by
  funext x
  simp [inrPureTensor, Function.update]

@[simp]
lemma inrPureTensor_update_right [DecidableEq (X ⊕ Y)] (f : 𝓣.PureTensor (Sum.elim c d)) (y : Y)
    (v1  : 𝓣.ColorModule (Sum.elim c d (Sum.inr y)))  :
    𝓣.inrPureTensor (Function.update f (Sum.inr y) v1) =Function.update (𝓣.inrPureTensor f) y v1 := by
  funext y
  simp [inrPureTensor, Function.update, Sum.inl.injEq, Sum.elim_inl]
  split
  next h =>
    subst h
    simp_all only
  next h => simp_all only

@[simp]
lemma inlPureTensor_update_right [DecidableEq (X ⊕ Y)] (f : 𝓣.PureTensor (Sum.elim c d)) (y : Y)
    (v1  : 𝓣.ColorModule (Sum.elim c d (Sum.inr y)))  :
    𝓣.inlPureTensor (Function.update f (Sum.inr y) v1) = (𝓣.inlPureTensor f) := by
  funext x
  simp [inlPureTensor, Function.update]

def elimPureTensorMulLin : MultilinearMap R (fun i => 𝓣.ColorModule (c i))
    (MultilinearMap R (fun x => 𝓣.ColorModule (d x)) (𝓣.Tensor (Sum.elim c d))) where
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
def domCoprod : MultilinearMap R (fun x => 𝓣.ColorModule (Sum.elim c d x)) (𝓣.Tensor c ⊗[R] 𝓣.Tensor d) where
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

def tensoratorSymm : 𝓣.Tensor c ⊗[R] 𝓣.Tensor d →ₗ[R] 𝓣.Tensor (Sum.elim c d) := by
  refine TensorProduct.lift {
    toFun := fun a ↦
      PiTensorProduct.lift <|
          PiTensorProduct.lift (𝓣.elimPureTensorMulLin) a,
    map_add' := fun a b ↦ by simp
    map_smul' := fun r a ↦ by simp}

/-! TODO: Replace with dependent type version of `PiTensorProduct.tmulEquiv` when in Mathlib. -/
def tensorator : 𝓣.Tensor (Sum.elim c d) →ₗ[R] 𝓣.Tensor c ⊗[R] 𝓣.Tensor d :=
  PiTensorProduct.lift 𝓣.domCoprod

def tensoratorEquiv (c : X → 𝓣.Color) (d : Y → 𝓣.Color) : 𝓣.Tensor c ⊗[R] 𝓣.Tensor d ≃ₗ[R] 𝓣.Tensor (Sum.elim c d) :=
  LinearEquiv.ofLinear (𝓣.tensoratorSymm) (𝓣.tensorator)
  (by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro p
    simp [tensorator, tensoratorSymm, domCoprod]
    change (PiTensorProduct.lift (_)) ((PiTensorProduct.tprod R) _) =
      LinearMap.id ((PiTensorProduct.tprod R) p)
    rw [PiTensorProduct.lift.tprod]
    simp [elimPureTensorMulLin, elimPureTensor]
    change (PiTensorProduct.tprod R)  _ = _
    apply congrArg
    funext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl)
  (by
    apply tensorProd_piTensorProd_ext
    intro p q
    simp [tensorator,  tensoratorSymm]
    change (PiTensorProduct.lift 𝓣.domCoprod) ((PiTensorProduct.lift (𝓣.elimPureTensorMulLin p)) ((PiTensorProduct.tprod R) q)) =_
    rw [PiTensorProduct.lift.tprod]
    simp [elimPureTensorMulLin]
    rfl)

@[simp]
lemma tensoratorEquiv_tmul_tprod (p : 𝓣.PureTensor c) (q : 𝓣.PureTensor d) :
    (𝓣.tensoratorEquiv c d) ((PiTensorProduct.tprod R) p ⊗ₜ[R] (PiTensorProduct.tprod R) q) =
    (PiTensorProduct.tprod R) (𝓣.elimPureTensor p q) := by
  simp [tensoratorEquiv, tensorator, tensoratorSymm, domCoprod]
  change (PiTensorProduct.lift (𝓣.elimPureTensorMulLin p)) ((PiTensorProduct.tprod R) q) = _
  rw [PiTensorProduct.lift.tprod]
  simp [elimPureTensorMulLin]

lemma tensoratorEquiv_mapIso_cond {e : X ≃ Y} {e' : Z ≃ Y} {e'' : W ≃ X}
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = d ∘ e') (h'' : bW = c ∘ e'') :
    Sum.elim bW b = Sum.elim c d ∘ ⇑(e''.sumCongr e') := by
  subst h h' h''
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

@[simp]
lemma tensoratorEquiv_mapIso (e : X ≃ Y) (e' : Z ≃ Y) (e'' : W ≃ X)
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = d ∘ e') (h'' : bW = c ∘ e'') :
   (TensorProduct.congr (𝓣.mapIso e'' h'') (𝓣.mapIso e' h')) ≪≫ₗ (𝓣.tensoratorEquiv c d)
    = (𝓣.tensoratorEquiv bW b)
    ≪≫ₗ (𝓣.mapIso (Equiv.sumCongr e'' e') (𝓣.tensoratorEquiv_mapIso_cond h h' h'' )) := by
  apply LinearEquiv.toLinearMap_inj.mp
  apply tensorProd_piTensorProd_ext
  intro p q
  simp
  apply congrArg
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

@[simp]
lemma tensoratorEquiv_mapIso_apply (e : X ≃ Y) (e' : Z ≃ Y) (e'' : W ≃ X)
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = d ∘ e') (h'' : bW = c ∘ e'')
    (x : 𝓣.Tensor bW ⊗[R] 𝓣.Tensor b) :
    (𝓣.tensoratorEquiv c d) ((TensorProduct.congr (𝓣.mapIso e'' h'') (𝓣.mapIso e' h')) x) =
    (𝓣.mapIso (Equiv.sumCongr e'' e') (𝓣.tensoratorEquiv_mapIso_cond h h' h'' )) ((𝓣.tensoratorEquiv bW b) x) := by
  trans ((TensorProduct.congr (𝓣.mapIso e'' h'') (𝓣.mapIso e' h')) ≪≫ₗ (𝓣.tensoratorEquiv c d)) x
  rfl
  rw [tensoratorEquiv_mapIso]
  rfl
  exact e
  exact h

lemma tensoratorEquiv_mapIso_tmul (e : X ≃ Y) (e' : Z ≃ Y) (e'' : W ≃ X)
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = d ∘ e') (h'' : bW = c ∘ e'')
    (x : 𝓣.Tensor bW) (y :  𝓣.Tensor b) :
    (𝓣.tensoratorEquiv c d) ((𝓣.mapIso e'' h'' x) ⊗ₜ[R] (𝓣.mapIso e' h' y)) =
    (𝓣.mapIso (Equiv.sumCongr e'' e') (𝓣.tensoratorEquiv_mapIso_cond h h' h'' )) ((𝓣.tensoratorEquiv bW b) (x ⊗ₜ y)) := by
  rw [← tensoratorEquiv_mapIso_apply]
  rfl
  exact e
  exact h

/-!

## Splitting tensors into tensor products

-/

def decompEmbedSet (f : Y ↪ X) :
    X ≃ {x // x ∈ (Finset.image f Finset.univ)ᶜ} ⊕ Y :=
  (Equiv.Set.sumCompl (Set.range ⇑f)).symm.trans <|
  (Equiv.sumComm _ _).trans <|
  Equiv.sumCongr ((Equiv.subtypeEquivRight (by simp))) <|
  (Function.Embedding.toEquivRange f).symm

def decompEmbedColorLeft (c : X → 𝓣.Color)  (f : Y ↪ X) : {x // x ∈ (Finset.image f Finset.univ)ᶜ} → 𝓣.Color :=
  (c ∘ (decompEmbedSet f).symm) ∘ Sum.inl

def decompEmbedColorRight  (c : X → 𝓣.Color)  (f : Y ↪ X) : Y → 𝓣.Color :=
  (c ∘ (decompEmbedSet f).symm) ∘ Sum.inr

lemma decompEmbed_cond  (c : X → 𝓣.Color)  (f : Y ↪ X) : c =
    (Sum.elim (𝓣.decompEmbedColorLeft c f) (𝓣.decompEmbedColorRight c f)) ∘ decompEmbedSet f  := by
  simpa [decompEmbedColorLeft, decompEmbedColorRight] using (Equiv.comp_symm_eq _ _ _).mp rfl

/-- Decomposes a tensor into a tensor product based on an embedding. -/
def decompEmbed (f : Y ↪ X) :
    𝓣.Tensor c ≃ₗ[R] 𝓣.Tensor (𝓣.decompEmbedColorLeft c f) ⊗[R] 𝓣.Tensor (c ∘ f) :=
  (𝓣.mapIso (decompEmbedSet f) (𝓣.decompEmbed_cond c f)) ≪≫ₗ
  (𝓣.tensoratorEquiv (𝓣.decompEmbedColorLeft c f) (𝓣.decompEmbedColorRight c f)).symm


/-!

## Contraction

-/

def pairProd : 𝓣.Tensor c ⊗[R] 𝓣.Tensor c₂ →ₗ[R]
    ⨂[R] x, 𝓣.ColorModule (c x) ⊗[R] 𝓣.ColorModule (c₂ x) :=
  TensorProduct.lift (
    PiTensorProduct.map₂ (fun x =>
      TensorProduct.mk R (𝓣.ColorModule (c x)) (𝓣.ColorModule (c₂ x)) ))

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

def contrAll' : 𝓣.Tensor c ⊗[R] 𝓣.Tensor (𝓣.τ ∘ c) →ₗ[R] R :=
  (PiTensorProduct.lift (MultilinearMap.mkPiAlgebra R X R)) ∘ₗ
  (PiTensorProduct.map (fun x => 𝓣.contrDual (c x))) ∘ₗ
  (𝓣.pairProd)

lemma contrAll'_mapIso_cond {e : X ≃ Y} (h : c = d ∘ e) :
   𝓣.τ ∘ d = (𝓣.τ ∘ c) ∘ ⇑e.symm := by
  subst h
  ext1 x
  simp

@[simp]
lemma contrAll'_mapIso (e : X ≃ Y) (h : c = d ∘ e) :
  𝓣.contrAll' ∘ₗ
    (TensorProduct.congr (𝓣.mapIso e h) (LinearEquiv.refl R _)).toLinearMap =
  𝓣.contrAll' ∘ₗ  (TensorProduct.congr (LinearEquiv.refl R _)
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
  simp
  apply congrArg
  rw [← LinearEquiv.symm_apply_eq]
  rw [PiTensorProduct.reindex_symm]
  rw [← PiTensorProduct.map_reindex]
  subst h
  simp
  apply congrArg
  rw [pairProd, pairProd]
  simp
  apply congrArg
  change _ = ((PiTensorProduct.map₂ fun x => TensorProduct.mk R (𝓣.ColorModule (d (e x))) (𝓣.ColorModule (𝓣.τ (d (e x)))))
      ((PiTensorProduct.tprod R) fx))
    ((𝓣.mapIso e.symm _) ((PiTensorProduct.tprod R) fy))
  rw [mapIso_tprod]
  simp
  rw [PiTensorProduct.map₂_tprod_tprod]
  change (PiTensorProduct.reindex R (fun x => 𝓣.ColorModule (d x) ⊗[R] 𝓣.ColorModule (𝓣.τ (d x))) e.symm)
    (((PiTensorProduct.map₂ fun x => TensorProduct.mk R (𝓣.ColorModule (d x)) (𝓣.ColorModule (𝓣.τ (d x))))
        ((PiTensorProduct.tprod R) fun i => (𝓣.colorModuleCast _) (fx (e.symm i))))
      ((PiTensorProduct.tprod R) fy)) = _
  rw [PiTensorProduct.map₂_tprod_tprod]
  simp
  erw [PiTensorProduct.reindex_tprod]
  apply congrArg
  funext i
  simp
  congr
  simp [colorModuleCast]
  apply cast_eq_iff_heq.mpr
  rw [Equiv.symm_apply_apply]

@[simp]
lemma contrAll'_mapIso_tmul (e : X ≃ Y) (h : c = d ∘ e) (x : 𝓣.Tensor c) (y : 𝓣.Tensor (𝓣.τ ∘ d)) :
  𝓣.contrAll' ((𝓣.mapIso e h) x ⊗ₜ[R] y) = 𝓣.contrAll' (x ⊗ₜ[R] (𝓣.mapIso e.symm (𝓣.contrAll'_mapIso_cond h) y)) := by
  change  (𝓣.contrAll' ∘ₗ
    (TensorProduct.congr (𝓣.mapIso e h) (LinearEquiv.refl R _)).toLinearMap) (x ⊗ₜ[R] y) = _
  rw [contrAll'_mapIso]
  rfl

def contrAll {c : X → 𝓣.Color} {d : Y → 𝓣.Color}
    (e : X ≃ Y) (h : c = 𝓣.τ ∘ d ∘ e) : 𝓣.Tensor c ⊗[R] 𝓣.Tensor d →ₗ[R] R :=
  𝓣.contrAll' ∘ₗ (TensorProduct.congr (LinearEquiv.refl _ _)
    (𝓣.mapIso e.symm (by subst h; funext a; simp; rw [𝓣.τ_involutive]))).toLinearMap

lemma contrAll_symm_cond {e : X ≃ Y} (h : c = 𝓣.τ ∘ d ∘ e) :
    d = 𝓣.τ ∘ c ∘ ⇑e.symm := by
  subst h
  ext1 x
  simp
  rw [𝓣.τ_involutive]

lemma contrAll_mapIso_right_cond {e : X ≃ Y} {e' : Z ≃ Y}
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = d ∘ e') : c = 𝓣.τ ∘ b ∘ ⇑(e.trans e'.symm) := by
  subst h h'
  ext1 x
  simp only [Function.comp_apply, Equiv.coe_trans, Equiv.apply_symm_apply]

@[simp]
lemma contrAll_mapIso_right_tmul (e : X ≃ Y) (e' : Z ≃ Y)
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = d ∘ e')  (x : 𝓣.Tensor c) (z : 𝓣.Tensor b) :
    𝓣.contrAll e h (x ⊗ₜ[R] (𝓣.mapIso e' h' z)) =
    𝓣.contrAll (e.trans e'.symm) (𝓣.contrAll_mapIso_right_cond h h') (x ⊗ₜ[R] z) := by
  rw [contrAll, contrAll]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, congr_tmul,
    LinearEquiv.refl_apply, mapIso_mapIso]
  congr

@[simp]
lemma contrAll_comp_mapIso_right (e : X ≃ Y) (e' : Z ≃ Y)
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = d ∘ e')  : 𝓣.contrAll e h ∘ₗ
    (TensorProduct.congr (LinearEquiv.refl R (𝓣.Tensor c)) (𝓣.mapIso e' h')).toLinearMap
    = 𝓣.contrAll (e.trans e'.symm) (𝓣.contrAll_mapIso_right_cond h h') := by
  apply TensorProduct.ext'
  intro x y
  exact 𝓣.contrAll_mapIso_right_tmul e e' h h' x y

lemma contrAll_mapIso_left_cond {e : X ≃ Y} {e' : Z ≃ X}
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = c ∘ e') : b = 𝓣.τ ∘ d ∘ ⇑(e'.trans e) := by
  subst h h'
  ext1 x
  simp only [Function.comp_apply, Equiv.coe_trans, Equiv.apply_symm_apply]

@[simp]
lemma contrAll_mapIso_left_tmul {e : X ≃ Y} {e' : Z ≃ X}
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = c ∘ e') (x :  𝓣.Tensor b) (y : 𝓣.Tensor d) :
    𝓣.contrAll e h ((𝓣.mapIso e' h' x) ⊗ₜ[R] y) =
    𝓣.contrAll (e'.trans e) (𝓣.contrAll_mapIso_left_cond h h') (x ⊗ₜ[R] y) := by
  rw [contrAll, contrAll]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, congr_tmul,
    LinearEquiv.refl_apply, contrAll'_mapIso_tmul, mapIso_mapIso]
  congr

@[simp]
lemma contrAll_mapIso_left {e : X ≃ Y} {e' : Z ≃ X}
    (h : c = 𝓣.τ ∘ d ∘ e) (h' : b = c ∘ e') :
    𝓣.contrAll e h ∘ₗ
    (TensorProduct.congr (𝓣.mapIso e' h') (LinearEquiv.refl R (𝓣.Tensor d))).toLinearMap
    = 𝓣.contrAll (e'.trans e) (𝓣.contrAll_mapIso_left_cond h h') := by
  apply TensorProduct.ext'
  intro x y
  exact 𝓣.contrAll_mapIso_left_tmul h h' x y

end PreTensorStructure

structure TensorStructure (R : Type) [CommSemiring R] extends PreTensorStructure R where
  contrDual_symm : ∀ μ,
    (contrDual μ) ∘ₗ (TensorProduct.comm R (ColorModule (τ μ)) (ColorModule μ)).toLinearMap  =
    (contrDual (τ μ)) ∘ₗ (TensorProduct.congr (LinearEquiv.refl _ _)
    (toPreTensorStructure.colorModuleCast (by rw[toPreTensorStructure.τ_involutive]))).toLinearMap

namespace TensorStructure

open PreTensorStructure

variable (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  {c c₂ : X → 𝓣.Color}  {d : Y → 𝓣.Color} {b : Z → 𝓣.Color}  {d' : Y' → 𝓣.Color}  {μ ν: 𝓣.Color}


end TensorStructure

structure GroupTensorStructure (R : Type) [CommSemiring R]
    (G : Type) [Group G] extends TensorStructure R where
  repColorModule : (μ : Color) → Representation R G (ColorModule μ)
  contrDual_inv : ∀ μ g, contrDual μ ∘ₗ
    TensorProduct.map (repColorModule μ g) (repColorModule (τ μ) g) = contrDual μ

namespace GroupTensorStructure
open TensorStructure
open PreTensorStructure

variable {G : Type} [Group G]

variable (𝓣 : GroupTensorStructure R G)

variable {d : ℕ} {X Y Y' Z : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z]
  {c c₂ : X → 𝓣.Color}  {d : Y → 𝓣.Color} {b : Z → 𝓣.Color}  {d' : Y' → 𝓣.Color}  {μ ν: 𝓣.Color}


def rep : Representation R G (𝓣.Tensor c) where
  toFun g := PiTensorProduct.map (fun x => 𝓣.repColorModule (c x) g)
  map_one' := by
    simp_all only [_root_.map_one, PiTensorProduct.map_one]
  map_mul' g g' := by
    simp_all only [_root_.map_mul]
    exact PiTensorProduct.map_mul _ _

local infixl:78 " • " => 𝓣.rep

lemma repColorModule_colorModuleCast_apply (h : μ = ν) (g : G) (x : 𝓣.ColorModule μ) :
    (𝓣.repColorModule ν g) ((𝓣.colorModuleCast h) x) = (𝓣.colorModuleCast h) ((𝓣.repColorModule μ g) x) := by
  subst h
  simp [colorModuleCast]

@[simp]
lemma repColorModule_colorModuleCast (h : μ = ν) (g : G) :
    (𝓣.repColorModule ν g) ∘ₗ (𝓣.colorModuleCast h).toLinearMap =
    (𝓣.colorModuleCast h).toLinearMap  ∘ₗ (𝓣.repColorModule μ g) := by
  apply LinearMap.ext
  intro x
  simp [repColorModule_colorModuleCast_apply]


@[simp]
lemma rep_mapIso (e : X ≃ Y) (h : c = d ∘ e) (g : G) :
    (𝓣.rep g) ∘ₗ (𝓣.mapIso e h).toLinearMap = (𝓣.mapIso e h).toLinearMap ∘ₗ 𝓣.rep g := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp
  erw [mapIso_tprod]
  simp [rep, repColorModule_colorModuleCast_apply]
  change (PiTensorProduct.map fun x => (𝓣.repColorModule (d x)) g)
    ((PiTensorProduct.tprod R) fun i => (𝓣.colorModuleCast _) (x (e.symm i))) =
    (𝓣.mapIso e h) ((PiTensorProduct.map fun x => (𝓣.repColorModule (c x)) g) ((PiTensorProduct.tprod R) x))
  rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
  rw [mapIso_tprod]
  apply congrArg
  funext i
  subst h
  simp [repColorModule_colorModuleCast_apply]

@[simp]
lemma rep_mapIso_apply (e : X ≃ Y) (h : c = d ∘ e) (g : G) (x : 𝓣.Tensor c) :
    g • (𝓣.mapIso e h x) = (𝓣.mapIso e h) (g • x) := by
  trans ((𝓣.rep g) ∘ₗ (𝓣.mapIso e h).toLinearMap) x
  rfl
  simp

@[simp]
lemma rep_tprod (g : G) (f : (i : X) → 𝓣.ColorModule (c i)) :
    g • (PiTensorProduct.tprod R f) = PiTensorProduct.tprod R (fun x =>
      𝓣.repColorModule (c x) g (f x)) := by
  simp [rep]
  change (PiTensorProduct.map fun x => (𝓣.repColorModule (c x)) g) ((PiTensorProduct.tprod R) f) = _
  rw [PiTensorProduct.map_tprod]

/-!

## Group acting on tensor products

-/

lemma rep_tensoratorEquiv (g : G) :
    (𝓣.tensoratorEquiv c d) ∘ₗ (TensorProduct.map (𝓣.rep g)  (𝓣.rep g)) = 𝓣.rep g ∘ₗ
    (𝓣.tensoratorEquiv c d).toLinearMap := by
  apply tensorProd_piTensorProd_ext
  intro p q
  simp
  apply congrArg
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

lemma rep_tensoratorEquiv_apply (g : G) (x : 𝓣.Tensor c ⊗[R] 𝓣.Tensor d) :
    (𝓣.tensoratorEquiv c d) ((TensorProduct.map (𝓣.rep g) (𝓣.rep g)) x) = (𝓣.rep g) ((𝓣.tensoratorEquiv c d) x) := by
  trans ((𝓣.tensoratorEquiv c d) ∘ₗ (TensorProduct.map (𝓣.rep g) (𝓣.rep g))) x
  rfl
  rw [rep_tensoratorEquiv]
  rfl

lemma rep_tensoratorEquiv_tmul (g : G) (x : 𝓣.Tensor c) (y : 𝓣.Tensor d) :
    (𝓣.tensoratorEquiv c d) ((g • x) ⊗ₜ[R] (g • y)) = g • ((𝓣.tensoratorEquiv c d) (x ⊗ₜ[R] y)) := by
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
  change (PiTensorProduct.map _) ((PiTensorProduct.map₂ _ _) _)  =
    (PiTensorProduct.map _) ((PiTensorProduct.map₂ _ _) _)
  rw [PiTensorProduct.map₂_tprod_tprod, PiTensorProduct.map₂_tprod_tprod, PiTensorProduct.map_tprod,
  PiTensorProduct.map_tprod]
  simp
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
