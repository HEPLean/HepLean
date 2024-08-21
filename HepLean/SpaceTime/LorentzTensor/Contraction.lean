/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.MulActionTensor
/-!

# Contraction of indices

We define a number of ways to contract indices of tensors:

- `contrDualLeft`: Contracts vectors on the left as:
  `𝓣.ColorModule ν ⊗[R] 𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η →ₗ[R] 𝓣.ColorModule η`

- `contrDualMid`: Contracts vectors in the middle as:
  `(𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule ν) ⊗[R] (𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η) →ₗ[R]`
  `𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule η`

- `contrAll'`: Contracts all indices of manifestly tensors with manifestly dual colors as:
  `𝓣.Tensor cX ⊗[R] 𝓣.Tensor (𝓣.τ ∘ cX) →ₗ[R] R`

- `contrAll`: Contracts all indices of tensors with dual colors as:
  `𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY →ₗ[R] R`

- `contrAllLeft`: Contracts all indices of tensors on the left as:
  `𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY ⊗[R] 𝓣.Tensor cZ →ₗ[R] 𝓣.Tensor cZ`

- `contrElim`: Contracting indices of tensors indexed by `Sum.elim _ _` as:
  `𝓣.Tensor (Sum.elim cW cX) ⊗[R] 𝓣.Tensor (Sum.elim cY cZ) →ₗ[R] 𝓣.Tensor (Sum.elim cW cZ)`

-/

noncomputable section

open TensorProduct
open MulActionTensor

variable {R : Type} [CommSemiring R]

namespace TensorColor

variable {d : ℕ} {X X' Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
variable {d : ℕ} {X Y Y' Z W C P : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]

namespace ColorMap

variable {𝓒 : TensorColor} [Fintype 𝓒.Color] [DecidableEq 𝓒.Color]

variable (cX : ColorMap 𝓒 X) (cY : ColorMap 𝓒 Y) (cZ : ColorMap 𝓒 Z)

/-- Given an equivalence `e` of types the condition that the color map `cX` is the dual to `cY`
  up to this equivalence. -/
def ContrAll (e : X ≃ Y) (cX : ColorMap 𝓒 X) (cY : ColorMap 𝓒 Y) : Prop :=
  cX = 𝓒.τ ∘ cY ∘ e

namespace ContrAll

variable {e : X ≃ Y} {e' : Y ≃ Z} {cX : ColorMap 𝓒 X} {cY : ColorMap 𝓒 Y} {cZ : ColorMap 𝓒 Z}
variable {cX' : ColorMap 𝓒 X'} {cY' : ColorMap 𝓒 Y'}

lemma toMapIso (h : cX.ContrAll e cY) : cX.MapIso e cY.dual := by
  subst h
  rfl

lemma symm (h : cX.ContrAll e cY) : cY.ContrAll e.symm cX := by
  subst h
  funext x
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  exact (𝓒.τ_involutive (cY x)).symm

lemma trans_mapIso {e : X ≃ Y} {e' : Z ≃ Y}
    (h : cX.ContrAll e cY) (h' : cZ.MapIso e' cY) : cX.ContrAll (e.trans e'.symm) cZ := by
  subst h h'
  funext x
  simp only [Function.comp_apply, Equiv.coe_trans, Equiv.apply_symm_apply]

lemma mapIso_trans {e : X ≃ Y} {e' : Z ≃ X}
    (h : cX.ContrAll e cY) (h' : cZ.MapIso e' cX) : cZ.ContrAll (e'.trans e) cY := by
  subst h h'
  funext x
  simp only [Function.comp_apply, Equiv.coe_trans, Equiv.apply_symm_apply]

end ContrAll

/-- Given an equivalence `(C ⊕ C) ⊕ P ≃ X` the restriction of a color map `cX` on to `P`. -/
def contr (e : (C ⊕ C) ⊕ P ≃ X) (cX : ColorMap 𝓒 X) : ColorMap 𝓒 P :=
  cX ∘ e ∘ Sum.inr

/-- Given an equivalence `(C ⊕ C) ⊕ P ≃ X` the restriction of a color map `cX` on `X`
  to the first `C`. -/
def contrLeft (e : (C ⊕ C) ⊕ P ≃ X) (cX : ColorMap 𝓒 X) : ColorMap 𝓒 C :=
  cX ∘ e ∘ Sum.inl ∘ Sum.inl

/-- Given an equivalence `(C ⊕ C) ⊕ P ≃ X` the restriction of a color map `cX` on `X`
  to the second `C`. -/
def contrRight (e : (C ⊕ C) ⊕ P ≃ X) (cX : ColorMap 𝓒 X) : ColorMap 𝓒 C :=
  cX ∘ e ∘ Sum.inl ∘ Sum.inr

/-- Given an equivalence `(C ⊕ C) ⊕ P ≃ X` the condition on `cX` so that we contract
  the indices of the `C`'s under this equivalence. -/
def ContrCond (e : (C ⊕ C) ⊕ P ≃ X) (cX : ColorMap 𝓒 X) : Prop :=
    cX ∘ e ∘ Sum.inl ∘ Sum.inl = 𝓒.τ ∘ cX ∘ e ∘ Sum.inl ∘ Sum.inr

namespace ContrCond

variable {e : (C ⊕ C) ⊕ P ≃ X} {e' : Y ≃ Z} {cX : ColorMap 𝓒 X} {cY : ColorMap 𝓒 Y}
  {cZ : ColorMap 𝓒 Z}

variable {cX' : ColorMap 𝓒 X'} {cY' : ColorMap 𝓒 Y'}

lemma to_contrAll (h : cX.ContrCond e) :
    (cX.contrLeft e).ContrAll (Equiv.refl _) (cX.contrRight e) := h

end ContrCond

end ColorMap

end TensorColor

namespace TensorStructure

variable (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W C P : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]
  {cX cX2 : 𝓣.ColorMap X} {cY : 𝓣.ColorMap Y} {cZ : 𝓣.ColorMap Z}
  {cW : 𝓣.ColorMap W} {cY' : 𝓣.ColorMap Y'} {μ ν: 𝓣.Color}

variable {G H : Type} [Group G] [Group H] [MulActionTensor G 𝓣]
local infixl:101 " • " => 𝓣.rep
/-!

# Contractions of vectors

-/

/-- The contraction of a vector in `𝓣.ColorModule ν` with a vector in
  `𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η` to form a vector in `𝓣.ColorModule η`. -/
def contrDualLeft {ν η : 𝓣.Color} :
    𝓣.ColorModule ν ⊗[R] 𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η →ₗ[R] 𝓣.ColorModule η :=
  contrLeftAux (𝓣.contrDual ν)

/-- The contraction of a vector in `𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule ν` with a vector in
  `𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η` to form a vector in
  `𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule η`. -/
def contrDualMid {μ ν η : 𝓣.Color} :
    (𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule ν) ⊗[R] (𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η) →ₗ[R]
      𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule η :=
  contrMidAux (𝓣.contrDual ν)

/-- A linear map taking tensors mapped with the same index set to the product of paired tensors. -/
def pairProd : 𝓣.Tensor cX ⊗[R] 𝓣.Tensor cX2 →ₗ[R]
    ⨂[R] x, 𝓣.ColorModule (cX x) ⊗[R] 𝓣.ColorModule (cX2 x) :=
  TensorProduct.lift (
    PiTensorProduct.map₂ (fun x =>
      TensorProduct.mk R (𝓣.ColorModule (cX x)) (𝓣.ColorModule (cX2 x))))

lemma pairProd_tmul_tprod_tprod (fx : (i : X) → 𝓣.ColorModule (cX i))
    (fx2 : (i : X) → 𝓣.ColorModule (cX2 i)) :
    𝓣.pairProd (PiTensorProduct.tprod R fx ⊗ₜ[R] PiTensorProduct.tprod R fx2) =
    PiTensorProduct.tprod R (fun x => fx x ⊗ₜ[R] fx2 x) := by
  simp [pairProd]
  erw [PiTensorProduct.map₂_tprod_tprod]
  rfl

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

lemma contrAll'_tmul_tprod_tprod (fx : (i : X) → 𝓣.ColorModule (cX i))
    (fy : (i : X) → 𝓣.ColorModule (𝓣.τ (cX i))) :
    𝓣.contrAll' (PiTensorProduct.tprod R fx ⊗ₜ[R] PiTensorProduct.tprod R fy) =
    (PiTensorProduct.lift (MultilinearMap.mkPiAlgebra R X R))
    (PiTensorProduct.tprod R (fun x => 𝓣.contrDual (cX x) (fx x ⊗ₜ[R] fy x))) := by
  simp only [contrAll', Function.comp_apply, LinearMap.coe_comp, PiTensorProduct.lift.tprod,
    MultilinearMap.mkPiAlgebra_apply]
  erw [pairProd_tmul_tprod_tprod]
  simp only [Function.comp_apply, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod,
    MultilinearMap.mkPiAlgebra_apply]

@[simp]
lemma contrAll'_isEmpty_tmul [IsEmpty X] (x : 𝓣.Tensor cX) (y : 𝓣.Tensor (𝓣.τ ∘ cX)) :
    𝓣.contrAll' (x ⊗ₜ y) = 𝓣.isEmptyEquiv x * 𝓣.isEmptyEquiv y := by
  refine PiTensorProduct.induction_on' x ?_ (by
    intro a b hx hy
    simp [map_add, add_tmul, add_mul, hx, hy])
  intro rx fx
  refine PiTensorProduct.induction_on' y ?_ (by
      intro a b hx hy
      simp at hx hy
      simp [map_add, tmul_add, mul_add, hx, hy])
  intro ry fy
  simp [smul_tmul]
  ring_nf
  rw [mul_assoc, mul_assoc]
  apply congrArg
  apply congrArg
  simp [contrAll']
  erw [pairProd_tmul_tprod_tprod]
  simp only [Function.comp_apply, PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod,
    MultilinearMap.mkPiAlgebra_apply, Finset.univ_eq_empty, Finset.prod_empty]
  erw [isEmptyEquiv_tprod]

@[simp]
lemma contrAll'_mapIso (e : X ≃ Y) (h : cX.MapIso e cY) :
    𝓣.contrAll' ∘ₗ
      (TensorProduct.congr (𝓣.mapIso e h) (LinearEquiv.refl R _)).toLinearMap =
    𝓣.contrAll' ∘ₗ (TensorProduct.congr (LinearEquiv.refl R _)
      (𝓣.mapIso e.symm h.symm.dual)).toLinearMap := by
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
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, Function.comp_apply, tmul_smul,
    LinearMapClass.map_smul, LinearMap.coe_comp, LinearEquiv.coe_coe, congr_tmul, mapIso_tprod,
    LinearEquiv.refl_apply, smul_eq_mul, smul_tmul]
  apply congrArg
  apply congrArg
  erw [contrAll'_tmul_tprod_tprod]
  erw [TensorProduct.congr_tmul]
  simp only [PiTensorProduct.lift.tprod, LinearEquiv.refl_apply]
  erw [mapIso_tprod]
  erw [contrAll'_tmul_tprod_tprod]
  rw [mkPiAlgebra_equiv e]
  simp only [Equiv.symm_symm_apply, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, PiTensorProduct.reindex_tprod,
    PiTensorProduct.lift.tprod]
  apply congrArg
  funext y
  rw [𝓣.contrDual_cast (congrFun h.symm y)]
  apply congrArg
  congr 1
  · simp [colorModuleCast]
  · symm
    apply cast_eq_iff_heq.mpr
    simp [colorModuleCast, Equiv.apply_symm_apply]
    rw [Equiv.apply_symm_apply]
    exact HEq.symm (cast_heq _ _)

@[simp]
lemma contrAll'_mapIso_tmul (e : X ≃ Y) (h : cX.MapIso e cY) (x : 𝓣.Tensor cX)
    (y : 𝓣.Tensor (𝓣.τ ∘ cY)) : 𝓣.contrAll' ((𝓣.mapIso e h) x ⊗ₜ[R] y) =
    𝓣.contrAll' (x ⊗ₜ[R] (𝓣.mapIso e.symm h.symm.dual y)) := by
  change (𝓣.contrAll' ∘ₗ
    (TensorProduct.congr (𝓣.mapIso e h) (LinearEquiv.refl R _)).toLinearMap) (x ⊗ₜ[R] y) = _
  rw [contrAll'_mapIso]
  rfl

/-- The contraction of all the indices of two tensors with dual colors. -/
def contrAll (e : X ≃ Y) (h : cX.ContrAll e cY) : 𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY →ₗ[R] R :=
  𝓣.contrAll' ∘ₗ (TensorProduct.congr (LinearEquiv.refl _ _)
    (𝓣.mapIso e.symm h.symm.toMapIso)).toLinearMap

lemma contrAll_tmul (e : X ≃ Y) (h : cX.ContrAll e cY) (x : 𝓣.Tensor cX) (y : 𝓣.Tensor cY) :
    𝓣.contrAll e h (x ⊗ₜ[R] y) = 𝓣.contrAll' (x ⊗ₜ[R] ((𝓣.mapIso e.symm h.symm.toMapIso) y)) := by
  rw [contrAll]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rfl

@[simp]
lemma contrAll_mapIso_right_tmul (e : X ≃ Y) (e' : Z ≃ Y)
    (h : c.ContrAll e cY) (h' : cZ.MapIso e' cY) (x : 𝓣.Tensor c) (z : 𝓣.Tensor cZ) :
    𝓣.contrAll e h (x ⊗ₜ[R] 𝓣.mapIso e' h' z) =
    𝓣.contrAll (e.trans e'.symm) (h.trans_mapIso h') (x ⊗ₜ[R] z) := by
  simp only [contrAll_tmul, mapIso_mapIso]
  apply congrArg
  rfl

@[simp]
lemma contrAll_comp_mapIso_right (e : X ≃ Y) (e' : Z ≃ Y)
    (h : c.ContrAll e cY) (h' : cZ.MapIso e' cY) : 𝓣.contrAll e h ∘ₗ
    (TensorProduct.congr (LinearEquiv.refl R (𝓣.Tensor c)) (𝓣.mapIso e' h')).toLinearMap
    = 𝓣.contrAll (e.trans e'.symm) (h.trans_mapIso h') := by
  apply TensorProduct.ext'
  intro x y
  exact 𝓣.contrAll_mapIso_right_tmul e e' h h' x y

@[simp]
lemma contrAll_mapIso_left_tmul {e : X ≃ Y} {e' : Z ≃ X}
    (h : cX.ContrAll e cY) (h' : cZ.MapIso e' cX) (x : 𝓣.Tensor cZ) (y : 𝓣.Tensor cY) :
    𝓣.contrAll e h (𝓣.mapIso e' h' x ⊗ₜ[R] y) =
    𝓣.contrAll (e'.trans e) (h.mapIso_trans h') (x ⊗ₜ[R] y) := by
  simp only [contrAll_tmul, contrAll'_mapIso_tmul, mapIso_mapIso]
  rfl

@[simp]
lemma contrAll_mapIso_left {e : X ≃ Y} {e' : Z ≃ X}
    (h : cX.ContrAll e cY) (h' : cZ.MapIso e' cX) :
    𝓣.contrAll e h ∘ₗ
    (TensorProduct.congr (𝓣.mapIso e' h') (LinearEquiv.refl R (𝓣.Tensor cY))).toLinearMap
    = 𝓣.contrAll (e'.trans e) (h.mapIso_trans h') := by
  apply TensorProduct.ext'
  intro x y
  exact 𝓣.contrAll_mapIso_left_tmul h h' x y

/-- The linear map from `𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY ⊗[R] 𝓣.Tensor cZ` to
  `𝓣.Tensor cZ` obtained by contracting all indices in `𝓣.Tensor cX` and `𝓣.Tensor cY`,
  given a proof that this is possible. -/
def contrAllLeft (e : X ≃ Y) (h : cX.ContrAll e cY) :
    𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY ⊗[R] 𝓣.Tensor cZ →ₗ[R] 𝓣.Tensor cZ :=
  (TensorProduct.lid R _).toLinearMap ∘ₗ
  TensorProduct.map (𝓣.contrAll e h) (LinearEquiv.refl R (𝓣.Tensor cZ)).toLinearMap
  ∘ₗ (TensorProduct.assoc R _ _ _).symm.toLinearMap

/-- The linear map from `(𝓣.Tensor cW ⊗[R] 𝓣.Tensor cX) ⊗[R] (𝓣.Tensor cY ⊗[R] 𝓣.Tensor cZ)`
  to `𝓣.Tensor cW ⊗[R] 𝓣.Tensor cZ` obtained by contracting all indices of the tensors
  in the middle. -/
def contrAllMid (e : X ≃ Y) (h : cX.ContrAll e cY) :
    (𝓣.Tensor cW ⊗[R] 𝓣.Tensor cX) ⊗[R] (𝓣.Tensor cY ⊗[R] 𝓣.Tensor cZ) →ₗ[R]
    𝓣.Tensor cW ⊗[R] 𝓣.Tensor cZ :=
  (TensorProduct.map (LinearEquiv.refl R _).toLinearMap (𝓣.contrAllLeft e h)) ∘ₗ
  (TensorProduct.assoc R _ _ _).toLinearMap

/-- The linear map from `𝓣.Tensor (Sum.elim cW cX) ⊗[R] 𝓣.Tensor (Sum.elim cY cZ)`
  to `𝓣.Tensor (Sum.elim cW cZ)` formed by contracting the indices specified by
  `cX` and `cY`, which are assumed to be dual. -/
def contrElim (e : X ≃ Y) (h : cX.ContrAll e cY) :
    𝓣.Tensor (Sum.elim cW cX) ⊗[R] 𝓣.Tensor (Sum.elim cY cZ) →ₗ[R] 𝓣.Tensor (Sum.elim cW cZ) :=
    (𝓣.tensoratorEquiv cW cZ).toLinearMap ∘ₗ 𝓣.contrAllMid e h ∘ₗ
    (TensorProduct.congr (𝓣.tensoratorEquiv cW cX).symm
      (𝓣.tensoratorEquiv cY cZ).symm).toLinearMap

/-!

## Group acting on contraction

-/

@[simp]
lemma contrAll_rep (e : X ≃ Y) (h : cX.ContrAll e cY) (g : G) :
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
  simp only [contrAll_tmul, PiTensorProduct.tprodCoeff_eq_smul_tprod, tmul_smul, smul_tmul,
    LinearMapClass.map_smul, LinearMap.coe_comp, Function.comp_apply, map_tmul, rep_tprod,
    smul_eq_mul]
  apply congrArg
  apply congrArg
  simp only [contrAll', mapIso_tprod, Equiv.symm_symm_apply, colorModuleCast_equivariant_apply,
    LinearMap.coe_comp, Function.comp_apply]
  apply congrArg
  erw [pairProd_tmul_tprod_tprod, pairProd_tmul_tprod_tprod, PiTensorProduct.map_tprod,
    PiTensorProduct.map_tprod]
  apply congrArg
  funext x
  nth_rewrite 2 [← contrDual_inv (cX x) g]
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
  nth_rewrite 2 [← @contrAll_rep_apply R _ 𝓣 _ _ _ G]
  rfl

/-!

## Contraction based on specification

-/

lemma contr_cond (e : (C ⊕ C) ⊕ P ≃ X) :
    cX.MapIso e.symm (Sum.elim (Sum.elim (cX.contrLeft e) (cX.contrRight e)) (cX.contr e)) := by
  rw [TensorColor.ColorMap.MapIso, Equiv.eq_comp_symm]
  funext x
  match x with
  | Sum.inl (Sum.inl x) => rfl
  | Sum.inl (Sum.inr x) => rfl
  | Sum.inr x => rfl

/-- Contraction of indices based on an equivalence `(C ⊕ C) ⊕ P ≃ X`. The indices
  in `C` are contracted pair-wise, whilst the indices in `P` are preserved. -/
def contr (e : (C ⊕ C) ⊕ P ≃ X) (h : cX.ContrCond e) :
    𝓣.Tensor cX →ₗ[R] 𝓣.Tensor (cX.contr e) :=
  (TensorProduct.lid R _).toLinearMap ∘ₗ
  (TensorProduct.map (𝓣.contrAll (Equiv.refl C) h.to_contrAll) LinearMap.id) ∘ₗ
  (TensorProduct.congr (𝓣.tensoratorEquiv _ _).symm (LinearEquiv.refl R _)).toLinearMap ∘ₗ
  (𝓣.tensoratorEquiv _ _).symm.toLinearMap ∘ₗ
  (𝓣.mapIso e.symm (𝓣.contr_cond e)).toLinearMap

open PiTensorProduct in
lemma contr_tprod (e : (C ⊕ C) ⊕ P ≃ X) (h : cX.ContrCond e) (f : (i : X) → 𝓣.ColorModule (cX i)) :
    𝓣.contr e h (tprod R f) = (𝓣.contrAll (Equiv.refl C) h.to_contrAll
        (tprod R (fun i => f (e (Sum.inl (Sum.inl i)))) ⊗ₜ[R]
        tprod R (fun i => f (e (Sum.inl (Sum.inr i)))))) •
        tprod R (fun (p : P) => f (e (Sum.inr p))) := by
  simp only [contr, LinearEquiv.comp_coe, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.trans_apply, mapIso_tprod, Equiv.symm_symm_apply,
    tensoratorEquiv_symm_tprod, congr_tmul, LinearEquiv.refl_apply, map_tmul, LinearMap.id_coe,
    id_eq, lid_tmul]
  rw [contrAll_tmul]
  rfl

open PiTensorProduct in
@[simp]
lemma contr_tprod_isEmpty [IsEmpty C] (e : (C ⊕ C) ⊕ P ≃ X) (h : cX.ContrCond e)
    (f : (i : X) → 𝓣.ColorModule (cX i)) :
    𝓣.contr e h (tprod R f) = tprod R (fun (p : P) => f (e (Sum.inr p))) := by
  rw [contr_tprod]
  rw [contrAll_tmul, contrAll'_isEmpty_tmul]
  simp only [isEmptyEquiv_tprod, Equiv.refl_symm, mapIso_tprod, Equiv.refl_apply, one_mul]
  erw [isEmptyEquiv_tprod]
  simp

/-- The contraction of indices via `contr` is equivariant. -/
@[simp]
lemma contr_equivariant (e : (C ⊕ C) ⊕ P ≃ X) (h : cX.ContrCond e)
    (g : G) (x : 𝓣.Tensor cX) : 𝓣.contr e h (g • x) = g • 𝓣.contr e h x := by
  simp only [TensorColor.ColorMap.contr, contr, TensorProduct.congr, LinearEquiv.refl_toLinearMap,
    LinearEquiv.symm_symm, LinearEquiv.refl_symm, LinearEquiv.ofLinear_toLinearMap,
    LinearEquiv.comp_coe, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.trans_apply, rep_mapIso_apply, rep_tensoratorEquiv_symm_apply]
  rw [← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp]
  rw [← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp]
  rw [LinearMap.comp_assoc, rep_tensoratorEquiv_symm, ← LinearMap.comp_assoc]
  simp only [contrAll_rep, LinearMap.comp_id, LinearMap.id_comp]
  have h1 {M N A B : Type} [AddCommMonoid M] [AddCommMonoid N]
      [AddCommMonoid A] [AddCommMonoid B] [Module R M] [Module R N] [Module R A] [Module R B]
      (f : M →ₗ[R] N) (g : A →ₗ[R] B) : TensorProduct.map f g
      = TensorProduct.map (LinearMap.id) g ∘ₗ TensorProduct.map f (LinearMap.id) :=
    ext rfl
  rw [h1]
  simp only [LinearMap.coe_comp, Function.comp_apply, rep_lid_apply]
  rw [← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp]
  rfl

end TensorStructure
