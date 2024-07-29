/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Basic
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

variable {R : Type} [CommSemiring R]

namespace TensorStructure

variable (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color}
  {cW : W → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}

/-!

# Contractions of vectors

-/

def contrDualLeftAux {V1 V2 V3 : Type} [AddCommMonoid V1] [AddCommMonoid V2] [AddCommMonoid V3]
    [Module R V1] [Module R V2] [Module R V3] (f : V1 ⊗[R] V2 →ₗ[R] R) :
    V1 ⊗[R] V2 ⊗[R] V3 →ₗ[R] V3 :=
  (TensorProduct.lid R _).toLinearMap ∘ₗ
  TensorProduct.map (f) (LinearEquiv.refl R V3).toLinearMap
  ∘ₗ (TensorProduct.assoc R _ _ _).symm.toLinearMap

/-- The contraction of a vector in `𝓣.ColorModule ν` with a vector in
  `𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η` to form a vector in `𝓣.ColorModule η`. -/
def contrDualLeft {ν η : 𝓣.Color} :
    𝓣.ColorModule ν ⊗[R] 𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η →ₗ[R] 𝓣.ColorModule η :=
  contrDualLeftAux (𝓣.contrDual ν)

def contrDualMidAux {V1 V2 V3 V4 : Type} [AddCommMonoid V1] [AddCommMonoid V2] [AddCommMonoid V3]
    [AddCommMonoid V4] [Module R V1] [Module R V2] [Module R V3] [Module R V4] (f : V1 ⊗[R] V2 →ₗ[R] R) :
    (V4 ⊗[R] V1) ⊗[R] (V2 ⊗[R] V3) →ₗ[R] V4 ⊗[R] V3 :=
  (TensorProduct.map (LinearEquiv.refl R V4).toLinearMap (contrDualLeftAux f)) ∘ₗ
  (TensorProduct.assoc R _ _ _).toLinearMap

/-- The contraction of a vector in `𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule ν` with a vector in
  `𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η` to form a vector in
  `𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule η`. -/
def contrDualMid {μ ν η : 𝓣.Color} :
    (𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule ν) ⊗[R] (𝓣.ColorModule (𝓣.τ ν) ⊗[R] 𝓣.ColorModule η) →ₗ[R]
      𝓣.ColorModule μ ⊗[R] 𝓣.ColorModule η :=
  contrDualMidAux (𝓣.contrDual ν)

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
def contrAll (e : X ≃ Y) (h : cX = 𝓣.τ ∘ cY ∘ e) : 𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY →ₗ[R] R :=
  𝓣.contrAll' ∘ₗ (TensorProduct.congr (LinearEquiv.refl _ _)
    (𝓣.mapIso e.symm (by funext a; simpa [h] using (𝓣.τ_involutive _).symm))).toLinearMap

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
    𝓣.contrAll e h (x ⊗ₜ[R] 𝓣.mapIso e' h' z) =
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
    𝓣.contrAll e h (𝓣.mapIso e' h' x ⊗ₜ[R] y) =
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

/-- The linear map from `𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY ⊗[R] 𝓣.Tensor cZ` to
  `𝓣.Tensor cZ` obtained by contracting all indices in `𝓣.Tensor cX` and `𝓣.Tensor cY`,
  given a proof that this is possible. -/
def contrAllLeft (e : X ≃ Y) (h : cX = 𝓣.τ ∘ cY ∘ e) :
    𝓣.Tensor cX ⊗[R] 𝓣.Tensor cY ⊗[R] 𝓣.Tensor cZ →ₗ[R] 𝓣.Tensor cZ :=
  (TensorProduct.lid R _).toLinearMap ∘ₗ
  TensorProduct.map (𝓣.contrAll e h) (LinearEquiv.refl R (𝓣.Tensor cZ)).toLinearMap
  ∘ₗ (TensorProduct.assoc R _ _ _).symm.toLinearMap

/-- The linear map from `(𝓣.Tensor cW ⊗[R] 𝓣.Tensor cX) ⊗[R] (𝓣.Tensor cY ⊗[R] 𝓣.Tensor cZ)`
  to `𝓣.Tensor cW ⊗[R] 𝓣.Tensor cZ` obtained by contracting all indices of the tensors
  in the middle. -/
def contrAllMid (e : X ≃ Y) (h : cX = 𝓣.τ ∘ cY ∘ e) :
    (𝓣.Tensor cW ⊗[R] 𝓣.Tensor cX) ⊗[R] (𝓣.Tensor cY ⊗[R] 𝓣.Tensor cZ) →ₗ[R]
    𝓣.Tensor cW ⊗[R] 𝓣.Tensor cZ :=
  (TensorProduct.map (LinearEquiv.refl R _).toLinearMap (𝓣.contrAllLeft e h)) ∘ₗ
  (TensorProduct.assoc R _ _ _).toLinearMap

/-- The linear map from `𝓣.Tensor (Sum.elim cW cX) ⊗[R] 𝓣.Tensor (Sum.elim cY cZ)`
  to `𝓣.Tensor (Sum.elim cW cZ)` formed by contracting the indices specified by
  `cX` and `cY`, which are assumed to be dual. -/
def contrElim (e : X ≃ Y) (h : cX = 𝓣.τ ∘ cY ∘ e) :
    𝓣.Tensor (Sum.elim cW cX) ⊗[R] 𝓣.Tensor (Sum.elim cY cZ) →ₗ[R] 𝓣.Tensor (Sum.elim cW cZ) :=
    (𝓣.tensoratorEquiv cW cZ).toLinearMap ∘ₗ 𝓣.contrAllMid e h ∘ₗ
    (TensorProduct.congr (𝓣.tensoratorEquiv cW cX).symm
      (𝓣.tensoratorEquiv cY cZ).symm).toLinearMap

end TensorStructure
