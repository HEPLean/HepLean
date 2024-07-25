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
import HepLean.Mathematics.PiTensorProduct
/-!

# Real Lorentz Tensors

In this file we define real Lorentz tensors.

We implicitly follow the definition of a modular operad.
This will relation should be made explicit in the future.

## References

-- For modular operads see: [Raynor][raynor2021graphical]

-/
/-! TODO: Relate the constructions here to `PiTensorProduct`. -/
/-! TODO: Generalize to maps into Lorentz tensors. -/



section PiTensorProductResults
variable {ι ι₂ ι₃ : Type*}
variable {R : Type*} [CommSemiring R]
variable {R₁ R₂ : Type*}
variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable {E : Type*} [AddCommMonoid E] [Module R E]
variable {F : Type*} [AddCommMonoid F]


end PiTensorProductResults

open TensorProduct
noncomputable section
/-- The possible `color` of an index for a RealLorentzTensor.
 There are two possiblities, `up` and `down`. -/
inductive RealLorentzTensor.Color where
  | up : RealLorentzTensor.Color
  | down : RealLorentzTensor.Color

/-- To set of allowed index values associated to a color of index. -/
def RealLorentzTensor.ColorIndex (d : ℕ) (μ : RealLorentzTensor.Color) : Type :=
  match μ with
  | RealLorentzTensor.Color.up => Fin 1 ⊕ Fin d
  | RealLorentzTensor.Color.down => Fin 1 ⊕ Fin d

/-- The instance of a finite type on the set of allowed index values for a given color. -/
instance (d : ℕ) (μ : RealLorentzTensor.Color) : Fintype (RealLorentzTensor.ColorIndex d μ) :=
  match μ with
  | RealLorentzTensor.Color.up => instFintypeSum (Fin 1) (Fin d)
  | RealLorentzTensor.Color.down => instFintypeSum (Fin 1) (Fin d)

/-- The color index set for each color has a decidable equality. -/
instance (d : ℕ) (μ : RealLorentzTensor.Color) : DecidableEq (RealLorentzTensor.ColorIndex d μ) :=
  match μ with
  | RealLorentzTensor.Color.up => instDecidableEqSum
  | RealLorentzTensor.Color.down => instDecidableEqSum

def RealLorentzTensor.ColorModule (d : ℕ) (μ : RealLorentzTensor.Color) : Type :=
  RealLorentzTensor.ColorIndex d μ → ℝ

instance (d : ℕ) (μ : RealLorentzTensor.Color) :
    AddCommMonoid (RealLorentzTensor.ColorModule d μ) :=
  Pi.addCommMonoid

instance (d : ℕ) (μ : RealLorentzTensor.Color) : Module ℝ (RealLorentzTensor.ColorModule d μ) :=
  Pi.module _ _ _

instance (d : ℕ) (μ : RealLorentzTensor.Color) : AddCommGroup (RealLorentzTensor.ColorModule d μ) :=
  Pi.addCommGroup

/-- Real Lorentz tensors. -/
def RealLorentzTensor {X : Type} (d : ℕ) (c : X → RealLorentzTensor.Color) : Type :=
    ⨂[ℝ] i : X, RealLorentzTensor.ColorModule d (c i)

instance {X : Type} (d : ℕ) (c : X → RealLorentzTensor.Color) :
    AddCommMonoid (RealLorentzTensor d c) :=
  PiTensorProduct.instAddCommMonoid fun i => RealLorentzTensor.ColorModule d (c i)

instance {X : Type} (d : ℕ) (c : X → RealLorentzTensor.Color) :
  Module ℝ (RealLorentzTensor d c) := PiTensorProduct.instModule


instance {X : Type} (d : ℕ) (c : X → RealLorentzTensor.Color) :
  AddCommGroup (RealLorentzTensor d c) := PiTensorProduct.instAddCommGroup

namespace RealLorentzTensor

variable {d : ℕ} {X Y Z : Type} (c : X → Color)
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

/-- An `IndexValue` is a set of actual values an index can take. e.g. for a
  3-tensor (0, 1, 2). -/
def IndexValue {X : Type} (d : ℕ) (c : X → RealLorentzTensor.Color) :
    Type 0 := (x : X) → ColorIndex d (c x)

instance [Fintype X] [DecidableEq X] : Fintype (IndexValue d c) := Pi.fintype

instance [Fintype X] : DecidableEq (IndexValue d c) :=
  Fintype.decidablePiFintype

def basisColorModule {d : ℕ} (μ : Color) :
    Basis (ColorIndex d μ) ℝ (ColorModule d μ) := Pi.basisFun _ _

def basis (d : ℕ) (c : X → RealLorentzTensor.Color) :
    Basis (IndexValue d c) ℝ (RealLorentzTensor d c) :=
  Basis.piTensorProduct (fun x => basisColorModule (c x))

abbrev PiModule (d : ℕ) (c : X → Color) := IndexValue d c → ℝ

def asPi {d : ℕ} {c : X → Color} :
    RealLorentzTensor d c ≃ₗ[ℝ] PiModule d c  :=
  (basis d c).repr  ≪≫ₗ
  Finsupp.linearEquivFunOnFinite ℝ ℝ (IndexValue d c)


/-!

## Colors

-/

/-- The involution acting on colors. -/
def τ : Color → Color
  | Color.up => Color.down
  | Color.down => Color.up

/-- The map τ is an involution. -/
@[simp]
lemma τ_involutive : Function.Involutive τ := by
  intro x
  cases x <;> rfl

lemma color_eq_dual_symm {μ ν : Color} (h : μ = τ ν) : ν = τ μ :=
  (Function.Involutive.eq_iff τ_involutive).mp h.symm

lemma color_comp_τ_symm {c1 c2 : X → Color} (h : c1 = τ ∘ c2) : c2 = τ ∘ c1 :=
  funext (fun x => color_eq_dual_symm (congrFun h x))

/-- An equivalence of `ColorIndex` types given an equality of colors. -/
def colorIndexCast {d : ℕ} {μ₁ μ₂ : Color} (h : μ₁ = μ₂) :
    ColorIndex d μ₁ ≃ ColorIndex d μ₂ :=
  Equiv.cast (congrArg (ColorIndex d) h)

@[simp]
lemma colorIndexCast_symm {d : ℕ} {μ₁ μ₂ : Color} (h : μ₁ = μ₂) :
    (@colorIndexCast d _ _ h).symm = colorIndexCast h.symm := by
  rfl

/-- An equivalence of `ColorIndex` between that of a color and that of its dual.
   I.e. the allowed index values for a color and its dual are equivalent. -/
def colorIndexDualCastSelf {d : ℕ} {μ : Color}:
    ColorIndex d μ ≃ ColorIndex d (τ μ) where
  toFun x :=
    match μ with
    | Color.up => x
    | Color.down => x
  invFun x :=
    match μ with
    | Color.up => x
    | Color.down => x
  left_inv x := by cases μ <;> rfl
  right_inv x := by cases μ <;> rfl

/-- An equivalence between the allowed index values of a color and a color dual to it. -/
def colorIndexDualCast {μ ν : Color} (h : μ = τ ν) : ColorIndex d μ ≃ ColorIndex d ν :=
  (colorIndexCast h).trans colorIndexDualCastSelf.symm

@[simp]
lemma colorIndexDualCast_symm {μ ν : Color} (h : μ = τ ν) : (colorIndexDualCast h).symm =
    @colorIndexDualCast d _ _ ((Function.Involutive.eq_iff τ_involutive).mp h.symm) := by
  match μ, ν with
  | Color.up, Color.down => rfl
  | Color.down, Color.up => rfl

@[simp]
lemma colorIndexDualCast_trans {μ ν ξ : Color} (h : μ = τ ν) (h' : ν = τ ξ) :
    (@colorIndexDualCast d _ _ h).trans (colorIndexDualCast h') =
    colorIndexCast (by rw [h, h', τ_involutive]) := by
  match μ, ν, ξ with
  | Color.up, Color.down, Color.up => rfl
  | Color.down, Color.up, Color.down => rfl

@[simp]
lemma colorIndexDualCast_trans_colorsIndexCast {μ ν ξ : Color} (h : μ = τ ν) (h' : ν = ξ) :
    (@colorIndexDualCast d _ _ h).trans (colorIndexCast h') =
    colorIndexDualCast (by rw [h, h']) := by
  match μ, ν, ξ with
  | Color.down, Color.up, Color.up => rfl
  | Color.up, Color.down, Color.down => rfl

@[simp]
lemma colorIndexCast_trans_colorsIndexDualCast {μ ν ξ : Color} (h : μ = ν) (h' : ν = τ ξ) :
    (colorIndexCast h).trans (@colorIndexDualCast d _ _ h')  =
    colorIndexDualCast (by rw [h, h']) := by
  match μ, ν, ξ with
  | Color.up, Color.up, Color.down => rfl
  | Color.down, Color.down, Color.up => rfl


/-!

## Index values

-/



/-!

## Induced isomorphisms between IndexValue sets

-/

/-- An isomorphism of the type of index values given an isomorphism of sets. -/
def indexValueIso (d : ℕ) (f : X ≃ Y) {i : X → Color} {j : Y → Color} (h : i = j ∘ f) :
    IndexValue d i ≃ IndexValue d j :=
  (Equiv.piCongrRight (fun μ => colorIndexCast (congrFun h μ))).trans $
  Equiv.piCongrLeft (fun y => ColorIndex d (j y)) f

@[simp]
lemma indexValueIso_symm_apply' (d : ℕ) (f : X ≃ Y) {i : X → Color} {j : Y → Color}
    (h : i = j ∘ f) (y : IndexValue d j) (x : X) :
    (indexValueIso d f h).symm y x = (colorIndexCast (congrFun h x)).symm (y (f x)) := by
  rfl

@[simp]
lemma indexValueIso_trans (d : ℕ) (f : X ≃ Y) (g : Y ≃ Z) {i : X → Color}
    {j : Y → Color} {k : Z → Color} (h : i = j ∘ f) (h' : j = k ∘ g) :
    (indexValueIso d f h).trans (indexValueIso d g h') =
    indexValueIso d (f.trans g) (by rw [h, h', Function.comp.assoc]; rfl) := by
  have h1 : ((indexValueIso d f h).trans (indexValueIso d g h')).symm =
      (indexValueIso d (f.trans g) (by rw [h, h', Function.comp.assoc]; rfl)).symm := by
    subst h' h
    exact Equiv.coe_inj.mp rfl
  simpa only [Equiv.symm_symm] using congrArg (fun e => e.symm) h1

@[simp]
lemma indexValueIso_symm (d : ℕ) (f : X ≃ Y) (h : i = j ∘ f) :
    (indexValueIso d f h).symm =
    indexValueIso d f.symm ((Equiv.eq_comp_symm f j i).mpr h.symm) := by
  ext i : 1
  rw [← Equiv.symm_apply_eq]
  funext y
  rw [indexValueIso_symm_apply', indexValueIso_symm_apply']
  simp only [Function.comp_apply, colorIndexCast, Equiv.cast_symm, Equiv.cast_apply, cast_cast]
  apply cast_eq_iff_heq.mpr
  rw [Equiv.apply_symm_apply]

lemma indexValueIso_eq_symm (d : ℕ) (f : X ≃ Y) (h : i = j ∘ f) :
    indexValueIso d f h =
    (indexValueIso d f.symm ((Equiv.eq_comp_symm f j i).mpr h.symm)).symm := by
  rw [indexValueIso_symm]
  rfl

@[simp]
lemma indexValueIso_refl (d : ℕ) (i : X → Color) :
    indexValueIso d (Equiv.refl X) (rfl : i = i) = Equiv.refl _ := by
  rfl



/-!

## Dual isomorphism for index values

-/

/-- The isomorphism between the index values of a color map and its dual. -/
def indexValueDualIso (d : ℕ) {i : X → Color} {j : Y → Color} (e : X ≃ Y)
    (h : i = τ ∘ j ∘ e) : IndexValue d i ≃ IndexValue d j :=
  (Equiv.piCongrRight (fun μ => colorIndexDualCast (congrFun h μ))).trans $
  Equiv.piCongrLeft (fun y => ColorIndex d (j y)) e

lemma indexValueDualIso_symm_apply' (d : ℕ) {i : X → Color} {j : Y → Color} (e : X ≃ Y)
    (h : i = τ ∘ j ∘ e) (y : IndexValue d j) (x : X) :
    (indexValueDualIso d e h).symm y x = (colorIndexDualCast (congrFun h x)).symm (y (e x)) := by
  rfl

lemma indexValueDualIso_cond_symm {i : X → Color} {j : Y → Color} {e : X ≃ Y}
    (h : i = τ ∘ j ∘ e) : j = τ ∘ i ∘ e.symm := by
  subst h
  simp only [Function.comp.assoc, Equiv.self_comp_symm, CompTriple.comp_eq]
  rw [← Function.comp.assoc]
  funext a
  simp only [τ_involutive, Function.Involutive.comp_self, Function.comp_apply, id_eq]

@[simp]
lemma indexValueDualIso_symm {d : ℕ} {i : X → Color} {j : Y → Color} (e : X ≃ Y)
    (h : i = τ ∘ j ∘ e) : (indexValueDualIso d e h).symm =
    indexValueDualIso d e.symm (indexValueDualIso_cond_symm h) := by
  ext i : 1
  rw [← Equiv.symm_apply_eq]
  funext a
  rw [indexValueDualIso_symm_apply', indexValueDualIso_symm_apply']
  erw [← Equiv.trans_apply, colorIndexDualCast_symm, colorIndexDualCast_symm,
    colorIndexDualCast_trans]
  simp only [Function.comp_apply, colorIndexCast, Equiv.cast_apply]
  apply cast_eq_iff_heq.mpr
  rw [Equiv.apply_symm_apply]

lemma indexValueDualIso_eq_symm {d : ℕ} {i : X → Color} {j : Y → Color} (e : X ≃ Y)
    (h : i = τ ∘ j ∘ e) :
    indexValueDualIso d e h = (indexValueDualIso d e.symm (indexValueDualIso_cond_symm h)).symm := by
  rw [indexValueDualIso_symm]
  simp

lemma indexValueDualIso_cond_trans {i : X → Color} {j : Y → Color} {k : Z → Color}
    {e : X ≃ Y} {f : Y ≃ Z} (h : i = τ ∘ j ∘ e) (h' : j = τ ∘ k ∘ f) :
    i = k ∘ (e.trans f) := by
  rw [h, h']
  funext a
  simp only [Function.comp_apply, Equiv.coe_trans]
  rw [τ_involutive]

@[simp]
lemma indexValueDualIso_trans {d : ℕ} {i : X → Color} {j : Y → Color} {k : Z → Color}
    (e : X ≃ Y) (f : Y ≃ Z) (h : i = τ ∘ j ∘ e) (h' : j = τ ∘ k ∘ f) :
    (indexValueDualIso d e h).trans (indexValueDualIso d f h') =
    indexValueIso d (e.trans f) (indexValueDualIso_cond_trans h h') := by
  ext i
  rw [Equiv.trans_apply]
  rw [← Equiv.eq_symm_apply, ← Equiv.eq_symm_apply, indexValueIso_eq_symm]
  funext a
  rw [indexValueDualIso_symm_apply', indexValueDualIso_symm_apply',
    indexValueIso_symm_apply']
  erw [← Equiv.trans_apply]
  rw [colorIndexDualCast_symm, colorIndexDualCast_symm, colorIndexDualCast_trans]
  simp only [Function.comp_apply, colorIndexCast, Equiv.symm_trans_apply, Equiv.cast_symm,
    Equiv.cast_apply, cast_cast]
  symm
  apply cast_eq_iff_heq.mpr
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

lemma indexValueDualIso_cond_trans_indexValueIso {i : X → Color} {j : Y → Color} {k : Z → Color}
    {e : X ≃ Y} {f : Y ≃ Z} (h : i = τ ∘ j ∘ e) (h' : j = k ∘ f)  :
    i = τ ∘ k ∘ (e.trans f) := by
  rw [h, h']
  funext a
  simp only [Function.comp_apply, Equiv.coe_trans]

@[simp]
lemma indexValueDualIso_trans_indexValueIso {d : ℕ} {i : X → Color} {j : Y → Color} {k : Z → Color}
    (e : X ≃ Y) (f : Y ≃ Z) (h : i = τ ∘ j ∘ e) (h' : j = k ∘ f) :
    (indexValueDualIso d e h).trans (indexValueIso d f h') =
    indexValueDualIso d (e.trans f) (indexValueDualIso_cond_trans_indexValueIso h h') := by
  ext i
  rw [Equiv.trans_apply, ← Equiv.eq_symm_apply]
  funext a
  rw [ indexValueDualIso_eq_symm, indexValueDualIso_symm_apply',
    indexValueIso_symm_apply',indexValueDualIso_eq_symm, indexValueDualIso_symm_apply']
  rw [Equiv.symm_apply_eq]
  erw [← Equiv.trans_apply, ← Equiv.trans_apply]
  simp only [Function.comp_apply, Equiv.symm_trans_apply, colorIndexDualCast_symm,
    colorIndexCast_symm, colorIndexCast_trans_colorsIndexDualCast, colorIndexDualCast_trans]
  simp only [colorIndexCast, Equiv.cast_apply]
  symm
  apply cast_eq_iff_heq.mpr
  rw [Equiv.symm_apply_apply]

lemma indexValueIso_trans_indexValueDualIso_cond {i : X → Color} {j : Y → Color} {k : Z → Color}
    {e : X ≃ Y} {f : Y ≃ Z} (h : i = j ∘ e) (h' : j = τ ∘ k ∘ f)   :
    i = τ ∘ k ∘ (e.trans f) := by
  rw [h, h']
  funext a
  simp only [Function.comp_apply, Equiv.coe_trans]

@[simp]
lemma indexValueIso_trans_indexValueDualIso {d : ℕ} {i : X → Color} {j : Y → Color} {k : Z → Color}
    (e : X ≃ Y) (f : Y ≃ Z) (h : i = j ∘ e) (h' : j = τ ∘ k ∘ f) :
    (indexValueIso d e h).trans (indexValueDualIso d f h') =
    indexValueDualIso d (e.trans f) (indexValueIso_trans_indexValueDualIso_cond h h') := by
  ext i
  rw [Equiv.trans_apply, ← Equiv.eq_symm_apply, ← Equiv.eq_symm_apply]
  funext a
  rw [indexValueIso_symm_apply', indexValueDualIso_symm_apply',
    indexValueDualIso_eq_symm, indexValueDualIso_symm_apply']
  erw [← Equiv.trans_apply, ← Equiv.trans_apply]
  simp only [Function.comp_apply, Equiv.symm_trans_apply, colorIndexDualCast_symm,
    colorIndexCast_symm, colorIndexDualCast_trans_colorsIndexCast, colorIndexDualCast_trans]
  simp only [colorIndexCast, Equiv.cast_apply]
  symm
  apply cast_eq_iff_heq.mpr
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]



/-!

## Mapping isomorphisms on fibers

-/

@[simps!]
def mapIso {d : ℕ} (f : X ≃ Y) {i : X → Color} {j : Y → Color} (h : i = j ∘ f) :
    RealLorentzTensor d i ≃ₗ[ℝ] RealLorentzTensor d j where
  toFun F := F ∘ (indexValueIso d f h).symm
  invFun F := F ∘ indexValueIso d f h
  map_add' F G := by rfl
  map_smul' a F := by rfl
  left_inv F := by
    funext x
    simp only [Function.comp_apply]
    exact congrArg _  $ Equiv.symm_apply_apply (indexValueIso d f h) x
  right_inv F := by
    funext x
    simp only [Function.comp_apply]
    exact congrArg _  $ Equiv.apply_symm_apply (indexValueIso d f h) x

@[simp]
lemma mapIso_trans (d : ℕ) (f : X ≃ Y) (g : Y ≃ Z) {i : X → Color}
    {j : Y → Color} {k : Z → Color} (h : i = j ∘ f) (h' : j = k ∘ g) :
    (@mapIso _ _ d f _ _ h).trans (mapIso g h') =
    mapIso  (f.trans g) (by rw [h, h', Function.comp.assoc]; rfl)  := by
  refine LinearEquiv.toEquiv_inj.mp (Equiv.ext (fun x => (funext (fun a => ?_))))
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.trans_apply, mapIso_apply,
    indexValueIso_symm, ← Equiv.trans_apply, indexValueIso_trans]
  rfl

lemma mapIso_symm (d : ℕ) (f : X ≃ Y) (h : i = j ∘ f) :
    (@mapIso _ _ d f _ _ h).symm = mapIso f.symm ((Equiv.eq_comp_symm f j i).mpr h.symm) := by
  refine LinearEquiv.toEquiv_inj.mp (Equiv.ext (fun x => (funext (fun a => ?_))))
  simp only [LinearEquiv.coe_toEquiv, mapIso_symm_apply, mapIso_apply, indexValueIso_symm,
    Equiv.symm_symm]


/-!

## Sums

-/

/-- An equivalence that splits elements of `IndexValue d (Sum.elim TX TY)` into two components. -/
def indexValueTensorator {X Y : Type} {TX : X → Color} {TY : Y → Color} :
    IndexValue d (Sum.elim TX TY) ≃ IndexValue d TX × IndexValue d TY where
  toFun i := (fun x => i (Sum.inl x), fun x => i (Sum.inr x))
  invFun p := fun c => match c with
    | Sum.inl x => (p.1 x)
    | Sum.inr x => (p.2 x)
  left_inv i := by
    simp only [IndexValue]
    ext1 x
    cases x with
    | inl val => rfl
    | inr val_1 => rfl
  right_inv p := rfl

/-! TODO : Move -/
lemma tensorator_mapIso_cond {cX : X → Color} {cY : Y → Color} {cX' : X' → Color}
    {cY' : Y' → Color} {eX : X ≃ X'} {eY : Y ≃ Y'} (hX : cX = cX' ∘ eX) (hY : cY = cY' ∘ eY) :
    Sum.elim cX cY = Sum.elim cX' cY' ∘ ⇑(eX.sumCongr eY) := by
  subst hX hY
  ext1 x
  simp_all only [Function.comp_apply, Equiv.sumCongr_apply]
  cases x with
  | inl val => simp_all only [Sum.elim_inl, Function.comp_apply, Sum.map_inl]
  | inr val_1 => simp_all only [Sum.elim_inr, Function.comp_apply, Sum.map_inr]

lemma indexValueTensorator_indexValueMapIso {cX : X → Color} {cY : Y → Color} {cX' : X' → Color}
    {cY' : Y' → Color} (eX : X ≃ X') (eY : Y ≃ Y') (hX : cX = cX' ∘ eX) (hY : cY = cY' ∘ eY) :
    (indexValueIso d (Equiv.sumCongr eX eY) (tensorator_mapIso_cond hX hY)).trans indexValueTensorator =
    indexValueTensorator.trans (Equiv.prodCongr (indexValueIso d eX hX) (indexValueIso d eY hY)) := by
  apply Equiv.ext
  intro i
  simp
  simp [ indexValueTensorator]
  apply And.intro
  all_goals
    funext x
    rw [indexValueIso_eq_symm, indexValueIso_symm_apply']
    rw [indexValueIso_eq_symm, indexValueIso_symm_apply']
    simp

/-!

## A basis for Lorentz tensors

-/

noncomputable section basis

open TensorProduct
open Set LinearMap Submodule

variable {d : ℕ} {X Y Y' X'  : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype X'] [DecidableEq X']
  (cX : X → Color) (cY : Y → Color)

def basis : Basis (IndexValue d cX) ℝ (RealLorentzTensor d cX) := Pi.basisFun _ _

@[simp]
def basisProd :
    Basis (IndexValue d cX × IndexValue d cY) ℝ (RealLorentzTensor d cX ⊗[ℝ] RealLorentzTensor d cY) :=
  (Basis.tensorProduct (basis cX) (basis cY))

lemma mapIsoFiber_basis {cX : X → Color} {cY : Y → Color} (e : X ≃ Y) (h : cX = cY ∘ e)
    (i : IndexValue d cX) : (mapIso e h) (basis cX i)
    = basis cY (indexValueIso d e h i) := by
  funext a
  rw [mapIso_apply]
  by_cases ha : a = ((indexValueIso d e h) i)
  · subst ha
    nth_rewrite 2 [indexValueIso_eq_symm]
    rw [Equiv.apply_symm_apply]
    simp only [basis]
    erw [Pi.basisFun_apply, Pi.basisFun_apply]
    simp only [stdBasis_same]
  · simp only [basis]
    erw [Pi.basisFun_apply, Pi.basisFun_apply]
    simp
    rw [if_neg, if_neg]
    exact fun a_1 => ha (_root_.id (Eq.symm a_1))
    rw [← Equiv.symm_apply_eq, indexValueIso_symm]
    exact fun a_1 => ha (_root_.id (Eq.symm a_1))


end basis

/-! TODO: Following the ethos of modular operads, prove properties of contraction. -/

/-! TODO: Use `contr` to generalize to any pair of marked index. -/

/-!

## Rising and lowering indices

Rising or lowering an index corresponds to changing the color of that index.

-/

/-! TODO: Define the rising and lowering of indices using contraction with the metric. -/

/-!

## Graphical species and Lorentz tensors

-/

/-! TODO: From Lorentz tensors graphical species. -/
/-! TODO: Show that the action of the Lorentz group defines an action on the graphical species. -/

end RealLorentzTensor
