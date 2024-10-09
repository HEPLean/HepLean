/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.PiTensorProduct
/-!
# Pi Tensor Products

The purpose of this file is to define some results about Pi tensor products not currently
in Mathlib.

At some point these should either be up-streamed to Mathlib or replaced with definitions already
in Mathlib.

-/
namespace HepLean.PiTensorProduct

noncomputable section tmulEquiv


variable {R ι1 ι2 ι3 M N : Type} [CommSemiring R]
  {s1 : ι1 → Type} [inst1 : (i : ι1) → AddCommMonoid (s1 i)] [inst1' : (i : ι1) → Module R (s1 i)]
  {s2 : ι2 → Type} [inst2 : (i : ι2) → AddCommMonoid (s2 i)] [inst2' : (i : ι2) → Module R (s2 i)]
  {s3 : ι3 → Type} [inst3 : (i : ι3) → AddCommMonoid (s3 i)] [inst3' : (i : ι3) → Module R (s3 i)]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

open TensorProduct

/-!

## induction principals for pi tensor products

-/
lemma tensorProd_piTensorProd_ext
    {f g : ((⨂[R] i : ι1, s1 i) ⊗[R] ⨂[R] i : ι2, s2 i) →ₗ[R] M}
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
      simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod] at hx hy
      simp [map_add, tmul_add, hx, hy])
  intro ry fy
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, tmul_smul, LinearMapClass.map_smul]
  apply congrArg
  simp only [smul_tmul, tmul_smul, LinearMapClass.map_smul]
  exact congrArg (HSMul.hSMul rx) (h fx fy)

lemma induction_assoc
    {f g : ((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i) ⊗[R] ⨂[R] i : ι3, s3 i) →ₗ[R] M}
    (h : ∀ p q m, f (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q ⊗ₜ[R] PiTensorProduct.tprod R m)
    = g (PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q ⊗ₜ[R] PiTensorProduct.tprod R m)) : f = g := by
  apply TensorProduct.ext'
  refine fun x ↦
  PiTensorProduct.induction_on' x ?_ (by
    intro a b hx hy y
    simp [map_add, add_tmul, hx, hy])
  intro rx fx
  intro y
  simp
  simp only [smul_tmul, tmul_smul, LinearMapClass.map_smul]
  apply congrArg
  let f' : ((⨂[R] i : ι2, s2 i) ⊗[R] ⨂[R] i : ι3, s3 i) →ₗ[R] M  := {
    toFun := fun y => f (PiTensorProduct.tprod R fx ⊗ₜ[R] y),
    map_add' := fun y1 y2 => by
      simp [tmul_add]
    map_smul' := fun r y => by
      simp [tmul_smul]}
  let g' : ((⨂[R] i : ι2, s2 i) ⊗[R] ⨂[R] i : ι3, s3 i) →ₗ[R] M  := {
    toFun := fun y => g (PiTensorProduct.tprod R fx ⊗ₜ[R] y),
    map_add' := fun y1 y2 => by
      simp [tmul_add]
    map_smul' := fun r y => by
      simp [tmul_smul]}
  change f' y = g' y
  apply congrFun
  refine DFunLike.coe_fn_eq.mpr ?H.h.h.a
  apply tensorProd_piTensorProd_ext
  intro p q
  exact h fx p q

lemma induction_assoc'
    {f g : (((⨂[R] i : ι1, s1 i) ⊗[R] (⨂[R] i : ι2, s2 i)) ⊗[R] ⨂[R] i : ι3, s3 i) →ₗ[R] M}
    (h : ∀ p q m, f ((PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q) ⊗ₜ[R] PiTensorProduct.tprod R m)
     = g ((PiTensorProduct.tprod R p ⊗ₜ[R] PiTensorProduct.tprod R q) ⊗ₜ[R] PiTensorProduct.tprod R m)) : f = g := by
  apply TensorProduct.ext'
  intro x
  refine fun y ↦
  PiTensorProduct.induction_on' y ?_ (by
    intro a b hy hx
    simp [map_add, add_tmul, tmul_add, hy, hx])
  intro ry fy
  simp
  apply congrArg
  let f' : ((⨂[R] i : ι1, s1 i) ⊗[R] ⨂[R] i : ι2, s2 i) →ₗ[R] M  := {
    toFun := fun y => f (y ⊗ₜ[R] PiTensorProduct.tprod R fy),
    map_add' := fun y1 y2 => by
      simp [add_tmul]
    map_smul' := fun r y => by
      simp [smul_tmul]}
  let g' : ((⨂[R] i : ι1, s1 i) ⊗[R] ⨂[R] i : ι2, s2 i) →ₗ[R] M  := {
    toFun := fun y => g (y ⊗ₜ[R] PiTensorProduct.tprod R fy),
    map_add' := fun y1 y2 => by
      simp [add_tmul]
    map_smul' := fun r y => by
      simp [smul_tmul]}
  change f' x = g' x
  apply congrFun
  refine DFunLike.coe_fn_eq.mpr ?H.h.h.a
  apply tensorProd_piTensorProd_ext
  intro p q
  exact h p q fy

lemma induction_tmul_mod
    {f g : ((⨂[R] i : ι1, s1 i) ⊗[R] N) →ₗ[R] M}
    (h : ∀ p m, f (PiTensorProduct.tprod R p ⊗ₜ[R] m) = g (PiTensorProduct.tprod R p ⊗ₜ[R] m)) : f = g := by
  apply TensorProduct.ext'
  refine fun y ↦
  PiTensorProduct.induction_on' y ?_ (by
    intro a b hy hx
    simp [map_add, add_tmul, tmul_add, hy, hx])
  intro ry fy
  intro x
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, smul_tmul, tmul_smul, map_smul]
  apply congrArg
  exact h fy x

lemma induction_mod_tmul
    {f g : (N ⊗[R] ⨂[R] i : ι1, s1 i) →ₗ[R] M}
    (h : ∀ m p, f (m ⊗ₜ[R] PiTensorProduct.tprod R p) = g (m ⊗ₜ[R] PiTensorProduct.tprod R p)) : f = g := by
  apply TensorProduct.ext'
  intro x
  refine fun y ↦
  PiTensorProduct.induction_on' y ?_ (by
    intro a b hy hx
    simp [map_add, add_tmul, tmul_add, hy, hx])
  intro ry fy
  simp only [PiTensorProduct.tprodCoeff_eq_smul_tprod, smul_tmul, tmul_smul, map_smul]
  apply congrArg
  exact h x fy
/-!

# Dependent type version of PiTensorProduct.tmulEquiv
-/

instance : (i : ι1 ⊕ ι2) → AddCommMonoid ((fun i => Sum.elim s1 s2 i) i) := fun i =>
  match i with
  | Sum.inl i => inst1 i
  | Sum.inr i => inst2 i

instance : (i : ι1 ⊕ ι2) → Module R ((fun i => Sum.elim s1 s2 i) i) := fun i =>
  match i with
  | Sum.inl i => inst1' i
  | Sum.inr i => inst2' i


private def pureInl (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) : (i : ι1) → s1 i :=
  fun i => f (Sum.inl i)

private def pureInr (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) : (i : ι2) → s2 i :=
  fun i => f (Sum.inr i)

section
variable [DecidableEq (ι1 ⊕ ι2)] [DecidableEq ι1] [DecidableEq ι2]
lemma pureInl_update_left (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι1)
    (v1 : s1 x) : pureInl (Function.update f (Sum.inl x) v1) =
    Function.update (pureInl f) x v1 := by
  funext y
  simp only [pureInl, Function.update, Sum.inl.injEq, Sum.elim_inl]
  split
  · rename_i h
    subst h
    rfl
  · rfl

lemma pureInr_update_left (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι1)
    (v2 : s1 x) :
    pureInr (Function.update f (Sum.inl x) v2) = (pureInr f) := by
  funext y
  simp [pureInr, Function.update, Sum.inl.injEq, Sum.elim_inl]

lemma pureInr_update_right (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι2)
    (v2 : s2 x) : pureInr (Function.update f (Sum.inr x) v2) =
    Function.update (pureInr f) x v2 := by
  funext y
  simp only [pureInr, Function.update, Sum.inr.injEq, Sum.elim_inr]
  split
  · rename_i h
    subst h
    rfl
  · rfl

lemma pureInl_update_right (f : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i) (x : ι2)
    (v1 : s2 x) :
    pureInl (Function.update f (Sum.inr x) v1) = (pureInl f) := by
  funext y
  simp [pureInl, Function.update, Sum.inr.injEq, Sum.elim_inr]

end
def domCoprod : MultilinearMap R (Sum.elim s1 s2) ((⨂[R] i : ι1, s1 i) ⊗[R] ⨂[R] i : ι2, s2 i) where
  toFun f := (PiTensorProduct.tprod R (pureInl f)) ⊗ₜ
    (PiTensorProduct.tprod R (pureInr f))
  map_add' f xy v1 v2 := by
    haveI : DecidableEq (ι1 ⊕ ι2) := inferInstance
    haveI : DecidableEq ι1 :=
      @Function.Injective.decidableEq ι1 (ι1 ⊕ ι2) Sum.inl _ Sum.inl_injective
    haveI : DecidableEq ι2 :=
      @Function.Injective.decidableEq ι2 (ι1 ⊕ ι2) Sum.inr _ Sum.inr_injective
    match xy with
    | Sum.inl xy =>
      simp only [Sum.elim_inl, pureInl_update_left, MultilinearMap.map_add, pureInr_update_left, ←
        add_tmul]
    | Sum.inr xy =>
      simp only [Sum.elim_inr, pureInr_update_right, MultilinearMap.map_add, pureInl_update_right, ←
        tmul_add]
  map_smul' f xy r p := by
    haveI : DecidableEq (ι1 ⊕ ι2) := inferInstance
    haveI : DecidableEq ι1 :=
      @Function.Injective.decidableEq ι1 (ι1 ⊕ ι2) Sum.inl _ Sum.inl_injective
    haveI : DecidableEq ι2 :=
      @Function.Injective.decidableEq ι2 (ι1 ⊕ ι2) Sum.inr _ Sum.inr_injective
    match xy with
    | Sum.inl x =>
      simp only [Sum.elim_inl, pureInl_update_left, MultilinearMap.map_smul, pureInr_update_left,
        smul_tmul, tmul_smul]
    | Sum.inr y =>
      simp only [Sum.elim_inr, pureInl_update_right, pureInr_update_right, MultilinearMap.map_smul,
        tmul_smul]

def tmulSymm : (⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i) →ₗ[R]
    ((⨂[R] i : ι1, s1 i) ⊗[R] ⨂[R] i : ι2, s2 i) := PiTensorProduct.lift domCoprod


def elimPureTensor (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i) : (i : ι1 ⊕ ι2) → Sum.elim s1 s2 i :=
  fun x =>
    match x with
    | Sum.inl x => p x
    | Sum.inr x => q x

section

variable [DecidableEq ι1] [DecidableEq ι2]

lemma elimPureTensor_update_right (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i)
    (y : ι2) (r : s2 y) : elimPureTensor p (Function.update q y r) =
    Function.update (elimPureTensor p q) (Sum.inr y) r := by
  funext x
  match x with
  | Sum.inl x =>
    simp only [Sum.elim_inl, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_noteq]
    rfl
  | Sum.inr x =>
    change Function.update q y r x = _
    simp only [Function.update, Sum.inr.injEq, Sum.elim_inr]
    split_ifs
    · rename_i h
      subst h
      simp_all only
    · rfl

@[simp]
lemma elimPureTensor_update_left (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i)
    (x : ι1) (r : s1 x) : elimPureTensor (Function.update p x r) q =
    Function.update (elimPureTensor p q) (Sum.inl x) r := by
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
  | Sum.inr y =>
    simp only [Sum.elim_inr, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_noteq]
    rfl

end

def elimPureTensorMulLin : MultilinearMap R s1
    (MultilinearMap R s2 (⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i)) where
  toFun p := {
    toFun := fun q => PiTensorProduct.tprod R (elimPureTensor p q)
    map_add' := fun m x v1 v2 => by
      haveI : DecidableEq ι2 := inferInstance
      haveI := Classical.decEq ι1
      simp only [elimPureTensor_update_right, MultilinearMap.map_add]
    map_smul' := fun m x r v => by
      haveI : DecidableEq ι2 := inferInstance
      haveI := Classical.decEq ι1
      simp only [elimPureTensor_update_right, MultilinearMap.map_smul]}
  map_add' p x v1 v2 := by
    haveI : DecidableEq ι1 := inferInstance
    haveI := Classical.decEq ι2
    apply MultilinearMap.ext
    intro y
    simp
  map_smul' p x r v := by
    haveI : DecidableEq ι1 := inferInstance
    haveI := Classical.decEq ι2
    apply MultilinearMap.ext
    intro y
    simp

def tmul : ((⨂[R] i : ι1, s1 i) ⊗[R] ⨂[R] i : ι2, s2 i) →ₗ[R]
    ⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i := TensorProduct.lift {
    toFun := fun a ↦
      PiTensorProduct.lift <|
          PiTensorProduct.lift (elimPureTensorMulLin) a,
    map_add' := fun a b ↦ by simp
    map_smul' := fun r a ↦ by simp}

def tmulEquiv : ((⨂[R] i : ι1, s1 i) ⊗[R] ⨂[R] i : ι2, s2 i) ≃ₗ[R]
    ⨂[R] i : ι1 ⊕ ι2, (Sum.elim s1 s2) i  :=
  LinearEquiv.ofLinear tmul tmulSymm
  (by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro p
    simp only [tmul, tmulSymm, domCoprod, LinearMap.compMultilinearMap_apply,
      LinearMap.coe_comp, Function.comp_apply, PiTensorProduct.lift.tprod, MultilinearMap.coe_mk,
      lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
    simp only [elimPureTensorMulLin, MultilinearMap.coe_mk, LinearMap.id_coe, id_eq]
    apply congrArg
    funext x
    match x with
    | Sum.inl x => rfl
    | Sum.inr x => rfl)
  (by
    apply tensorProd_piTensorProd_ext
    intro p q
    simp only [tmulSymm, domCoprod, tmul, elimPureTensorMulLin, LinearMap.coe_comp,
      Function.comp_apply, lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, PiTensorProduct.lift.tprod,
      MultilinearMap.coe_mk, LinearMap.id_coe, id_eq]
    rfl)

@[simp]
lemma tmulEquiv_tmul_tprod (p : (i : ι1) → s1 i) (q : (i : ι2) → s2 i) :
    tmulEquiv ((PiTensorProduct.tprod R) p ⊗ₜ[R] (PiTensorProduct.tprod R) q) =
    (PiTensorProduct.tprod R) (elimPureTensor p q) := by
  simp only [tmulEquiv, tmul, elimPureTensorMulLin, LinearEquiv.ofLinear_apply, lift.tmul,
    LinearMap.coe_mk, AddHom.coe_mk, PiTensorProduct.lift.tprod, MultilinearMap.coe_mk]

end tmulEquiv
end HepLean.PiTensorProduct
