/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.LinearAlgebra.Contraction

/-!

# A tensor read as a linear map through a pairing

A pairing `p : V ⊗ W → R` reads a tensor `z` in `W ⊗ U` as a linear map from `V` to `U`.

## i. Overview

Here `V`, `W` and `U` are spaces, and `x`, `w`, `y` and `z` are elements. The pairing `p` contracts
an element `x` of `V` with an element `w` of `W` to the scalar `p (x ⊗ w)`. A tensor `z` in `W ⊗ U`
reads as the linear map from `V` to `U` that contracts its input with the first factor of `z` and
keeps the second. On a pure tensor this is `x ↦ p (x ⊗ w) • y` for `z = w ⊗ y`.

For Lorentz tensors take `V = ℝ⁴` the vectors `x^μ`, `W = (ℝ⁴)*` the covectors `w_μ`, and
`p (x ⊗ w) = x^μ w_μ`. In the standard basis of `ℝ⁴` and its dual basis, a tensor `z` in `W ⊗ U`
has components `z_μ^A`, where `A` labels a basis of `U`, and reads as the map `x^μ ↦ x^μ z_μ^A`.

- With `U = V` and `z` the Kronecker delta `δ_μ^ν`, the map is `x^μ ↦ x^μ δ_μ^ν = x^ν`, the
  identity.
- With `U = W` and `z` the Minkowski metric `η_μν`, the map is `x^μ ↦ x^μ η_μν = x_ν`, lowering
  the index.

## ii. Key results

- `TensorProduct.pairingToLinearMap` : a tensor in `W ⊗ U` as a linear map `V → U` through `p`.
- `TensorProduct.pairingToLinearMap_tmul` : its value on a pure tensor `w ⊗ y`.
- `TensorProduct.pairingToLinearMap_lTensor` : a linear map applied to the second factor of `z` is
  applied to the values.
- `TensorProduct.pairingToLinearMap_apply` : the value at `x` as `x ⊗ z` with its first two factors
  contracted.
- `TensorProduct.lTensor_pairingToLinearMap_apply` : the map of `N` on the second factor of `M` as
  `M ⊗ N` with its middle pair contracted.

## iii. Table of contents

- A. Reading a tensor as a linear map

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace TensorProduct

variable {R V W U U' : Type*} [CommSemiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid W]
    [Module R W] [AddCommMonoid U] [Module R U] [AddCommMonoid U'] [Module R U']

/-!

## A. Reading a tensor as a linear map

-/

/-- The tensor `z` in `W ⊗ U` read through the pairing `p` as a linear map from `V` to `U`. The
pairing takes the input on the left, `p (x ⊗ w)`, and contracts it with the first factor of `z`.
It is Mathlib's `dualTensorHom R V U` with each `w` read as the form
`x ↦ p (x ⊗ w)`. -/
noncomputable def pairingToLinearMap (p : V ⊗[R] W →ₗ[R] R) : W ⊗[R] U →ₗ[R] V →ₗ[R] U :=
  dualTensorHom R V U ∘ₗ (TensorProduct.curry p).flip.rTensor U

/-- On a pure tensor, `(w ⊗ y)(x) = p (x ⊗ w) • y`. -/
@[simp]
lemma pairingToLinearMap_tmul (p : V ⊗[R] W →ₗ[R] R) (w : W) (y : U) (x : V) :
    pairingToLinearMap p (w ⊗ₜ y) x = p (x ⊗ₜ w) • y := rfl

/-- Applying a linear map `f : U → U'` to the second factor of `z` composes the map of `z` with
`f`. -/
lemma pairingToLinearMap_lTensor (p : V ⊗[R] W →ₗ[R] R) (f : U →ₗ[R] U') (z : W ⊗[R] U) :
    pairingToLinearMap p (f.lTensor W z) = f ∘ₗ pairingToLinearMap p z := by
  induction z using TensorProduct.inductionOn with
  | tmul w y => ext x; simp
  | add z z' hz hz' => simp only [map_add, hz, hz', LinearMap.comp_add]

/-- The value at `x` is `x ⊗ z` with its first two factors contracted by `p`,
`lid (p.rTensor U (assoc.symm (x ⊗ z)))`. This is the form of a contraction built from Mathlib's
associator `TensorProduct.assoc` and unitor `TensorProduct.lid`. -/
lemma pairingToLinearMap_apply (p : V ⊗[R] W →ₗ[R] R) (z : W ⊗[R] U) (x : V) :
    pairingToLinearMap p z x =
      TensorProduct.lid R U (p.rTensor U ((TensorProduct.assoc R V W U).symm (x ⊗ₜ z))) := by
  induction z using TensorProduct.inductionOn with
  | tmul w y => rfl
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, tmul_add, hz, hz']

/-- Applying the map of `N` to the second factor of `M ∈ U' ⊗ V` is `M ⊗ N` with its middle pair
contracted by `p`, as in `M^{aμ} N_μ^b`. The right side is that contraction built from Mathlib's
associator `TensorProduct.assoc` and unitor `TensorProduct.lid`, as in
`pairingToLinearMap_apply`. -/
lemma lTensor_pairingToLinearMap_apply (p : V ⊗[R] W →ₗ[R] R) (M : U' ⊗[R] V) (N : W ⊗[R] U) :
    (pairingToLinearMap p N).lTensor U' M = (TensorProduct.lid R U).lTensor U'
      ((p.rTensor U).lTensor U' ((TensorProduct.assoc R V W U).symm.toLinearMap.lTensor U'
        (TensorProduct.assoc R U' V (W ⊗[R] U) (M ⊗ₜ N)))) := by
  induction M using TensorProduct.inductionOn with
  | add M M' hM hM' => simp only [map_add, add_tmul, hM, hM']
  | tmul u v => simp [pairingToLinearMap_apply]

end TensorProduct
