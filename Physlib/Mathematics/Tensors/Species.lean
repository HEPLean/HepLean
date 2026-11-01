/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.ForMathlib.Contraction
public import Physlib.Mathematics.Tensors.Color
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.Bilinear
/-!

# Tensor species and their tensors

A species assigns to each color a representation with a basis, the contraction with the dual
color and the Kronecker delta. Its tensors with colors `c : ι → Color K` form Mathlib's
`⨂[k] i, V (c i)`, for any slot type `ι`.

## i. Overview

A species `S : Species k G K basisIdx` assigns to each color `c` a `k`-module `S.V c`, a
representation `S.rep c` of the group `G` on it, and a basis `S.basis c` labelled by
`basisIdx c.kind`. It also gives the invariant contraction `S.contr c : V c ⊗ V c.dual → k`, which
pairs an index with its dual as in `u^μ α_μ`, and the Kronecker delta `S.delta c ∈ V c.dual ⊗ V c`,
written `δ_μ^ν`. Two laws relate them. The contraction is symmetric, `u^μ α_μ = α_μ u^μ`
(`contr_tmul_symm`). The delta acts as the identity, `u^μ δ_μ^ν = u^ν` (`snake`). It follows that
the delta is invariant and that the delta of `c.dual` is the delta of `c` with its factors
swapped. Since `c.dual.dual = c` holds by `rfl`, no statement needs a cast.

Indices name slots, as in abstract index notation, so `u^μ α_μ` is `S.contr c (u ⊗ α)` in any
basis. Components are taken with `tensorBasis`. The bases `S.basis c` and `S.basis c.dual` are not
related by the laws. The components of `S.delta c` form the identity matrix, and
`S.contr c (e_μ ⊗ e^ν)` is `1` for `μ = ν` and `0` otherwise, only when the two bases are dual. A
species does not require this, and a concrete species can prove it.

The basis labels `basisIdx κ` depend only on the kind `κ` of a color, not on its variance, so an
index and its dual have the same labels by definition, as `μ` in `v^μ` and `α_μ`. They are a
parameter, not a field, so that a conjugate species can give a kind and its conjugate the same
labels by definition. A species is a value, so a new species can
be built from an old one, for example by restricting the group.

`S.Tensor c` is a space and `S.pure f` an element of it. The space is `⨂[k] i, V (c i)`. The pure
tensor of a family `f` of vectors, one per slot, is `⨂ₜ[k] i, f i`, such as `u ⊗ α ⊗ β`. Every
tensor is a sum of pure tensors. A group element `Λ` acts on every slot by the representation of
its color. The components `T^μ_ν` of a tensor `T` are its coordinates in the basis
`e_μ ⊗ e^ν ⊗ …` of Mathlib's `Basis.piTensorProduct`.

For example, Lorentz tensors have one kind `vec`. An upper index has color `⟨vec, up⟩` with
`V ⟨vec, up⟩ = ℝ⁴` and basis `e_μ`. A lower index has color `⟨vec, down⟩` with
`V ⟨vec, down⟩ = (ℝ⁴)*` and basis `e^μ`. The colors `![⟨vec, up⟩, ⟨vec, down⟩, ⟨vec, down⟩]` give
the space `ℝ⁴ ⊗ (ℝ⁴)* ⊗ (ℝ⁴)*` of tensors `T = T^μ_νρ e_μ ⊗ e^ν ⊗ e^ρ`. The pure tensor
`u ⊗ α ⊗ β` has components `u^μ α_ν β_ρ`. A Lorentz transformation `Λ` acts as
`(ΛT)^μ_νρ = Λ^μ_σ (Λ⁻¹)^τ_ν (Λ⁻¹)^λ_ρ T^σ_τλ`. Lower indices transform with `Λ⁻¹`, which keeps
`u^μ α_μ` invariant.

## ii. Key results

- `Species` : the data and laws of a tensor species.
- `Species.contr_invariant`, `Species.delta_invariant` : `u^μ α_μ` and `δ_μ^ν` are invariant.
- `Species.delta_eq_comm_delta_dual` : the delta of `c` is the delta of `c.dual`, swapped.
- `Species.pairingToLinearMap_contr_injective` : a tensor in `V c.dual ⊗ U` is determined by the
  linear map `V c → U` it defines through the contraction.
- `Species.Tensor`, `Species.pure`, `Species.inductionOn_pure` : tensors, pure tensors, and
  induction through pure tensors.
- `Species.smul_pure` : the group acts on a pure tensor slot by slot.
- `Species.map_smul_of_pure` : a map of tensors that commutes with the group on pure tensors
  commutes with it on all tensors.
- `Species.tensorBasis`, `Species.tensorBasis_repr_pure` : the basis of tensors, and the
  components of a pure tensor.
- `Species.contr_tmul_eq_sum_basis` : the contraction of two vectors in components.

## iii. Table of contents

- A. Species
- B. Invariance of the contraction, invariance and symmetry of the delta
- C. Tensors
- D. The group action
- E. The basis of tensors

## iv. References

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

/-!

## A. Species

-/

/-- A tensor species: for each color a representation with a basis, the contraction `u^μ α_μ`
with the dual color, and the Kronecker delta `δ_μ^ν`. The basis labels `basisIdx κ` depend only on
the kind, so a color and its dual share them. They are a parameter so that a conjugate species can
give a kind and its conjugate the same labels by definition. -/
structure Species (k : Type) [CommRing k] (G : Type) [Group G] (K : Type)
    (basisIdx : K → Type) [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] where
  /-- The vector space of a color. -/
  V : Color K → Type
  /-- The vector spaces are additive groups. -/
  [addCommGroup : ∀ c, AddCommGroup (V c)]
  /-- The vector spaces are modules over `k`. -/
  [module : ∀ c, Module k (V c)]
  /-- The representation of a color. -/
  rep : (c : Color K) → Representation k G (V c)
  /-- The basis of a color. -/
  basis : (c : Color K) → Module.Basis (basisIdx c.kind) k (V c)
  /-- The invariant contraction `V c ⊗ V c.dual → k`, `u ⊗ α ↦ u^μ α_μ`. The vector of color `c`
  is the first factor. -/
  contr : (c : Color K) →
    ((rep c).tprod (rep c.dual)).IntertwiningMap (Representation.trivial k G k)
  /-- The Kronecker delta `δ_μ^ν ∈ V c.dual ⊗ V c`. The factor of the dual color is first. -/
  delta : (c : Color K) → V c.dual ⊗[k] V c
  /-- The contraction is symmetric, `u^μ α_μ = α_μ u^μ`. -/
  contr_tmul_symm : ∀ c (x : V c) (y : V c.dual), contr c (x ⊗ₜ[k] y) = contr c.dual (y ⊗ₜ[k] x)
  /-- The snake law `u^μ δ_μ^ν = u^ν`: the delta, read as a linear map through the contraction
  (`pairingToLinearMap`), is the identity. The vector `u` is contracted with the first factor of
  the delta. -/
  snake : ∀ c, pairingToLinearMap (contr c).toLinearMap (delta c) = LinearMap.id

attribute [instance] Species.addCommGroup Species.module

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-!

## B. Invariance of the contraction, invariance and symmetry of the delta

-/

/-- The contraction is invariant, `(Λu)^μ (Λα)_μ = u^μ α_μ` for every `Λ : G`. -/
lemma contr_invariant (S : Species k G K basisIdx) (c : Color K) (g : G) (x : S.V c)
    (y : S.V c.dual) : S.contr c (S.rep c g x ⊗ₜ[k] S.rep c.dual g y) = S.contr c (x ⊗ₜ[k] y) := by
  change S.contr c ((S.rep c).tprod (S.rep c.dual) g (x ⊗ₜ[k] y)) = _
  rw [(S.contr c).isIntertwining]
  simp

/-- A tensor `z ∈ V c.dual ⊗ U` read through the contraction as a linear map `x ↦ z x` from
`V c` to `U` satisfies `((Λ ⊗ f) z)(Λx) = f (z x)` for every `Λ : G` and linear map `f` on `U`.
For `f = Λ` this is the equivariance `(Λz)(Λx) = Λ(z x)`. -/
lemma pairingToLinearMap_contr_map_rep (S : Species k G K basisIdx) (c : Color K) (g : G)
    {U U' : Type} [AddCommGroup U] [Module k U] [AddCommGroup U'] [Module k U'] (f : U →ₗ[k] U')
    (z : S.V c.dual ⊗[k] U) (x : S.V c) :
    pairingToLinearMap (S.contr c).toLinearMap (TensorProduct.map (S.rep c.dual g) f z)
      (S.rep c g x) = f (pairingToLinearMap (S.contr c).toLinearMap z x) := by
  induction z using TensorProduct.inductionOn with
  | tmul w y =>
    simp only [TensorProduct.map_tmul, pairingToLinearMap_tmul, map_smul,
      Representation.IntertwiningMap.toLinearMap_apply, S.contr_invariant]
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']

/-- A tensor `z ∈ V c.dual ⊗ U` is recovered from its linear map `x ↦ z x` by applying the map
to the `V c` factor of the delta of `c.dual` with its factors swapped. In bases of `c` and `c.dual`
that are dual, this reads `z = e^μ ⊗ z(e_μ)`. -/
lemma lTensor_pairingToLinearMap_comm_delta_dual (S : Species k G K basisIdx) (c : Color K)
    {U : Type} [AddCommGroup U] [Module k U] (z : S.V c.dual ⊗[k] U) :
    (pairingToLinearMap (S.contr c).toLinearMap z).lTensor (S.V c.dual)
      (TensorProduct.comm k _ _ (S.delta c.dual)) = z := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ h₁ h₂ => simp only [map_add, LinearMap.lTensor_add, LinearMap.add_apply, h₁, h₂]
  | tmul w y =>
    -- On `w ⊗ y` this is the snake law at `c.dual`, applied to `w`, with `contr_tmul_symm`.
    conv_rhs => rw [← LinearMap.id_apply (R := k) w, ← S.snake c.dual]
    induction S.delta c.dual using TensorProduct.inductionOn with
    | add D₁ D₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, add_tmul, h₁, h₂]
    | tmul e₁ e₂ =>
      simp only [TensorProduct.comm_tmul, LinearMap.lTensor_tmul, pairingToLinearMap_tmul,
        Representation.IntertwiningMap.toLinearMap_apply, tmul_smul, smul_tmul']
      rw [S.contr_tmul_symm c e₁ w]

/-- A tensor `z ∈ V c.dual ⊗ U` is determined by the linear map `x ↦ z x` from `V c` to `U` it
defines through the contraction. In particular `δ_μ^ν` is the only tensor acting as the
identity. -/
lemma pairingToLinearMap_contr_injective (S : Species k G K basisIdx) (c : Color K) {U : Type}
    [AddCommGroup U] [Module k U] :
    Function.Injective (pairingToLinearMap (S.contr c).toLinearMap :
      S.V c.dual ⊗[k] U →ₗ[k] S.V c →ₗ[k] U) := fun z z' h => by
  rw [← S.lTensor_pairingToLinearMap_comm_delta_dual c z,
    ← S.lTensor_pairingToLinearMap_comm_delta_dual c z', h]

/-- The delta of `c` is the delta of `c.dual ∈ V c ⊗ V c.dual` with its factors swapped. -/
lemma delta_eq_comm_delta_dual (S : Species k G K basisIdx) (c : Color K) :
    S.delta c = TensorProduct.comm k _ _ (S.delta c.dual) := by
  simpa [S.snake c] using (S.lTensor_pairingToLinearMap_comm_delta_dual c (S.delta c)).symm

/-- The delta is invariant, `Λ δ = δ`. -/
lemma delta_invariant (S : Species k G K basisIdx) (c : Color K) (g : G) :
    TensorProduct.map (S.rep c.dual g) (S.rep c g) (S.delta c) = S.delta c := by
  -- Both act as the identity: `(Λδ)(Λx) = Λx` by the snake law.
  apply S.pairingToLinearMap_contr_injective c
  ext x
  conv_lhs => rw [← Representation.self_inv_apply (S.rep c) g x]
  rw [S.pairingToLinearMap_contr_map_rep, S.snake c, LinearMap.id_apply, LinearMap.id_apply,
    Representation.self_inv_apply]

/-!

## C. Tensors

-/

/-- The space `⨂[k] i, S.V (c i)` of tensors with colors `c` on the slots `ι`. It is a `def`, not
an `abbrev`, so that the type remembers `S` and instances on `⨂` from elsewhere do not apply. -/
def Tensor (S : Species k G K basisIdx) {ι : Type} (c : ι → Color K) : Type :=
  ⨂[k] i, S.V (c i)

noncomputable instance {S : Species k G K basisIdx} {ι : Type} {c : ι → Color K} :
    AddCommGroup (S.Tensor c) :=
  inferInstanceAs (AddCommGroup (⨂[k] i, S.V (c i)))

noncomputable instance {S : Species k G K basisIdx} {ι : Type} {c : ι → Color K} :
    Module k (S.Tensor c) :=
  inferInstanceAs (Module k (⨂[k] i, S.V (c i)))

variable {ι : Type} {c : ι → Color K}

/-- The identity from `S.Tensor c` to Mathlib's `⨂[k] i, S.V (c i)`, as a linear equivalence.
Mathlib's constructions on `⨂` are composed with it. -/
noncomputable def toPiTensor (S : Species k G K basisIdx) (c : ι → Color K) :
    S.Tensor c ≃ₗ[k] ⨂[k] i, S.V (c i) :=
  LinearEquiv.refl k _

/-- The pure tensor of a family of vectors, one per slot, such as `u ⊗ α ⊗ β` with components
`u^μ α_ν β_ρ`. It is Mathlib's `⨂ₜ[k] i, f i`. -/
noncomputable def pure (S : Species k G K basisIdx) (f : Π i, S.V (c i)) : S.Tensor c :=
  (S.toPiTensor c).symm (⨂ₜ[k] i, f i)

variable {S : Species k G K basisIdx}

@[simp]
lemma toPiTensor_pure (f : Π i, S.V (c i)) : S.toPiTensor c (S.pure f) = ⨂ₜ[k] i, f i := rfl

@[simp]
lemma toPiTensor_symm_tprod (f : Π i, S.V (c i)) :
    (S.toPiTensor c).symm (⨂ₜ[k] i, f i) = S.pure f := rfl

/-- Induction on tensors through pure tensors: every tensor is a sum of pure tensors. -/
lemma inductionOn_pure {P : S.Tensor c → Prop}
    (h : ∀ f : Π i, S.V (c i), P (S.pure f)) (hsmul : ∀ (r : k) t, P t → P (r • t))
    (hadd : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ + t₂)) (t : S.Tensor c) : P t :=
  PiTensorProduct.induction_on (motive := P) t (fun r f => hsmul r _ (h f)) hadd

/-!

## D. The group action

-/

/-- The group acts on every slot by the representation of its color,
`Λ (u ⊗ α ⊗ …) = Λu ⊗ Λα ⊗ …`, through Mathlib's `PiTensorProduct.mapMonoidHom`. -/
noncomputable instance : DistribMulAction G (S.Tensor c) :=
  DistribMulAction.compHom (M := Module.End k (S.Tensor c)) _
    (PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi fun i => S.rep (c i)))

@[simp]
lemma smul_pure (g : G) (f : Π i, S.V (c i)) :
    g • S.pure f = S.pure fun i => S.rep (c i) g (f i) :=
  PiTensorProduct.map_tprod _ _

noncomputable instance : SMulCommClass G k (S.Tensor c) where
  smul_comm g r t := by
    change PiTensorProduct.map (fun i => S.rep (c i) g) (r • t) = r • PiTensorProduct.map _ t
    exact map_smul _ r t

noncomputable instance : SMulCommClass k G (S.Tensor c) := .symm _ _ _

/-- A linear or conjugate-linear map of tensors that commutes with `Λ` on pure tensors commutes
with `Λ` on all tensors. -/
lemma map_smul_of_pure {ι' : Type} {c' : ι' → Color K} {σ : k →+* k} {F : Type}
    [FunLike F (S.Tensor c) (S.Tensor c')] [SemilinearMapClass F σ (S.Tensor c) (S.Tensor c')]
    (f : F) (g : G) (h : ∀ p : Π i, S.V (c i), f (g • S.pure p) = g • f (S.pure p))
    (t : S.Tensor c) : f (g • t) = g • f t := by
  induction t using inductionOn_pure with
  | h p => exact h p
  | hsmul r t ht => rw [smul_comm, map_smulₛₗ, ht, map_smulₛₗ, smul_comm]
  | hadd x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- Moving a vector along an equality of colors `a = a'` commutes with the group action. -/
lemma cast_rep {a a' : Color K} (p : a = a') (g : G) (x : S.V a) :
    LinearEquiv.cast (R := k) (M := S.V) p (S.rep a g x) =
      S.rep a' g (LinearEquiv.cast (R := k) (M := S.V) p x) := by
  subst p
  rfl

/-!

## E. The basis of tensors

-/

/-- The basis `e_μ ⊗ e^ν ⊗ …` of tensors, Mathlib's `Basis.piTensorProduct` of the bases of the
colors. -/
noncomputable def tensorBasis (S : Species k G K basisIdx) [Fintype ι] (c : ι → Color K) :
    Module.Basis (Π i, basisIdx (c i).kind) k (S.Tensor c) :=
  (Basis.piTensorProduct fun i => S.basis (c i)).map (S.toPiTensor c).symm

/-- A basis tensor is the pure tensor of basis vectors, `e_μ ⊗ e^ν ⊗ …`. -/
lemma tensorBasis_apply [Fintype ι] (x : Π i, basisIdx (c i).kind) :
    S.tensorBasis c x = S.pure fun i => S.basis (c i) (x i) := by
  simp [tensorBasis, Basis.piTensorProduct_apply]

/-- The components of a pure tensor are products, `(u ⊗ α)^μ_ν = u^μ α_ν`. -/
lemma tensorBasis_repr_pure [Fintype ι] (f : Π i, S.V (c i))
    (x : Π i, basisIdx (c i).kind) :
    (S.tensorBasis c).repr (S.pure f) x = ∏ i, (S.basis (c i)).repr (f i) (x i) := by
  simp [tensorBasis, Basis.piTensorProduct_repr_tprod_apply]

/-- The contraction in components, `∑ μ ν, u^μ α_ν C_μ^ν`, where `C_μ^ν = S.contr c (e_μ ⊗ e^ν)`.
When the bases of `c` and `c.dual` are dual, `C_μ^ν` is `1` for `μ = ν` and `0` otherwise, and
the sum has one index. A species does not require this. -/
lemma contr_tmul_eq_sum_basis (c : Color K) (x : S.V c) (y : S.V c.dual) :
    S.contr c (x ⊗ₜ y) =
      ∑ μ, ∑ ν, (S.basis c).repr x μ * (S.basis c.dual).repr y ν *
        S.contr c (S.basis c μ ⊗ₜ S.basis c.dual ν) := by
  simpa [Finsupp.sum_fintype, mul_assoc] using (LinearMap.sum_repr_mul_repr_mul (S.basis c)
    (S.basis c.dual) (B := TensorProduct.curry (S.contr c).toLinearMap) x y).symm

end Species

end Tensors
