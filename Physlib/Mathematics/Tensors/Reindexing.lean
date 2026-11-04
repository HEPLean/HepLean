/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Species
/-!

# Relabeling the slots of a tensor

A bijection of the slots of a tensor that keeps their colors, and its action on tensors, as in the
transpose `T^μ_ν ↦ T_ν^μ`.

## i. Overview

A tensor of a species `S` with colors `c₁ : ι₁ → Color K` has one slot for each label `i : ι₁`.
A relabeling `σ : ColorEquiv c₁ c₂` from colors `c₁` on `ι₁` to colors `c₂` on `ι₂` is a bijection
`σ.toEquiv : ι₁ ≃ ι₂` together with the proof `σ.color_eq j : c₁ (σ.toEquiv.symm j) = c₂ j` that
every new slot `j` has the color of the old slot it comes from. The proof is stated at the new
labels, so that `c₂ j` reduces for concrete colors. For these the default proof of the structure
finds it, by `rfl` or by `rfl` on each slot, and rejects a relabeling that changes a color.

`S.reindex σ : S.Tensor c₁ ≃ₗ[k] S.Tensor c₂` is a linear equivalence between two spaces of
tensors. The new slot `j` of `S.reindex σ T` holds the vector of the old slot `σ.toEquiv.symm j`,
moved along `σ.color_eq j` from `S.V (c₁ (σ.toEquiv.symm j))` to `S.V (c₂ j)`. The move changes
the type and no data. The components move with the slots (`tensorBasis_repr_reindex`).

For example, a Lorentz upper index has the color `⟨vec, up⟩` with `V ⟨vec, up⟩ = ℝ⁴` and basis
`e_μ`, and a lower index has the color `⟨vec, down⟩` with `V ⟨vec, down⟩ = (ℝ⁴)*` and basis `e^μ`.
The colors `c₁ = ![⟨vec, up⟩, ⟨vec, down⟩]` on `Fin 2` give the space `ℝ⁴ ⊗ (ℝ⁴)*`, whose elements
are `T = T^μ_ν e_μ ⊗ e^ν`. The transpose relabels the slots by `Equiv.swap 0 1`, written
`.mk (Equiv.swap 0 1) : ColorEquiv c₁ ![⟨vec, down⟩, ⟨vec, up⟩]`. It sends `T` to its transpose
`Tᵀ = T^μ_ν e^ν ⊗ e_μ` in `(ℝ⁴)* ⊗ ℝ⁴`, whose components are `(Tᵀ)_ν^μ = T^μ_ν`.

## ii. Key results

- `ColorEquiv` : a bijection of slots that keeps their colors, with `refl`, `symm` and `trans`.
- `Species.reindex`, `Species.reindex_pure` : a relabeling applied to tensors, and to a pure
  tensor.
- `Species.reindex_reindex` : two relabelings in sequence are their composite.
- `Species.reindex_smul` : relabeling commutes with the group action.
- `Species.tensorBasis_repr_reindex` : the components of a relabeled tensor, `(Tᵀ)_ν^μ = T^μ_ν`.

## iii. Table of contents

- A. Relabelings that keep colors
- B. Relabeling tensors
- C. Composition and equivariance
- D. Components

## iv. References

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

/-!

## A. Relabelings that keep colors

-/

/-- A relabeling of slots that keeps their colors: a bijection of slots, with the proof that each
new slot has the color of the old slot it comes from. The proof is stated at the new labels `j`,
so that `c₂ j` reduces at labels such as `inl x` or `0`. For finitely many concrete slots it is
found by `rfl` or by cases. Two relabelings are equal when their bijections are
(`ColorEquiv.ext`). -/
@[ext]
structure ColorEquiv {K : Type} {ι₁ ι₂ : Type} (c₁ : ι₁ → Color K) (c₂ : ι₂ → Color K) where
  /-- The bijection of slots, old slot `i` to new slot `toEquiv i`. -/
  toEquiv : ι₁ ≃ ι₂
  /-- The new slot `j` has the color of the old slot `toEquiv.symm j`. -/
  color_eq : ∀ j, c₁ (toEquiv.symm j) = c₂ j := by
    first | exact fun _ => rfl | (intro j; fin_cases j <;> rfl)

namespace ColorEquiv

variable {K : Type} {ι₁ ι₂ ι₃ : Type} {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K}
    {c₃ : ι₃ → Color K}

/-- The identity relabeling, where every slot keeps its label. -/
def refl (c₁ : ι₁ → Color K) : ColorEquiv c₁ c₁ := ⟨Equiv.refl ι₁, fun _ => rfl⟩

/-- The inverse relabeling, where every slot gets back its old label. -/
def symm (σ : ColorEquiv c₁ c₂) : ColorEquiv c₂ c₁ :=
  ⟨σ.toEquiv.symm, fun i => by simpa using (σ.color_eq (σ.toEquiv i)).symm⟩

/-- The relabeling `σ₁` followed by `σ₂`. -/
def trans (σ₁ : ColorEquiv c₁ c₂) (σ₂ : ColorEquiv c₂ c₃) : ColorEquiv c₁ c₃ :=
  ⟨σ₁.toEquiv.trans σ₂.toEquiv, fun j => (σ₁.color_eq _).trans (σ₂.color_eq j)⟩

end ColorEquiv

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}

variable {ι₁ ι₂ ι₃ : Type}

/-!

## B. Relabeling tensors

-/

variable (S) in
/-- The relabeling `σ` applied to tensors, as in the transpose `T^μ_ν ↦ T_ν^μ`. The new slot `j`
holds the vector of the old slot `σ.toEquiv.symm j`, moved along `σ.color_eq j`. It is Mathlib's
`PiTensorProduct.reindex` followed by `PiTensorProduct.congr` of `LinearEquiv.cast`. -/
noncomputable def reindex {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂) :
    S.Tensor c₁ ≃ₗ[k] S.Tensor c₂ :=
  S.toPiTensor c₁ ≪≫ₗ PiTensorProduct.reindex k _ σ.toEquiv ≪≫ₗ
    PiTensorProduct.congr (fun j => LinearEquiv.cast (M := S.V) (σ.color_eq j)) ≪≫ₗ
    (S.toPiTensor c₂).symm

/-- On a pure tensor, the new slot `j` holds the vector of the old slot `σ.toEquiv.symm j`, moved
along `σ.color_eq j`. -/
@[simp]
lemma reindex_pure {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂)
    (f : Π i, S.V (c₁ i)) :
    S.reindex σ (S.pure f) = S.pure fun j =>
      LinearEquiv.cast (R := k) (M := S.V) (σ.color_eq j) (f (σ.toEquiv.symm j)) := by
  simp [reindex, PiTensorProduct.reindex_tprod, congr_tprod]

/-!

## C. Composition and equivariance

-/

/-- Relabeling by `σ₁` and then by `σ₂` is relabeling by `σ₁.trans σ₂`. -/
lemma reindex_reindex {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} {c₃ : ι₃ → Color K}
    (σ₁ : ColorEquiv c₁ c₂) (σ₂ : ColorEquiv c₂ c₃) (t : S.Tensor c₁) :
    S.reindex σ₂ (S.reindex σ₁ t) = S.reindex (σ₁.trans σ₂) t := by
  induction t using inductionOn_pure with
  | h f =>
    simp only [reindex_pure, LinearEquiv.cast_apply, cast_cast]
    rfl
  | hsmul r t ht => rw [map_smul, map_smul, ht, map_smul]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- Relabeling commutes with the group action, as in `(ΛT)ᵀ = Λ Tᵀ`. -/
lemma reindex_smul {c₁ : ι₁ → Color K} {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂) (g : G)
    (t : S.Tensor c₁) : S.reindex σ (g • t) = g • S.reindex σ t :=
  map_smul_of_pure (S.reindex σ) g (fun f => by
    simp only [smul_pure, reindex_pure]
    congr 1
    funext j
    exact cast_rep _ _ _) t

/-!

## D. Components

-/

/-- The components of a relabeled tensor are those of the tensor, as in `(Tᵀ)_ν^μ = T^μ_ν`. The
old slot `i` takes the label `y (σ.toEquiv i)` of its new slot, cast along the equality of their
colors. For concrete colors and labels the cast is between equal types, and `rfl` removes it. -/
lemma tensorBasis_repr_reindex [Fintype ι₁] [Fintype ι₂] {c₁ : ι₁ → Color K}
    {c₂ : ι₂ → Color K} (σ : ColorEquiv c₁ c₂) (t : S.Tensor c₁)
    (y : Π j, basisIdx (c₂ j).kind) :
    (S.tensorBasis c₂).repr (S.reindex σ t) y =
      (S.tensorBasis c₁).repr t fun i =>
        cast (congrArg (basisIdx ∘ Color.kind) (σ.symm.color_eq i)) (y (σ.toEquiv i)) := by
  induction t using inductionOn_pure with
  | hsmul r t ht => simp only [map_smul, Finsupp.smul_apply, ht]
  | hadd t t' ht ht' => simp only [map_add, Finsupp.add_apply, ht, ht']
  | h f =>
    rw [reindex_pure, tensorBasis_repr_pure, tensorBasis_repr_pure]
    refine (Fintype.prod_equiv σ.toEquiv _ _ fun i => ?_).symm
    -- The old slot `σ.toEquiv.symm (σ.toEquiv i)` is `i` only up to a proof, so it is generalized.
    have h : ∀ i' (_ : i' = i) (d : Color K) (p : c₁ i' = d) (q : d = c₁ i) (z : basisIdx d.kind),
        (S.basis (c₁ i)).repr (f i) (cast (congrArg (basisIdx ∘ Color.kind) q) z) =
          (S.basis d).repr (LinearEquiv.cast (R := k) (M := S.V) p (f i')) z := by
      rintro _ rfl _ rfl _ _
      rfl
    exact h _ (σ.toEquiv.symm_apply_apply i) _ _ (σ.symm.color_eq i) _

end Species

end Tensors
