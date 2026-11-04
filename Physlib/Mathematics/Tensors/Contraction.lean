/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Product
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
/-!

# Contraction of tensors

The contraction of pairs of indices, an index with its dual in each pair, as in the trace
`T^ρμ_μ` or the full contraction `T^μν U_μν`, and its laws.

## i. Overview

Take a Lorentz tensor `T = T^ρμ_ν e_ρ ⊗ e_μ ⊗ e^ν`, an element of `ℝ⁴ ⊗ ℝ⁴ ⊗ (ℝ⁴)*`, on the
slots `Fin 3` with colors `c = ![⟨vec, up⟩, ⟨vec, up⟩, ⟨vec, down⟩]`. Its trace over the last two
indices is the vector `(tr T)^ρ = T^ρμ_μ` in `ℝ⁴`. On a pure tensor `u ⊗ v ⊗ α` it is
`(v^μ α_μ) u`, where `v^μ α_μ` is the species contraction `S.contr`.

A contraction sorts the slots into the standard arrangement `κ ⊕ (J ⊕ J)`.
- The slot `inl x`, for `x : κ`, remains, with the color `c' x`.
- For each pair `j : J`, the slot `inr (inl j)` has the color `a j` and the slot `inr (inr j)`
  the dual color `(a j).dual`. The two are contracted.

These colors are `contrColors c' a`. For the trace, `κ = Fin 1`, `c' = ![⟨vec, up⟩]`, `J = Unit`
and `a = fun _ => ⟨vec, up⟩`. `Tensor.contrStd c' a` contracts a tensor in this arrangement. The
two slots of a pair have dual colors by construction, so its formula on pure tensors has no cast
(`contrStd_pure`).

`Tensor.contr σ` contracts the pairs chosen by a relabeling `σ : ColorEquiv c (contrColors c' a)`,
which sends each slot of `T` to its place in the standard arrangement. It is `S.reindex σ`
followed by `Tensor.contrStd c' a`. For the trace, `σ` sends `0 ↦ inl 0`, `1 ↦ inr (inl ())` and
`2 ↦ inr (inr ())`. The duality of the two colors of each pair is part of the color proof of `σ`,
not a separate hypothesis. The index notation `{T | ρ μ μ}ᵀ` builds `σ` from the names.

Each pair is ordered: its slot `inr (inl j)` is the first argument of `S.contr (a j)`. No lemma
here exchanges the two slots of a pair.

A contraction of two tensors is a contraction of their product. The full contraction `T^μν U_μν`
contracts every slot of `T ⊗ U`, with no remaining slots, `κ = Empty`. The laws let a network of
tensors be contracted in pieces.
- Relabeling the pairs does not change the contraction (`contr_reindex_pairs`).
- Two contractions in sequence are one, as contracting `μ` and then `ν` in `T^μ_μ^ν_ν` is
  contracting both pairs at once (`contr_contr`).
- Contracting `T` and then multiplying by `U` is contracting `T ⊗ U`,
  `(T^μ_μν) U^ρ = (T ⊗ U)^μ_μν^ρ` (`tmulEquiv_contr`).

For tensors on two slots, the contraction of the inner indices is the product of matrices
`M^μ_ν N^ν_ρ`, along the relabeling `ColorEquiv.matMul` (`contr_matMul`).

The components of a contraction are sums of components of the tensor, as in
`(tr T)^ρ = ∑ μ ν, C_μ^ν T^ρμ_ν` (`tensorBasis_repr_contr`). Here `C_μ^ν = S.contr (e_μ ⊗ e^ν)`
is the contraction of the basis vectors of the two slots of the pair. The formula assumes nothing
about the bases. When the bases of a color and of its dual are dual, `C_μ^ν` is `1` for `μ = ν`
and `0` otherwise, and the formula is the sum `(tr T)^ρ = ∑ μ, T^ρμ_μ`
(`tensorBasis_repr_contr_of_dual`).

## ii. Key results

- `contrColors` : the colors of the standard arrangement, the remaining slots and then the pairs.
- `Species.Tensor.contrStd` : the contraction of a tensor in the standard arrangement.
- `Species.Tensor.contr` : the contraction of the pairs of indices chosen by `σ`, as in `T^ρμ_μ`.
- `Species.Tensor.contr_pure` : the contraction of a pure tensor.
- `Species.Tensor.contr_smul` : contraction commutes with the group action.
- `Species.Tensor.contr_reindex_pairs` : relabeling the pairs does not change the contraction.
- `Species.Tensor.contr_contr` : two contractions in sequence are one, along `ColorEquiv.chain`.
- `Species.Tensor.tmulEquiv_contr` : contraction commutes with a product by a tensor that is not
  contracted, along `ColorEquiv.withSpectators`.
- `Species.Tensor.contr_matMul` : the contraction `M^μ_ν N^ν_ρ` of two tensors on two slots.
- `Species.Tensor.tensorBasis_repr_contr` : the components of a contraction.
- `Species.Tensor.tensorBasis_repr_contr_of_dual` : the components of a contraction in dual bases.

## iii. Table of contents

- A. Contraction in the standard arrangement of slots
- B. Contraction of chosen pairs of indices
  - B.1. Relabeling the pairs
  - B.2. Two contractions are one
  - B.3. Products with a tensor that is not contracted
- C. The product of two tensors on two slots
- D. Components

## iv. References

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}

variable {ι₁ ι₂ κ κ' κ₁ J J' J₁ J₂ : Type}

namespace Tensor

/-!

## A. Contraction in the standard arrangement of slots

-/

/-- The colors of the standard arrangement `κ ⊕ (J ⊕ J)` of slots. The remaining slot `inl x` has
the color `c x`, and the two slots `inr (inl j)` and `inr (inr j)` of the pair `j` have the colors
`a j` and `(a j).dual`. -/
noncomputable abbrev _root_.Tensors.contrColors {K κ J : Type} (c : κ → Color K) (a : J → Color K) :
    κ ⊕ (J ⊕ J) → Color K :=
  prodColors c (prodColors a fun j => (a j).dual)

/-- The contraction of a tensor in the standard arrangement `κ ⊕ (J ⊕ J)`. For each pair `j` the
slot `inr (inl j)` is contracted with the slot `inr (inr j)` by `S.contr (a j)`, with the slot
`inr (inl j)` as its first argument. The slots `inl x` remain, with the colors `c`. -/
noncomputable def contrStd [Fintype J] (c : κ → Color K) (a : J → Color K) :
    S.Tensor (contrColors c a) →ₗ[k] S.Tensor c :=
  -- The pairs are split into their first halves, of colors `a`, and their second halves, of the
  -- dual colors. Each vector of a second half is read as a linear form on the first half through
  -- `S.contr`, and the halves are paired by Mathlib's `PiTensorProduct.dualDistrib`.
  (TensorProduct.rid k _).toLinearMap ∘ₗ
    (lift ((PiTensorProduct.dualDistrib ∘ₗ
      PiTensorProduct.map (fun j => (curry (S.contr (a j)).toLinearMap).flip) ∘ₗ
      (S.toPiTensor _).toLinearMap).flip ∘ₗ (S.toPiTensor a).toLinearMap) ∘ₗ
      (S.tmulEquiv a _).symm.toLinearMap).lTensor _ ∘ₗ
    (S.tmulEquiv c _).symm.toLinearMap

/-- On a pure tensor the contraction multiplies the remaining vectors by the contraction of the
two vectors of each pair, as in `u ⊗ v ⊗ α ↦ (v^μ α_μ) u`. -/
lemma contrStd_pure [Fintype J] (c : κ → Color K) (a : J → Color K)
    (f : Π x, S.V (contrColors c a x)) :
    contrStd c a (S.pure f) =
      (∏ j, S.contr (a j) (f (.inr (.inl j)) ⊗ₜ f (.inr (.inr j)))) •
        S.pure (c := c) fun x => f (.inl x) := by
  simp [contrStd, PiTensorProduct.map_tprod, PiTensorProduct.dualDistrib_apply]

/-!

## B. Contraction of chosen pairs of indices

-/

/-- The contraction of the pairs of indices chosen by `σ`, as in `T^ρμ_ν ↦ T^ρμ_μ`. It is
`S.reindex σ` followed by `Tensor.contrStd c' a`. For each pair `j` the slot
`σ.toEquiv.symm (inr (inl j))`, of color `a j`, is contracted with the slot
`σ.toEquiv.symm (inr (inr j))`, of color `(a j).dual`. The slots `σ.toEquiv.symm (inl x)` remain,
with the colors `c'`. -/
noncomputable def contr [Fintype J] {c : ι₁ → Color K} {c' : κ → Color K}
    {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) : S.Tensor c →ₗ[k] S.Tensor c' :=
  contrStd c' a ∘ₗ (S.reindex σ).toLinearMap

variable {c : ι₁ → Color K} {c' : κ → Color K}

/-- On a pure tensor the contraction multiplies the remaining vectors by the contraction of the
two vectors of each pair. Each vector is moved along `σ.color_eq` to the color of its slot in the
standard arrangement. -/
lemma contr_pure [Fintype J] {a : J → Color K} (σ : ColorEquiv c (contrColors c' a))
    (f : Π x, S.V (c x)) :
    contr σ (S.pure f) =
      (∏ j, S.contr (a j) (LinearEquiv.cast (R := k) (M := S.V) (σ.color_eq (.inr (.inl j)))
          (f (σ.toEquiv.symm (.inr (.inl j)))) ⊗ₜ LinearEquiv.cast (R := k) (M := S.V)
            (σ.color_eq (.inr (.inr j))) (f (σ.toEquiv.symm (.inr (.inr j)))))) •
        S.pure (c := c') fun x => LinearEquiv.cast (R := k) (M := S.V) (σ.color_eq (.inl x))
          (f (σ.toEquiv.symm (.inl x))) :=
  (congrArg (contrStd c' a) (reindex_pure σ f)).trans (contrStd_pure c' a _)

/-- Contraction commutes with the group action, `(ΛT)^ρμ_μ = Λ^ρ_λ T^λμ_μ` for the action `Λ` of
`g : G`. -/
lemma contr_smul [Fintype J] {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) (g : G)
    (t : S.Tensor c) : contr σ (g • t) = g • contr σ t :=
  map_smul_of_pure (contr σ) g (fun f => by
    rw [smul_pure, contr_pure, contr_pure, smul_comm, smul_pure]
    simp only [cast_rep]
    congr 1
    exact Finset.prod_congr rfl fun j _ => S.contr_invariant (a j) g _ _) t

/-!

### B.1. Relabeling the pairs

-/

/-- Relabeling the pairs along `e : J ≃ J'` does not change the contraction. Each pair keeps its
order. -/
lemma contr_reindex_pairs [Fintype J] [Fintype J'] {a : J → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (e : J ≃ J') (t : S.Tensor c) :
    contr (σ.trans ((ColorEquiv.refl c').sumCongr
      ((ColorEquiv.mk e).sumCongr (.mk e)))) t = contr σ t := by
  simp only [contr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [← reindex_reindex]
  generalize S.reindex σ t = u
  induction u using inductionOn_pure with
  | h p =>
    rw [reindex_pure, contrStd_pure, contrStd_pure]
    congr 1
    exact Equiv.prod_comp e.symm fun j => S.contr (a j) (p (.inr (.inl j)) ⊗ₜ p (.inr (.inr j)))
  | hsmul r u hu => rw [map_smul, map_smul, hu, map_smul]
  | hadd u u' hu hu' => rw [map_add, map_add, hu, hu', map_add]

/-!

### B.2. Two contractions are one

-/

/-- The pairs of two contractions in sequence, `σ₁` and then `σ₂`, as one choice of pairs
`J₁ ⊕ J₂`, the pairs `J₁` of `σ₁` followed by the pairs `J₂` of `σ₂`. -/
noncomputable def _root_.Tensors.ColorEquiv.chain {c : ι₁ → Color K} {c₁ : κ₁ → Color K}
    {c' : κ → Color K} {a₁ : J₁ → Color K} {a₂ : J₂ → Color K}
    (σ₁ : ColorEquiv c (contrColors c₁ a₁)) (σ₂ : ColorEquiv c₁ (contrColors c' a₂)) :
    ColorEquiv c (contrColors c' (prodColors a₁ a₂)) :=
  σ₁.trans ((σ₂.sumCongr (.refl _)).trans ⟨(Equiv.sumAssoc _ _ _).trans
    (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumComm _ _).trans (Equiv.sumSumSumComm _ _ _ _))),
    by rintro (_ | (_ | _) | (_ | _)) <;> rfl⟩)

/-- Two contractions in sequence are one contraction, along `σ₁.chain σ₂`. Contracting `μ` and
then `ν` in `T^μ_μ^ν_ν` is contracting both pairs at once. -/
lemma contr_contr [Fintype J₁] [Fintype J₂] {c₁ : κ₁ → Color K} {a₁ : J₁ → Color K}
    {a₂ : J₂ → Color K} (σ₁ : ColorEquiv c (contrColors c₁ a₁))
    (σ₂ : ColorEquiv c₁ (contrColors c' a₂)) (t : S.Tensor c) :
    contr σ₂ (contr σ₁ t) = contr (σ₁.chain σ₂) t := by
  induction t using inductionOn_pure with
  | h f =>
    simp only [contr_pure, map_smul, smul_smul, Fintype.prod_sum_type, LinearEquiv.cast_apply,
      cast_cast]
    rfl
  | hsmul r t ht => rw [map_smul, map_smul, ht, map_smul]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-!

### B.3. Products with a tensor that is not contracted

-/

/-- The pairs `σ` of `T`, as pairs of `T ⊗ U`. The indices of `U`, on the slots `ι₂` with the
colors `d`, remain after those of `T` that are not contracted. -/
noncomputable def _root_.Tensors.ColorEquiv.withSpectators {c : ι₁ → Color K} {c' : κ → Color K}
    {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) (d : ι₂ → Color K) :
    ColorEquiv (prodColors c d) (contrColors (prodColors c' d) a) :=
  (σ.sumCongr (.refl d)).trans ((ColorEquiv.sumAssoc _ _ _).trans
    (((ColorEquiv.refl c').sumCongr (ColorEquiv.sumComm _ _)).trans
      (ColorEquiv.sumAssoc _ _ _).symm))

/-- Contracting indices of `T` and then multiplying by `U` is contracting the same indices of
`T ⊗ U`, `(T^μ_μν) U^ρ = (T ⊗ U)^μ_μν^ρ`. -/
lemma tmulEquiv_contr [Fintype J] {a : J → Color K} {d : ι₂ → Color K}
    (σ : ColorEquiv c (contrColors c' a)) (t : S.Tensor c) (u : S.Tensor d) :
    S.tmulEquiv c' d (contr σ t ⊗ₜ u) =
      contr (σ.withSpectators d) (S.tmulEquiv c d (t ⊗ₜ u)) := by
  induction t using inductionOn_pure with
  | hsmul r t ht => simp only [map_smul, ← smul_tmul', ht]
  | hadd x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | h p =>
    induction u using inductionOn_pure with
    | hsmul r u hu => simp only [map_smul, tmul_smul, hu]
    | hadd x y hx hy => simp only [map_add, tmul_add, hx, hy]
    | h p' =>
      rw [contr_pure, ← smul_tmul', map_smul, tmulEquiv_pure, tmulEquiv_pure, contr_pure]
      congr 1
      exact congrArg (PiTensorProduct.tprod k) (funext fun y => by rcases y with x | m <;> rfl)

/-!

## C. The product of two tensors on two slots

-/

/-- The pair of the product `M^μ_ν N^ν_ρ` of two tensors on two slots, the second slot of `M`, of
color `c`, with the first slot of `N`, of color `c.dual`. The slots of `μ` and `ρ` remain, as `0`
and `1`. -/
def _root_.Tensors.ColorEquiv.matMul (a c b : Color K) :
    ColorEquiv (prodColors ![a, c] ![c.dual, b]) (contrColors ![a, b] fun _ : Unit => c) where
  toEquiv.toFun
    | .inl 0 => .inl 0 | .inl 1 => .inr (.inl ()) | .inr 0 => .inr (.inr ()) | .inr 1 => .inl 1
  toEquiv.invFun
    | .inl 0 => .inl 0 | .inl 1 => .inr 1 | .inr (.inl ()) => .inl 1 | .inr (.inr ()) => .inr 0
  toEquiv.left_inv := by decide
  toEquiv.right_inv := by decide

/-- The contraction `M^μ_ν N^ν_ρ` of two tensors on two slots. It is `M` with its second factor
mapped by `N`, read through `S.contr c` as the linear map `v_ν ↦ v_ν N^ν_ρ`. -/
lemma contr_matMul (a c b : Color K) (M : S.V a ⊗[k] S.V c) (N : S.V c.dual ⊗[k] S.V b) :
    contr (ColorEquiv.matMul a c b)
        (S.tmulEquiv _ _ (S.twoSlotEquiv a c M ⊗ₜ S.twoSlotEquiv _ b N)) =
      S.twoSlotEquiv a b ((pairingToLinearMap (S.contr c).toLinearMap N).lTensor _ M) := by
  induction M using TensorProduct.inductionOn with
  | add M M' hM hM' => simp only [map_add, add_tmul, hM, hM']
  | tmul m₁ m₂ =>
  induction N using TensorProduct.inductionOn with
  | add N N' hN hN' =>
    simp only [map_add, tmul_add, LinearMap.lTensor_add, LinearMap.add_apply, hN, hN']
  | tmul n₁ n₂ =>
    simp only [twoSlotEquiv_tmul, tmulEquiv_pure, contr_pure, Fintype.prod_unique,
      LinearMap.lTensor_tmul, pairingToLinearMap_tmul, tmul_smul, map_smul]
    congr 2
    funext j
    fin_cases j <;> rfl

/-!

## D. Components

-/

/-- The components of a contraction, as `(tr T)^ρ = ∑ μ ν, C_μ^ν T^ρμ_ν` for a trace. The labels
`μ` and `ν` run over the first and the second slots of the pairs, `C_μ^ν` is the product over the
pairs of `S.contr (a j) (e_μ ⊗ e^ν)`, and the components of `T` are those of `S.reindex σ T`. -/
lemma tensorBasis_repr_contr [Fintype κ] [Fintype J] [DecidableEq J]
    {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) (t : S.Tensor c)
    (φ : Π x, basisIdx (c' x).kind) :
    (S.tensorBasis c').repr (contr σ t) φ =
      ∑ μ : Π j, basisIdx (a j).kind, ∑ ν : Π j, basisIdx (a j).dual.kind,
        (∏ j, S.contr (a j) (S.basis (a j) (μ j) ⊗ₜ S.basis (a j).dual (ν j))) *
          (S.tensorBasis (contrColors c' a)).repr (S.reindex σ t) (Sum.rec φ (Sum.rec μ ν)) := by
  simp only [contr, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  generalize S.reindex σ t = u
  induction u using inductionOn_pure with
  | hsmul r u hu =>
    simp only [map_smul, Finsupp.smul_apply, hu, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  | hadd u u' hu hu' =>
    simp only [map_add, Finsupp.add_apply, hu, hu', mul_add, Finset.sum_add_distrib]
  | h f =>
    -- Each contraction of a pair is expanded in components, and the product of sums over the
    -- pairs becomes a sum over the families of labels `μ` and `ν`.
    rw [contrStd_pure, map_smul, Finsupp.smul_apply, tensorBasis_repr_pure, smul_eq_mul,
      Finset.prod_congr rfl fun j _ => contr_tmul_eq_sum_basis (a j) _ _, Fintype.prod_sum]
    simp only [tensorBasis_repr_pure, Fintype.prod_sum_type, Fintype.prod_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    simp only [Finset.prod_mul_distrib]
    ring

/-- The components of a contraction in dual bases, as `(tr T)^ρ = ∑ μ, T^ρμ_μ` for a trace. When
the bases of each pair are dual, `S.contr (a j) (e_μ ⊗ e^ν)` is `1` for `μ = ν` and `0` otherwise,
and the double sum of `tensorBasis_repr_contr` has one label per pair. -/
lemma tensorBasis_repr_contr_of_dual [Fintype κ] [Fintype J] [DecidableEq J]
    {a : J → Color K} (σ : ColorEquiv c (contrColors c' a)) (t : S.Tensor c)
    (φ : Π x, basisIdx (c' x).kind)
    (h : ∀ j μ ν, S.contr (a j) (S.basis (a j) μ ⊗ₜ S.basis (a j).dual ν) =
      if μ = ν then 1 else 0) :
    (S.tensorBasis c').repr (contr σ t) φ = ∑ μ : Π j, basisIdx (a j).kind,
      (S.tensorBasis (contrColors c' a)).repr (S.reindex σ t) (Sum.rec φ (Sum.rec μ μ)) := by
  simp only [tensorBasis_repr_contr, h, Finset.prod_boole, Finset.mem_univ, forall_const,
    ← funext_iff, boole_mul, Fintype.sum_ite_eq]

end Tensor

end Species

end Tensors
