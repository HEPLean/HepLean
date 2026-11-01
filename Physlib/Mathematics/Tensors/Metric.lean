/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Contraction
/-!

# Invariant forms, metrics, and lowering and raising indices

An invariant form takes an index to its dual color, lowering an upper index and raising a lower
one.

## i. Overview

For Lorentz tensors `V ⟨vec, up⟩ = ℝ⁴` and `V ⟨vec, down⟩ = (ℝ⁴)*`. The Minkowski metric is the
element `η_μν e^μ ⊗ e^ν` of the space `(ℝ⁴)* ⊗ (ℝ⁴)*`, and its inverse is the element
`η^μν e_μ ⊗ e_ν` of `ℝ⁴ ⊗ ℝ⁴`. They lower and raise indices, `v_ν = v^μ η_μν` and
`w^ν = w_μ η^μν`, and they are inverse to each other, `v^μ η_μν η^νρ = v^ρ`.

An invariant form on a species `S`, the class `S.WithInvariantForm`, gives such a pair for every
color. The form `form c` is an element of `V c ⊗ V c`, written `g^μν` at an upper color and `g_μν`
at a lower one. It is invariant under the group, and the forms at `c` and at `c.dual` are inverse
to each other. A metric, the class `S.WithMetric`, is an invariant form that is symmetric,
`g_μν = g_νμ`, as `η`. The Weyl `ε` is an invariant form that is antisymmetric, so it is not a
metric.

The form is a choice, since `-η` serves as well as `η`. Given `g_μν`, its inverse `g^μν` is unique
(`form_inverse_unique`). The scalars `k` are only a commutative ring, over which a non-degenerate
form need not have an inverse, so the class stores the inverse and the law `form_inverse` checks
it.

`S.toDual c : V c ≃ V c.dual` contracts a vector with the first index of the form at `c.dual`. At
an upper color it lowers the index, `v^μ ↦ v^μ g_μν`, and at a lower color it raises it,
`w_μ ↦ w_μ g^μν`. Its inverse is `S.toDual c.dual`, by `rfl` (`toDual_symm`).

For a symmetric metric such as `η` the first index gives the textbook `v_ν = η_νμ v^μ`, as
`TensorSpecies.Tensor.toDualMapAtIndex` does. For the antisymmetric `ε` it gives
`ψ_β = ψ^α ε_αβ = -ε_βα ψ^α`. With `ε^12 = ε_21 = 1` this is minus the convention
`ψ_α = ε_αβ ψ^β`, so a Weyl species following that convention stores `-ε`.

`S.toDualAt i hi h` lowers or raises the index at the slot `i` of a tensor and keeps the others, as
in `T^μν ↦ T^μ_ν` for `i` the second slot. The caller states the colors `c'` of the result, such as
`![⟨vec, up⟩, ⟨vec, down⟩]`. The hypothesis `hi` says that `c'` has the dual color at `i`, and `h`
that it agrees with the colors `c` of the tensor elsewhere.

`S.formTensor c` is the form as a tensor on two slots, `η^μν` at `⟨vec, up⟩` and `η_μν` at
`⟨vec, down⟩`. The law `form_inverse` stated for tensors is `g^μν g_νρ = δ^μ_ρ`
(`contr_formTensor_formTensor`). Lowering an index is contracting it with the form,
`M^μν g_νρ = M^μ_ρ` (`toDualAt_eq_contr_formTensor`).

## ii. Key results

- `Species.WithInvariantForm` : an invariant form with its inverse, `g_μν` and `g^μν`.
- `Species.WithMetric` : a symmetric invariant form, `g_μν = g_νμ`.
- `Species.toDual` : `S.V c ≃ S.V c.dual`, lowering an upper index and raising a lower one.
- `Species.toDual_symm` : raising is the inverse of lowering.
- `Species.form_inverse_unique` : `g^μν` is determined by `g_μν`.
- `Species.toDual_rep`, `Species.toDualAt_smul` : `(Λv)_ν = Λ(v_ν)`, at one index of a tensor.
- `Species.toDualAt` : lowering or raising the index at one slot of a tensor.
- `Species.toDualAt_toDualAt` : raising at a slot undoes lowering there.
- `Species.toDualAt_twoSlotEquiv` : lowering the second index of a tensor on two slots,
  `M^μν ↦ M^μ_ν`, is `toDual` on the second factor.
- `Species.toDualAt_eq_contr_formTensor` : lowering is contracting with the form,
  `M^μν g_νρ = M^μ_ρ`.
- `Species.formTensor`, `Species.formTensor_invariant` : the form as an invariant tensor on two
  slots.
- `Species.contr_formTensor_formTensor` : `g^μν g_νρ = δ^μ_ρ`.

## iii. Table of contents

- A. Invariant forms and metrics
- B. Lowering and raising vectors
- C. Lowering and raising at one index
- D. The form as a tensor

## iv. References

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace Tensors

namespace Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)]

/-!

## A. Invariant forms and metrics

-/

/-- An invariant form on a species: for every color `c` an invariant element `g` of `V c ⊗ V c`,
`g^μν` at an upper color and `g_μν` at a lower one, with the forms at `c` and at `c.dual` inverse
to each other. It need not be symmetric, so it covers both `η` and the Weyl `ε`. Every color must
carry one, so a species containing the SU(3) triplet has none. The invariance at `c.dual` follows
from that at `c` and `form_inverse`, but a field for every color cannot state only half. -/
class WithInvariantForm (S : Species k G K basisIdx) where
  /-- The form at the color `c`, an element of `V c ⊗ V c`. -/
  form : (c : Color K) → S.V c ⊗[k] S.V c
  /-- The form is invariant, `Λ g = g` for every `Λ : G`. -/
  form_invariant : ∀ c (Λ : G), TensorProduct.map (S.rep c Λ) (S.rep c Λ) (form c) = form c
  /-- The forms at `c` and at `c.dual` are inverse to each other, `v^μ g_μν g^νρ = v^ρ` at an
  upper color `c`. The vector is contracted with the first index of each form. -/
  form_inverse : ∀ c, pairingToLinearMap (S.contr c.dual).toLinearMap (form c) ∘ₗ
    pairingToLinearMap (S.contr c).toLinearMap (form c.dual) = LinearMap.id

export WithInvariantForm (form form_invariant form_inverse)

/-- A metric on a species: an invariant form that is symmetric at every color, as `η`. -/
class WithMetric (S : Species k G K basisIdx) extends S.WithInvariantForm where
  /-- The form is symmetric, `g_μν = g_νμ`. -/
  form_symm : ∀ c, TensorProduct.comm k (S.V c) (S.V c) (form c) = form c

variable {S : Species k G K basisIdx} [S.WithInvariantForm]

/-!

## B. Lowering and raising vectors

-/

variable (S) in
/-- The vector `v` of color `c` contracted with the first index of the form at `c.dual`. It lowers
an upper index, `v^μ ↦ v^μ g_μν`, and raises a lower one, `w_μ ↦ w_μ g^μν`. -/
noncomputable def toDual (c : Color K) : S.V c ≃ₗ[k] S.V c.dual :=
  LinearEquiv.ofLinearMap (pairingToLinearMap (S.contr c).toLinearMap (form c.dual))
    (pairingToLinearMap (S.contr c.dual).toLinearMap (form c))
    (WithInvariantForm.form_inverse c.dual) (WithInvariantForm.form_inverse c)

lemma toDual_apply (c : Color K) (v : S.V c) :
    S.toDual c v = pairingToLinearMap (S.contr c).toLinearMap (form c.dual) v := rfl

/-- Raising is the inverse of lowering: the inverse of `S.toDual c` is `S.toDual c.dual`. -/
lemma toDual_symm (c : Color K) : (S.toDual c).symm = S.toDual c.dual := rfl

/-- The inverse of the form is unique: an element `N` of `V c.dual ⊗ V c.dual` inverse to the form
at `c` is the form at `c.dual`. -/
lemma form_inverse_unique (c : Color K) {N : S.V c.dual ⊗[k] S.V c.dual}
    (h : pairingToLinearMap (S.contr c.dual).toLinearMap (form c) ∘ₗ
      pairingToLinearMap (S.contr c).toLinearMap N = LinearMap.id) :
    N = form c.dual :=
  S.pairingToLinearMap_contr_injective c ((S.toDual c).toLinearMap_symm_comp_eq _ _ |>.1 h)

/-- Lowering and raising commute with the group action, `(Λv)_ν = Λ(v_ν)`. -/
lemma toDual_rep (c : Color K) (g : G) (v : S.V c) :
    S.toDual c (S.rep c g v) = S.rep c.dual g (S.toDual c v) := by
  rw [toDual_apply, toDual_apply, ← S.pairingToLinearMap_contr_map_rep c g, form_invariant]

/-!

## C. Lowering and raising at one index

-/

variable {ι : Type} [DecidableEq ι]

variable (S) in
/-- `S.toDual` at the slot `i` of a tensor and the identity at the other slots, as in
`T^μν ↦ T^μ_ν` for `i` the second slot. The colors `c'` of the result have the dual color at `i`
by `hi` and agree with `c` elsewhere by `h`. It is Mathlib's `PiTensorProduct.congr`. -/
noncomputable def toDualAt {c c' : ι → Color K} (i : ι) (hi : c' i = (c i).dual)
    (h : ∀ x, x ≠ i → c x = c' x) : S.Tensor c ≃ₗ[k] S.Tensor c' :=
  -- At the slot `i` the map to the dual color, moved along `hi`. At every other slot `x` the
  -- identity, moved along `h x`.
  S.toPiTensor c ≪≫ₗ PiTensorProduct.congr (fun x => if hx : x = i then
      hx ▸ (S.toDual (c i) ≪≫ₗ LinearEquiv.cast (M := S.V) hi.symm)
    else LinearEquiv.cast (M := S.V) (h x hx)) ≪≫ₗ (S.toPiTensor c').symm

/-- Lowering or raising at a slot commutes with the group action, `(ΛT)^μ_ν = Λ(T^μ_ν)`. -/
lemma toDualAt_smul {c c' : ι → Color K} (i : ι) (hi : c' i = (c i).dual)
    (h : ∀ x, x ≠ i → c x = c' x) (g : G) (t : S.Tensor c) :
    S.toDualAt i hi h (g • t) = g • S.toDualAt i hi h t :=
  map_smul_of_pure (S.toDualAt i hi h) g (fun p => by
    simp only [smul_pure, toDualAt, LinearEquiv.trans_apply, toPiTensor_pure,
      PiTensorProduct.congr_tprod, toPiTensor_symm_tprod]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx
      simp only [dite_true, LinearEquiv.trans_apply, toDual_rep, cast_rep]
    · simp only [hx, dite_false, cast_rep]) t

/-- On a pure tensor, `toDualAt` applies `toDual` to the vector at `i` and keeps the others. The
result `q` is explicit, so that for concrete colors `hqi` and `hq` hold by `rfl`. -/
lemma toDualAt_pure {c c' : ι → Color K} (i : ι) (hi : c' i = (c i).dual)
    (h : ∀ x, x ≠ i → c x = c' x) (p : Π x, S.V (c x)) (q : Π x, S.V (c' x))
    (hqi : q i = LinearEquiv.cast (R := k) (M := S.V) hi.symm (S.toDual (c i) (p i)))
    (hq : ∀ x (hx : x ≠ i), q x = LinearEquiv.cast (R := k) (M := S.V) (h x hx) (p x)) :
    S.toDualAt i hi h (S.pure p) = S.pure q := by
  simp only [toDualAt, LinearEquiv.trans_apply, toPiTensor_pure, PiTensorProduct.congr_tprod,
    toPiTensor_symm_tprod]
  congr 1
  funext x
  by_cases hx : x = i
  · subst hx
    simp [hqi]
  · simp [hx, hq x hx]

/-- Raising at a slot undoes lowering at that slot, `(T^μ_ν)^ν = T^μν`. -/
lemma toDualAt_toDualAt {c c' : ι → Color K} (i : ι) (hi : c' i = (c i).dual)
    (h : ∀ x, x ≠ i → c x = c' x) (t : S.Tensor c) :
    S.toDualAt (c := c') (c' := c) i (by rw [hi]) (fun x hx => (h x hx).symm)
      (S.toDualAt i hi h t) = t := by
  induction t using inductionOn_pure with
  | h p =>
    simp only [toDualAt, LinearEquiv.trans_apply, toPiTensor_pure, PiTensorProduct.congr_tprod,
      toPiTensor_symm_tprod]
    congr 1
    funext x
    by_cases hx : x = i
    · subst hx
      simp only [dite_true, LinearEquiv.trans_apply]
      generalize_proofs _ h₁ h₂
      revert h₁ h₂ hi
      generalize c' x = d
      rintro h₁ h₂ rfl
      exact (S.toDual _).symm_apply_apply (p x)
    · simp [hx]
  | hsmul r t ht => rw [map_smul, map_smul, ht]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

/-- Lowering or raising the second index of a tensor on two slots, `M^μν ↦ M^μ_ν`, is `toDual` on
the second factor of `M ∈ V a ⊗ V c`. -/
lemma toDualAt_twoSlotEquiv (a c : Color K) (M : S.V a ⊗[k] S.V c) :
    S.toDualAt (c := ![a, c]) (c' := ![a, c.dual]) 1 rfl
      (fun x hx => by fin_cases x <;> simp_all) (S.twoSlotEquiv a c M) =
      S.twoSlotEquiv a c.dual ((S.toDual c).toLinearMap.lTensor _ M) := by
  induction M using TensorProduct.inductionOn with
  | add M M' hM hM' => simp only [map_add, hM, hM']
  | tmul x y =>
    rw [twoSlotEquiv_tmul, LinearMap.lTensor_tmul, twoSlotEquiv_tmul]
    exact toDualAt_pure _ _ _ _ _ rfl
      (fun x hx => by fin_cases x <;> first | rfl | exact absurd rfl hx)

/-!

## D. The form as a tensor

-/

variable (S) in
/-- The form at `c` as a tensor with colors `![c, c]`, `g^μν` at an upper color and `g_μν` at a
lower one. -/
noncomputable def formTensor (c : Color K) : S.Tensor ![c, c] :=
  S.twoSlotEquiv c c (form c)

/-- The form is an invariant tensor: every group element fixes it, as every Lorentz
transformation fixes the Minkowski metric `η`. -/
lemma formTensor_invariant (c : Color K) (Λ : G) : Λ • S.formTensor c = S.formTensor c := by
  rw [formTensor, ← twoSlotEquiv_map_rep, form_invariant]

/-- `g^μν g_νρ = δ^μ_ρ` at an upper color `c`: the second slot of the form at `c` contracted with
the first slot of the form at `c.dual` is the delta. -/
lemma contr_formTensor_formTensor (c : Color K) :
    Tensor.contr (ColorEquiv.matMul c c c.dual)
        (S.tmulEquiv _ _ (S.formTensor c ⊗ₜ S.formTensor c.dual)) =
      S.deltaTensor c.dual := by
  rw [formTensor, formTensor, deltaTensor, Tensor.contr_matMul]
  congr 1
  -- Both tensors in `V c ⊗ V c.dual` act on `V c.dual` as the identity, the first by the law of
  -- the form and the second by the snake law.
  apply S.pairingToLinearMap_contr_injective c.dual
  rw [pairingToLinearMap_lTensor, S.snake c.dual]
  exact form_inverse c.dual

/-- Lowering the second index is contracting it with the form, `M^μν g_νρ = M^μ_ρ` at an upper
color `c`, along `ColorEquiv.matMul`. -/
lemma toDualAt_eq_contr_formTensor (a c : Color K) (M : S.V a ⊗[k] S.V c) :
    S.toDualAt (c := ![a, c]) (c' := ![a, c.dual]) 1 rfl
      (fun x hx => by fin_cases x <;> simp_all) (S.twoSlotEquiv a c M) =
      Tensor.contr (ColorEquiv.matMul a c c.dual)
        (S.tmulEquiv _ _ (S.twoSlotEquiv a c M ⊗ₜ S.formTensor c.dual)) := by
  rw [toDualAt_twoSlotEquiv, formTensor, Tensor.contr_matMul]
  rfl

end Species

end Tensors
