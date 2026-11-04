/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Elab
public import Physlib.Relativity.Tensors.RealTensor.Metrics.Pre
/-!

# The species of real Lorentz tensors

Real Lorentz tensors in `d + 1` dimensions as a species, with the Minkowski metric `η`.

## i. Overview

Real Lorentz tensors have one kind of index, the vector index `vec`. An upper index has the color
`⟨vec, up⟩` and a lower index the color `⟨vec, down⟩`. A color is a label. The species assigns to
it a space: `V ⟨vec, up⟩ = ContrMod d`, the contravariant vectors `v^μ` with basis `e_μ`, and
`V ⟨vec, down⟩ = CoMod d`, the covariant vectors `w_μ` with basis `e^μ`. Both are copies of
`ℝ^(d+1)`, so `V ⟨vec, up⟩ = ℝ⁴` for `d = 3`. The labels `μ` run over `Fin 1 ⊕ Fin d`, with
`Sum.inl 0` the time direction and `Sum.inr i` the space directions. A Lorentz transformation
`Λ : LorentzGroup d` acts on an upper index by `(Λv)^μ = Λ^μ_ν v^ν` and on a lower index by
`(Λw)_μ = (Λ⁻¹)^ν_μ w_ν`. The two colors are named `realLorentz.up` and `realLorentz.down`, and
`ℝT[d, up, down]` is the space of the tensors `T^μ_ν`, under `open scoped Tensors.realLorentz`.

The contraction `u^μ w_μ` is `ContrMod.contr` and `CoMod.contr`, the delta `δ_μ^ν` is
`ContrMod.unitVal` and `CoMod.unitVal`, and the metric is `η^μν = ContrMod.metricVal` and
`η_μν = CoMod.metricVal`, both with the matrix `diag(1, -1, …, -1)`. The laws of a species and of a
metric are `ContrMod.contr_tmul_symm`, `ContrMod.contr_unit` and `ContrMod.contr_metric` with their
`CoMod` versions, read through `TensorProduct.pairingToLinearMap_apply`.

So the general results apply. For example `η^μν η_νρ = δ^μ_ρ` is
`Species.contr_formTensor_formTensor` at `up`, and lowering an index, `v^μ ↦ v_ν = v^μ η_μν`, is
`(realLorentz d).toDual up`.

A variance stores whether it is up and whether it is down. The fields that pair a color with its
dual match on both booleans and list only the two consistent cases. Lean's `match` closes the other
two from `Variance.ne`.

## ii. Key results

- `realLorentz` : the species of real Lorentz tensors, with the colors `realLorentz.up` and
  `realLorentz.down` and the spaces of tensors `ℝT[d, up, down]` (scoped).
- the instance `(realLorentz d).WithMetric` : the Minkowski metric `η`.
- `realLorentz.contr_basis` : the bases of upper and lower indices are dual.
- `realLorentz.tensorBasis_repr_formTensor` : the components of `η^μν` and `η_μν` are the
  Minkowski matrix.

## iii. Table of contents

- A. The species
- B. The Minkowski metric
- C. Dual bases and components of the metric

## iv. References

-/

@[expose] public section

open TensorProduct Lorentz

namespace Tensors

/-!

## A. The species

-/

/-- The kinds of real Lorentz index. There is one, the vector index `vec`, carried up as `v^μ` and
down as `w_μ`. -/
inductive realLorentz.Kind
  /-- The Lorentz vector index. -/
  | vec

/-- The vector space of a real Lorentz index of color `c`: `ContrMod d` for an upper index and
`CoMod d` for a lower one. A `def` with its own instances, because instance search does not find
the instances of a field written inline once a proof splits the color into cases. -/
def realLorentz.IndexSpace (d : ℕ) (c : Color realLorentz.Kind) : Type :=
  match c.variance.isUp with
  | true => ContrMod d
  | false => CoMod d

noncomputable instance (d : ℕ) : ∀ c, AddCommGroup (realLorentz.IndexSpace d c)
  | ⟨_, ⟨true, _, _⟩⟩ => inferInstanceAs (AddCommGroup (ContrMod d))
  | ⟨_, ⟨false, _, _⟩⟩ => inferInstanceAs (AddCommGroup (CoMod d))

noncomputable instance (d : ℕ) : ∀ c, Module ℝ (realLorentz.IndexSpace d c)
  | ⟨_, ⟨true, _, _⟩⟩ => inferInstanceAs (Module ℝ (ContrMod d))
  | ⟨_, ⟨false, _, _⟩⟩ => inferInstanceAs (Module ℝ (CoMod d))

open realLorentz in
/-- Real Lorentz tensors in `d + 1` dimensions, on `ContrMod d` and `CoMod d` with their
representations, bases, contraction and delta. The labels `Fin 1 ⊕ Fin d` put time first. At a
concrete color each field is the `ContrMod` or `CoMod` one by `rfl`, as in
`(realLorentz d).rep up = ContrMod.rep`. -/
noncomputable abbrev realLorentz (d : ℕ) :
    Species ℝ (LorentzGroup d) Kind (fun _ => Fin 1 ⊕ Fin d) where
  V := IndexSpace d
  rep
    | ⟨_, ⟨true, _, _⟩⟩ => ContrMod.rep
    | ⟨_, ⟨false, _, _⟩⟩ => CoMod.rep
  basis
    | ⟨_, ⟨true, _, _⟩⟩ => contrBasis d
    | ⟨_, ⟨false, _, _⟩⟩ => coBasis d
  contr
    | ⟨_, ⟨true, false, _⟩⟩ => ContrMod.contr
    | ⟨_, ⟨false, true, _⟩⟩ => CoMod.contr
  delta
    | ⟨_, ⟨true, false, _⟩⟩ => ContrMod.unitVal d
    | ⟨_, ⟨false, true, _⟩⟩ => CoMod.unitVal d
  contr_tmul_symm
    | ⟨_, ⟨true, false, _⟩⟩ => ContrMod.contr_tmul_symm
    | ⟨_, ⟨false, true, _⟩⟩ => CoMod.contr_tmul_symm
  snake
    | ⟨_, ⟨true, false, _⟩⟩ => LinearMap.ext fun x => (pairingToLinearMap_apply _ _ x).trans
        (ContrMod.unit_apply_one (d := d) ▸ ContrMod.contr_unit x)
    | ⟨_, ⟨false, true, _⟩⟩ => LinearMap.ext fun x => (pairingToLinearMap_apply _ _ x).trans
        (CoMod.unit_apply_one (d := d) ▸ CoMod.contr_unit x)

namespace realLorentz

/-- The color of an upper Lorentz index, `v^μ`. -/
abbrev up : Color Kind := ⟨.vec, .up⟩

/-- The color of a lower Lorentz index, `w_μ`. -/
abbrev down : Color Kind := ⟨.vec, .down⟩

/-- The real Lorentz tensors in `d + 1` dimensions with the colors listed, as `ℝT[d, up, down]` for
`T^μ_ν`. The colors are read in the namespace `realLorentz`. The notation is scoped: it is active
under `open scoped Tensors.realLorentz`, so it does not clash with `ℝT[…]` of
`RealTensor.Basic`. -/
scoped syntax (name := realLorentzSyntax) "ℝT[" term,+ "]" : term

macro_rules (kind := realLorentzSyntax)
  | `(ℝT[$d]) => `((Tensors.realLorentz $d).Tensor ![])
  | `(ℝT[$d, $cs,*]) => `((Tensors.realLorentz $d).Tensor (open Tensors.realLorentz in ![$cs,*]))

end realLorentz

/-!

## B. The Minkowski metric

-/

open realLorentz in
/-- The Minkowski metric, `η^μν` at an upper color and `η_μν` at a lower one, both with the matrix
`diag(1, -1, …, -1)`: the signature is mostly minus. -/
noncomputable instance (d : ℕ) : (realLorentz d).WithMetric where
  form
    | ⟨_, ⟨true, _, _⟩⟩ => ContrMod.metricVal d
    | ⟨_, ⟨false, _, _⟩⟩ => CoMod.metricVal d
  form_invariant c g := by
    rcases c with ⟨_, _ | _, _, _⟩
    · have h := (LinearMap.congr_fun ((CoMod.metric d).isIntertwining' g) 1).symm
      simp [CoMod.metric_apply_one] at h
      exact h
    · have h := (LinearMap.congr_fun ((ContrMod.metric d).isIntertwining' g) 1).symm
      simp [ContrMod.metric_apply_one] at h
      exact h
  form_inverse c := by
    -- `ContrMod.contr_metric` states `η^μν η_νρ = δ^μ_ρ` with associators, `lid` and `comm`, the
    -- form of `lTensor_pairingToLinearMap_apply`.
    rw [← pairingToLinearMap_lTensor, ← (realLorentz d).snake c,
      (realLorentz d).delta_eq_comm_delta_dual c, lTensor_pairingToLinearMap_apply]
    congr 1
    match c with
    | ⟨_, ⟨true, false, _⟩⟩ =>
      have h := CoMod.contr_metric (d := d)
      rw [ContrMod.metric_apply_one, CoMod.metric_apply_one, CoMod.unit_apply_one] at h
      exact (TensorProduct.comm_comm _ _ _ _).symm.trans (congrArg (TensorProduct.comm ℝ _ _) h)
    | ⟨_, ⟨false, true, _⟩⟩ =>
      have h := ContrMod.contr_metric (d := d)
      rw [ContrMod.metric_apply_one, CoMod.metric_apply_one, ContrMod.unit_apply_one] at h
      exact (TensorProduct.comm_comm _ _ _ _).symm.trans (congrArg (TensorProduct.comm ℝ _ _) h)
  form_symm
    | ⟨_, ⟨true, _, _⟩⟩ => (by simp [ContrMod.metricVal_expand_tmul_minkowskiMatrix] :
        TensorProduct.comm ℝ _ _ (ContrMod.metricVal d) = _)
    | ⟨_, ⟨false, _, _⟩⟩ => (by simp [CoMod.metricVal_expand_tmul_minkowskiMatrix] :
        TensorProduct.comm ℝ _ _ (CoMod.metricVal d) = _)

/-!

## C. Dual bases and components of the metric

-/

namespace realLorentz

/-- The bases of an upper and a lower index are dual: `e_μ(e^ν)` is `1` for `μ = ν` and `0`
otherwise. At a lower color `c` the left factor is `e^μ` and the right `e_ν`. -/
lemma contr_basis (d : ℕ) (c : Color Kind) (μ ν : Fin 1 ⊕ Fin d) :
    (realLorentz d).contr c ((realLorentz d).basis c μ ⊗ₜ (realLorentz d).basis c.dual ν) =
      if μ = ν then 1 else 0 := by
  match c with
  | ⟨_, ⟨true, false, _⟩⟩ => exact ContrMod.contr_basis μ ν
  | ⟨_, ⟨false, true, _⟩⟩ => exact CoMod.contr_basis μ ν

/-- The components of the metric are the Minkowski matrix `diag(1, -1, …, -1)`: at the labels
`![α, β]` they are `η^αβ` at an upper color and `η_αβ` at a lower one. The labels are any
`μ : Fin 2 → Fin 1 ⊕ Fin d`, as in `Species.tensorBasis_repr_twoSlotEquiv`. -/
lemma tensorBasis_repr_formTensor (d : ℕ) (c : Color Kind) (μ : Fin 2 → Fin 1 ⊕ Fin d) :
    ((realLorentz d).tensorBasis ![c, c]).repr ((realLorentz d).formTensor c) μ =
      minkowskiMatrix (μ 0) (μ 1) := by
  rw [Species.formTensor, Species.tensorBasis_repr_twoSlotEquiv]
  rcases c with ⟨_, _ | _, _, _⟩
  · exact congrFun (congrFun (coCoToMatrixRe.apply_symm_apply minkowskiMatrix) (μ 0)) (μ 1)
  · exact congrFun (congrFun (contrContrToMatrixRe.apply_symm_apply minkowskiMatrix) (μ 0)) (μ 1)

/-- `η^00 = 1` and `η^11 = -1` in `3 + 1` dimensions: the signature is mostly minus. -/
example : ((realLorentz 3).tensorBasis ![up, up]).repr ((realLorentz 3).formTensor up)
      ![.inl 0, .inl 0] = 1 ∧
    ((realLorentz 3).tensorBasis ![up, up]).repr ((realLorentz 3).formTensor up)
      ![.inr 0, .inr 0] = -1 := by
  simp [tensorBasis_repr_formTensor, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]

/-- `η_μν η^μν = d + 1`: contracting both indices of `η_μν` with those of `η^μν` gives the number
of dimensions. -/
example (d : ℕ) : ((realLorentz d).tensorBasis ![]).repr
    {(realLorentz d).formTensor down | μ ν ⊗ (realLorentz d).formTensor up | μ ν}ᵀ
    (fun i => i.elim0) = d + 1 := by
  rw [Species.Tensor.tensorBasis_repr_contr_of_dual _ _ _ fun _ => contr_basis d _]
  simp only [Species.tensorBasis_repr_reindex, Species.tensorBasis_repr_tmulEquiv,
    tensorBasis_repr_formTensor]
  -- The labels of `η` are casts of `ν (.inl ())` and `ν (.inr ())`, equal to them by `rfl`.
  change ∑ ν : Unit ⊕ Unit → Fin 1 ⊕ Fin d, minkowskiMatrix (ν (.inl ())) (ν (.inr ())) *
    minkowskiMatrix (ν (.inl ())) (ν (.inr ())) = d + 1
  rw [← ((Equiv.sumArrowEquivProdArrow Unit Unit _).trans ((Equiv.funUnique Unit _).prodCongr
    (Equiv.funUnique Unit _))).symm.sum_comp, Fintype.sum_prod_type]
  simp [minkowskiMatrix.as_diagonal, Matrix.diagonal_apply, Fintype.sum_sum_type, add_comm]


/-- `ℝT[3, up, down]` is the space of tensors `T^μ_ν` in four dimensions. -/
example : ℝT[3, up, down] = (realLorentz 3).Tensor ![up, down] := rfl
end realLorentz

end Tensors
