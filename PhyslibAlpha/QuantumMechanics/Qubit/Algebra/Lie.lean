/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Qubit.Algebra.PauliVector
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Lie
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# The traceless qubit Lie algebra

The Pauli vector identifies the cross product with the normalized observable Lie bracket.

## i. Overview

Alpha uses the bracket `⁅a, b⁆ = -(i / 2)(ab - ba)`. With this convention
`τ v = σ v` preserves the cross product. The map is injective and gives a Lie algebra
isomorphism onto its range. This range models the traceless qubit observables.
The observable bracket is a scoped instance from `selfAdjoint`.

## ii. Key results

`Qubit.τ_lie_eq`, `Qubit.τ_injective` and `Qubit.τLieEquiv`.

## iii. Table of contents

- A. The Pauli vector as an observable
- B. `τ` is a Lie algebra isomorphism onto its range

## iv. References

The imported modules provide the underlying algebraic and analytic results.

-/

@[expose] public section

/-! ## A. The Pauli vector as an observable -/

open scoped ComplexOrder CStarAlgebra Matrix selfAdjoint
open Module ProbabilisticTheory selfAdjoint

namespace Qubit

variable {A : Type*} [CStarAlgebra A] [QubitAlgebra A]

/-- The Pauli vector as an observable for Alpha's normalized Lie bracket. -/
noncomputable def τ (v : Fin 3 → ℝ) : Observable A :=
  ⟨σ v, isSelfAdjoint_σ v⟩

private lemma coe_τ (v : Fin 3 → ℝ) : (τ (A := A) v : A) = σ v := rfl

/-- The Pauli vector intertwines the cross product with Alpha's normalized observable bracket. -/
lemma τ_lie_eq (u v : Fin 3 → ℝ) :
    (⁅τ (A := A) u, τ (A := A) v⁆ : Observable A) = τ (u ⨯₃ v) := by
  apply Subtype.ext
  rw [coe_bracket, coe_τ, coe_τ, coe_τ, σ_commutator, smul_smul]
  have h : -(Complex.I / 2) * (2 * Complex.I) = 1 := by
    ring_nf
    simp [Complex.I_sq]
  rw [h, one_smul]

/-! ## B. `τ` is a Lie algebra isomorphism onto its range

The intertwining identity `τ_lie_eq` above only says `τ` preserves the bracket; an
isomorphism additionally needs `τ` to be injective (surjectivity onto its own range is
tautological). This section supplies that, and packages the result as a genuine
`LieEquiv ℝ (Fin 3 → ℝ) τHom.range` — `ℝ³` (with the cross product) *is* `su(2)`, realized
concretely as the traceless self-adjoint generators, not just related to it by an unpackaged
bracket-compatible map.
-/

/-- `τ` is additive. -/
lemma τ_add (u v : Fin 3 → ℝ) : (τ (A := A) (u + v) : Observable A) = τ u + τ v := by
  apply Subtype.ext
  rw [AddSubgroup.coe_add, coe_τ, coe_τ, coe_τ, σ_add]

/-- `τ` is ℝ-homogeneous. -/
lemma τ_smul (r : ℝ) (v : Fin 3 → ℝ) : (τ (A := A) (r • v) : Observable A) = r • τ v := by
  apply Subtype.ext
  rw [coe_τ, σ_smul, real_smul_eq_ofReal_smul, selfAdjoint.val_smul, coe_τ,
    real_smul_eq_ofReal_smul]

/-- The three generators are linearly independent over `ℂ`: a sub-family of the basis
`QubitAlgebra.pauliBasis`. -/
private lemma gen_linearIndependent :
    LinearIndependent ℂ (fun i => (QubitAlgebra.gen (A := A) i : A)) := by
  have h := (QubitAlgebra.pauliBasis (A := A)).linearIndependent
  rw [QubitAlgebra.pauliBasis_eq] at h
  exact h.comp Fin.succ (Fin.succ_injective 3)

/-- `σ` is injective: it is exactly the coordinates against the (linearly independent) Pauli
generators. -/
private lemma σ_eq_zero_iff (v : Fin 3 → ℝ) : (σ v : A) = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hg := Fintype.linearIndependent_iff.mp (gen_linearIndependent (A := A))
      (fun i => (v i : ℂ)) (by rw [σ] at h; exact h)
    funext i
    exact_mod_cast hg i
  · rintro rfl
    simp [σ]

/-- `τ` is injective: `su(2)` really is `3`-dimensional, not a further quotient of it. -/
lemma τ_injective : Function.Injective (τ (A := A)) := by
  intro u v huv
  have hcoe : (τ (A := A) u : A) = (τ (A := A) v : A) := by rw [huv]
  rw [coe_τ, coe_τ] at hcoe
  have hσ : (σ u : A) = σ v := hcoe
  have h0 : (σ (u - v) : A) = 0 := by
    rw [sub_eq_add_neg, σ_add, σ_neg, hσ, add_neg_cancel]
  exact sub_eq_zero.mp ((σ_eq_zero_iff (u - v)).mp h0)

attribute [local instance] Cross.lieRing

/-- `Fin 3 → ℝ`, with the cross product as its bracket, is a Lie *algebra* over `ℝ`, not just a
Lie ring: the cross product is `ℝ`-bilinear, `crossProduct` already being an `ℝ`-linear map in
each argument. -/
noncomputable instance : LieAlgebra ℝ (Fin 3 → ℝ) where
  lie_smul r x y := (crossProduct x).map_smul r y

/-- `τ`, bundled as a genuine morphism of Lie algebras: `ℝ`-linear (`τ_add`/`τ_smul`) and
bracket-compatible (`τ_lie_eq`, using that `⁅u, v⁆ = u ⨯₃ v` on `Fin 3 → ℝ` (`Cross.lieRing`) and
`Observable A`'s own bracket on `Observable A`). -/
noncomputable def τHom : (Fin 3 → ℝ) →ₗ⁅ℝ⁆ Observable A where
  toFun := τ
  map_add' := τ_add
  map_smul' r v := by simp [τ_smul r v]
  map_lie' {u v} := (τ_lie_eq u v).symm

/-- **`ℝ³` (with the cross product) is `su(2)`**: `τHom` is injective, hence a Lie algebra
isomorphism onto its range — the traceless self-adjoint qubit generators. This is the genuine
isomorphism promised by the module docstring, not just the bracket-intertwining fact `τ_lie_eq`
on its own. -/
noncomputable def τLieEquiv : (Fin 3 → ℝ) ≃ₗ⁅ℝ⁆ (τHom (A := A)).range :=
  LieEquiv.ofInjective τHom τ_injective

end Qubit
