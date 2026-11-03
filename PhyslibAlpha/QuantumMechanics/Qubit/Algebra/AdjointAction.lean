/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Qubit.Algebra.Dynamics
public import PhyslibAlpha.QuantumMechanics.Qubit.Algebra.Lie

/-!
# The abstract qubit adjoint generator

The traceless Hamiltonian defines a cross-product action on Bloch vectors.

## i. Overview

The infinitesimal Bloch action associated with `H = h₀ 1 + σ(h)` is the real-linear map
`v ↦ 2(h × v)`. The scalar part does not occur in this definition. This file recovers the
explicit linear map. A finite rotation action and its derivative are not constructed here.
Alpha normalizes the observable bracket as `-(i / 2)(ab - ba)`. The factor two is retained
for the Hamiltonian convention `exp(-itH)`.

## ii. Key results

`Qubit.adjointAction` and `adjointAction_apply`.

## iii. Table of contents

- A. The Bloch-vector generator

## iv. References

The imported modules provide the underlying algebraic results.

-/

@[expose] public section

/-! ## A. The Bloch-vector generator -/

open ProbabilisticTheory
open scoped Matrix

namespace Qubit

variable {A : Type*} [CStarAlgebra A] [QubitAlgebra A]

/-- The Hamiltonian cross-product generator `v ↦ 2(h × v)` in Bloch coordinates. -/
noncomputable def adjointAction (H : Observable A) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  (2 : ℝ) • crossProduct (observableEquiv H).2

lemma adjointAction_apply (H : Observable A) (v : Fin 3 → ℝ) :
    adjointAction H v = (2 : ℝ) • ((observableEquiv H).2 ⨯₃ v) := rfl

end Qubit
