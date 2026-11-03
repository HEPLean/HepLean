/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Qubit.Algebra.Observable
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Abstract qubit unitary predicates

Rotations, scalar unitaries and special unitaries describe the intended Bloch action.

## i. Overview

A rotation preserves the Euclidean norm and has determinant one. Scalar unitaries are
complex phases times the identity. Special unitaries have determinant one in the abstract
Pauli coordinates. These predicates do not assert the existence of the rotation action
or the double-cover theorem.

## ii. Key results

`Qubit.IsRotation`, `IsScalarUnitary` and `IsSpecialUnitary`.

## iii. Table of contents

- A. Rotation and unitary predicates

## iv. References

The imported modules provide the underlying algebraic results.

-/

@[expose] public section

/-! ## A. Rotation and unitary predicates -/

namespace Qubit

/-- A real-linear rotation preserves the Euclidean norm and has determinant one. -/
def IsRotation (f : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) : Prop :=
  (∀ v, ‖(WithLp.toLp 2 (f v) : EuclideanSpace ℝ (Fin 3))‖ =
    ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖) ∧ LinearMap.det f = 1

variable {A : Type*} [CStarAlgebra A]

/-- A scalar unitary is a complex phase times the identity. -/
def IsScalarUnitary (U : unitary A) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ (U : A) = c • 1

/-- A special qubit unitary has determinant one in the abstract Pauli coordinates. -/
def IsSpecialUnitary [QubitAlgebra A] (U : unitary A) : Prop :=
  det (U : A) = 1

end Qubit
