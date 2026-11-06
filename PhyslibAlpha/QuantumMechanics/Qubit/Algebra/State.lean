/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Qubit.Algebra.Basic
public import PhyslibAlpha.ProbabilisticTheory.State.Basic

/-!
# Abstract qubit Bloch expectation vectors

A state gives a real Bloch vector through its Pauli expectation values.

## i. Overview

States use Alpha's existing notation `𝓢[ℂ, A]` for normalized positive linear functionals.
The Bloch coordinates are the real parts of their expectation values on the Pauli generators.
The norm bound and the equivalence with the Bloch ball remain separate results.

## ii. Key results

`Qubit.r`.

## iii. Table of contents

- A. Pauli expectation values

## iv. References

The imported modules provide the underlying algebraic results.

-/

@[expose] public section

/-! ## A. Pauli expectation values -/

open ProbabilisticTheory
open scoped ComplexOrder

namespace Qubit

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [QubitAlgebra A]

/-- The Bloch vector of an abstract state, given by its Pauli expectation values. -/
noncomputable def r (ω : 𝓢[ℂ, A]) : Fin 3 → ℝ :=
  fun i => (ω (QubitAlgebra.gen (A := A) i : A)).re

end Qubit
