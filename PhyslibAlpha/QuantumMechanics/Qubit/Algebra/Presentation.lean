/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.StdBasis

/-!
# An algebraic model of the Pauli relations

Complex quaternion coordinates give an associative algebra with a Pauli basis.

## i. Overview

The generators are `i` times the three standard quaternion units. They square to one
and satisfy the cyclic Pauli relations. A coordinate equivalence proves the basis property.
This construction supplies an algebraic model. It does not yet supply a C⋆-norm or
a `QubitAlgebra` instance. No universal property of a generators-and-relations quotient
is asserted.

## ii. Key results

`Qubit.Presentation.gen_sq`, `gen_mul_cyc` and `pauliBasis_eq`.

## iii. Table of contents

- A. An algebraic model of the Pauli relations

## iv. References

The imported modules provide the underlying algebraic and analytic results.

-/

@[expose] public section

/-! ## A. An algebraic model of the Pauli relations -/

open Module

namespace Qubit

namespace Presentation

/-- The concrete algebra presented by the Pauli relations: Hamilton's quaternions with complex
coefficients, `i² = j² = k² = -1`, `ij = k = -ji`, cyclically. See the module docstring for why
`gen`, defined below, satisfies the Pauli relations in this algebra. -/
abbrev PauliAlgebra := QuaternionAlgebra ℂ (-1) 0 (-1)

/-- The three Pauli generators inside `PauliAlgebra`: `I` times the three quaternion units. -/
def gen : Fin 3 → PauliAlgebra :=
  ![⟨0, Complex.I, 0, 0⟩, ⟨0, 0, Complex.I, 0⟩, ⟨0, 0, 0, Complex.I⟩]

@[simp] lemma gen_zero : gen 0 = (⟨0, Complex.I, 0, 0⟩ : PauliAlgebra) := rfl
@[simp] lemma gen_one : gen 1 = (⟨0, 0, Complex.I, 0⟩ : PauliAlgebra) := rfl
@[simp] lemma gen_two : gen 2 = (⟨0, 0, 0, Complex.I⟩ : PauliAlgebra) := rfl

/-- Each generator squares to `1`. -/
lemma gen_sq (i : Fin 3) : gen i * gen i = 1 := by
  fin_cases i <;>
    · ext <;> simp [QuaternionAlgebra.mk_mul_mk, Complex.I_mul_I]

/-- The cyclic Pauli relation: `gen i * gen (i + 1) = I • gen (i + 2)`. -/
lemma gen_mul_cyc (i : Fin 3) : gen i * gen (i + 1) = Complex.I • gen (i + 2) := by
  fin_cases i <;>
    · ext <;> simp [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.smul_mk, Complex.I_mul_I]

/-- The reversed cyclic relation: `gen (i + 1) * gen i = -I • gen (i + 2)`. -/
lemma gen_mul_cyc_symm (i : Fin 3) : gen (i + 1) * gen i = -Complex.I • gen (i + 2) := by
  fin_cases i <;>
    · ext <;> simp [QuaternionAlgebra.mk_mul_mk, QuaternionAlgebra.smul_mk, Complex.I_mul_I]

/-- The linear equivalence exhibiting `1, gen 0, gen 1, gen 2` as coordinates on `PauliAlgebra`:
forward, `c ↦ c 0 • 1 + c 1 • gen 0 + c 2 • gen 1 + c 3 • gen 2`; backward, reading off the four
components (dividing the imaginary parts by `I`, i.e. multiplying by `-I`). -/
def coordEquiv : (Fin 4 → ℂ) ≃ₗ[ℂ] PauliAlgebra :=
  LinearEquiv.ofLinearMap
    { toFun := fun c => (⟨c 0, Complex.I * c 1, Complex.I * c 2, Complex.I * c 3⟩ : PauliAlgebra)
      map_add' := by intro c c'; ext <;> simp <;> ring
      map_smul' := by intro r c; ext <;> simp <;> ring }
    { toFun := fun q => ![q.re, -Complex.I * q.imI, -Complex.I * q.imJ, -Complex.I * q.imK]
      map_add' := by intro q q'; ext i; fin_cases i <;> simp <;> ring
      map_smul' := by intro r q; ext i; fin_cases i <;> simp <;> ring }
    (by ext q <;> simp <;> ring_nf <;> simp [Complex.I_sq])
    (by ext c i; fin_cases i <;> simp <;> ring_nf <;> simp [Complex.I_sq])

/-- `1, gen 0, gen 1, gen 2` form a complex basis of `PauliAlgebra` — a genuine theorem, not a
hypothesis: `PauliAlgebra` is (by construction) coordinatized by `Fin 4 → ℂ` via `coordEquiv`,
whose standard basis transports to exactly `Fin.cons 1 gen`. -/
noncomputable def pauliBasis : Basis (Fin 4) ℂ PauliAlgebra :=
  (Pi.basisFun ℂ (Fin 4)).map coordEquiv

/-- The basis `pauliBasis` is exactly `1` followed by the generators. -/
lemma pauliBasis_eq : ⇑pauliBasis = Fin.cons (1 : PauliAlgebra) gen := by
  funext i
  fin_cases i <;> simp [pauliBasis, coordEquiv, Pi.basisFun_apply] <;> rfl

end Presentation

end Qubit
