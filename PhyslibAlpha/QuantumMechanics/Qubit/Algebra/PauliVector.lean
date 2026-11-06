/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Qubit.Algebra.Basic
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# The abstract Pauli vector

Real three-vectors parametrize traceless self-adjoint qubit elements.

## i. Overview

The Pauli product splits into a dot product and a cross product. Bloch vectors use
`Fin 3 → ℝ`. A Euclidean norm must be supplied explicitly when needed.

## ii. Key results

`Qubit.σ_mul_σ`, `Qubit.σ_sq`, `Qubit.σ_commutator` and `Qubit.σ_anticommutator`.

## iii. Table of contents

- A. The Pauli vector
- B. The product formula

## iv. References

The imported modules provide the underlying algebraic and analytic results.

-/

@[expose] public section

/-! ## A. The Pauli vector -/

open scoped ComplexOrder CStarAlgebra Matrix
open ProbabilisticTheory

namespace Qubit

variable {A : Type*} [CStarAlgebra A] [QubitAlgebra A]

/-- The Pauli vector `σ(v) = ∑ᵢ vᵢ genᵢ` associated with `v : Fin 3 → ℝ`. -/
noncomputable def σ (v : Fin 3 → ℝ) : A :=
  ∑ i, (v i : ℂ) • (QubitAlgebra.gen (A := A) i : A)

omit [QubitAlgebra A] in
/-- A real scalar acts on `A` the same way whether taken through `ℝ` directly or through `ℂ`. -/
lemma real_smul_eq_ofReal_smul (x : ℝ) (b : A) : x • b = (x : ℂ) • b := by
  have : (x : ℂ) = algebraMap ℝ ℂ x := by norm_cast
  rw [this, IsScalarTower.algebraMap_smul]

/-- `σ` is additive. -/
lemma σ_add (u v : Fin 3 → ℝ) : (σ (u + v) : A) = σ u + σ v := by
  simp only [σ, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

/-- `σ` is ℝ-homogeneous. -/
lemma σ_smul (r : ℝ) (v : Fin 3 → ℝ) : (σ (r • v) : A) = r • σ v := by
  simp only [σ, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul, real_smul_eq_ofReal_smul,
    Finset.smul_sum]

/-- `σ(v)` is self-adjoint: a real-linear combination of the self-adjoint generators. -/
lemma isSelfAdjoint_σ (v : Fin 3 → ℝ) : IsSelfAdjoint (σ v : A) := by
  rw [σ]
  refine isSelfAdjoint_sum _ fun i _ => ?_
  rw [IsSelfAdjoint, star_smul]
  simp [(QubitAlgebra.gen (A := A) i).2.star_eq]

/-!
## B. The product formula

`σ_mul_σ` reduces to a single fact about one generator against all of `σ v` at once
(`gen_mul_σ`), proved from the three general products `gen_sq`, `gen_mul_cyc`, `gen_mul_skip` —
kept universally quantified in `i` throughout, rather than instantiated by hand at each of the
nine pairs `(i, j) : Fin 3 × Fin 3`.
-/

/-- Rotating a `Fin 3` sum to start from any `i`, not just `0`: lets `gen_mul_σ` below split
`∑ j, ...` around a symbolic base point `i` instead of the literal `0` that `Fin.sum_univ_three`
is stuck with. -/
lemma sum_univ_three_rotate {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (i : Fin 3) :
    ∑ j, f j = f i + f (i + 1) + f (i + 2) := by
  fin_cases i <;> simp [Fin.sum_univ_three] <;> abel

/-- A single generator against all of `σ v`, split via `sum_univ_three_rotate` into the three
products `gen i * gen i`, `gen i * gen (i + 1)`, `gen i * gen (i + 2)`. -/
lemma gen_mul_σ (i : Fin 3) (v : Fin 3 → ℝ) :
    (QubitAlgebra.gen (A := A) i : A) * σ v =
      (v i : ℂ) • (1 : A) +
        Complex.I • (v (i + 1) : ℂ) • (QubitAlgebra.gen (A := A) (i + 2) : A) -
        Complex.I • (v (i + 2) : ℂ) • (QubitAlgebra.gen (A := A) (i + 1) : A) := by
  rw [σ, Finset.mul_sum, sum_univ_three_rotate (fun j => (QubitAlgebra.gen (A := A) i : A) *
    ((v j : ℂ) • QubitAlgebra.gen (A := A) j)) i]
  simp only [mul_smul_comm, QubitAlgebra.gen_sq, QubitAlgebra.gen_mul_cyc, gen_mul_skip, smul_smul]
  module

/-- The fundamental Pauli vector identity: `σ(u) σ(v) = (u ⬝ᵥ v) • 1 + i • σ(u ⨯₃ v)`. -/
lemma σ_mul_σ (u v : Fin 3 → ℝ) :
    (σ u : A) * σ v = ((u ⬝ᵥ v : ℝ) : ℂ) • (1 : A) + Complex.I • (σ (u ⨯₃ v) : A) := by
  rw [σ, Finset.sum_mul]
  simp_rw [smul_mul_assoc, gen_mul_σ (A := A)]
  rw [dotProduct, cross_apply, σ]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  push_cast
  module

/-- `σ(v)² = ‖v‖² • 1`, i.e. `σ(v) * σ(v) = (v ⬝ᵥ v) • 1`. -/
lemma σ_sq (v : Fin 3 → ℝ) :
    (σ v : A) * σ v = ((v ⬝ᵥ v : ℝ) : ℂ) • (1 : A) := by
  rw [σ_mul_σ, cross_self]
  simp [σ]

/-- `σ` is odd: `σ(-w) = -σ(w)`. -/
lemma σ_neg (w : Fin 3 → ℝ) : (σ (-w) : A) = -σ w := by
  simp only [σ, Pi.neg_apply, Complex.ofReal_neg, neg_smul]
  rw [Finset.sum_neg_distrib]

/-- The Pauli commutator: `[σ(u), σ(v)] = 2i • σ(u ⨯₃ v)`. -/
lemma σ_commutator (u v : Fin 3 → ℝ) :
    (σ u : A) * σ v - σ v * σ u = (2 * Complex.I) • (σ (u ⨯₃ v) : A) := by
  rw [σ_mul_σ, σ_mul_σ, dotProduct_comm v u, ← cross_anticomm u v, σ_neg]
  module

/-- The Pauli anticommutator is twice the dot product times the identity. -/
lemma σ_anticommutator (u v : Fin 3 → ℝ) :
    (σ u : A) * σ v + σ v * σ u = ((2 * (u ⬝ᵥ v) : ℝ) : ℂ) • (1 : A) := by
  rw [σ_mul_σ, σ_mul_σ, dotProduct_comm v u, ← cross_anticomm u v, σ_neg]
  push_cast
  module

end Qubit
