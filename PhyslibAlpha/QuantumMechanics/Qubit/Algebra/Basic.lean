/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.Observable
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Abstract qubit observable algebras

A qubit algebra is a complex C⋆-algebra with a Pauli triple and a four-element Pauli basis.

## i. Overview

The generators satisfy the cyclic Pauli relations. The basis hypothesis fixes the complex
dimension to four and gives unique Pauli coordinates. No matrix representation is chosen.

## ii. Key results

`Qubit.QubitAlgebra` and the reversed Pauli product identities.

## iii. Table of contents

- A. The qubit observable algebra
- B. Reversed products

## iv. References

The imported modules provide the underlying algebraic and analytic results.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra
open Module ProbabilisticTheory

namespace Qubit

/-!
## A. The qubit observable algebra
-/

/--
`A` is a qubit observable algebra: a unital C⋆-algebra carrying three self-adjoint generators,
indexed by `Fin 3`, satisfying the Pauli relations in cyclic form, with `1` together with the
generators forming a complex basis of `A`.

The basis condition (rather than a mere spanning condition) is what makes Pauli decompositions
of elements of `A` unique; this is used throughout the rest of the development. See the module
docstring for why this is taken as a field rather than derived from something weaker.
-/
class QubitAlgebra (A : Type*)
    [CStarAlgebra A] where
  /-- The three Pauli generators, indexed by `Fin 3`. `gen 0, gen 1, gen 2` are `X, Y, Z`. -/
  gen : Fin 3 → Observable A
  /-- Each generator squares to `1`. -/
  gen_sq : ∀ i, (gen i : A) * gen i = 1
  /-- The cyclic Pauli relation: `gen i * gen (i + 1) = i • gen (i + 2)`, indices mod 3.
  This single field is `XY = iZ`, `YZ = iX`, `ZX = iY` at `i = 0, 1, 2` respectively. -/
  gen_mul_cyc : ∀ i, (gen i : A) * gen (i + 1) = Complex.I • (gen (i + 2) : A)
  /-- `1, gen 0, gen 1, gen 2` form a complex basis of `A`. -/
  pauliBasis : Basis (Fin 4) ℂ A
  /-- The basis `pauliBasis` is exactly `1` followed by the generators. -/
  pauliBasis_eq : ⇑pauliBasis = Fin.cons (1 : A) (fun i => (gen i : A))

variable {A : Type*} [CStarAlgebra A] [QubitAlgebra A]

/-!
## B. Reversed products

Self-adjointness of the generators turns the cyclic relation `gen i * gen (i + 1) = i • gen
(i + 2)` into its own reversed form, by taking `star` of both sides. This is the single
uniform replacement for what would otherwise be three separate lemmas `YX = -iZ`, `ZY = -iX`,
`XZ = -iY`.
-/

/-- `gen (i + 1) * gen i = -i • gen (i + 2)`, indices mod 3. -/
lemma gen_mul_cyc_symm (i : Fin 3) :
    (QubitAlgebra.gen (A := A) (i + 1) : A) * (QubitAlgebra.gen (A := A) i : A) =
      -Complex.I • (QubitAlgebra.gen (A := A) (i + 2) : A) := by
  have h := congrArg star (QubitAlgebra.gen_mul_cyc (A := A) i)
  simpa [star_mul, (QubitAlgebra.gen (A := A) i).2.star_eq,
    (QubitAlgebra.gen (A := A) (i + 1)).2.star_eq,
    (QubitAlgebra.gen (A := A) (i + 2)).2.star_eq, star_smul] using h

/-- `gen i * gen (i + 2) = -i • gen (i + 1)`, indices mod 3: the remaining off-diagonal case,
complementary to `gen_mul_cyc` (`i`, `i + 1`) and `gen_mul_cyc_symm` (`i + 1`, `i`). Follows from
`gen_mul_cyc_symm` at `i + 2`, since `i + 2 + 1 = i` and `i + 2 + 2 = i + 1` mod 3. Together with
`gen_sq` and `gen_mul_cyc`, this gives `gen i * gen j` for every `i j : Fin 3` without having to
instantiate at each of the nine pairs by hand. -/
lemma gen_mul_skip (i : Fin 3) :
    (QubitAlgebra.gen (A := A) i : A) * (QubitAlgebra.gen (A := A) (i + 2) : A) =
      -Complex.I • (QubitAlgebra.gen (A := A) (i + 1) : A) := by
  have h := gen_mul_cyc_symm (A := A) (i + 2)
  rwa [show i + 2 + 1 = i from by omega, show i + 2 + 2 = i + 1 from by omega] at h

end Qubit
