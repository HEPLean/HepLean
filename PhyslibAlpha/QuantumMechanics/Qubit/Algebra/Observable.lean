/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Qubit.Algebra.PauliVector

/-!
# Pauli coordinates of abstract qubit observables

Every observable has a real scalar part and a real Pauli vector.

## i. Overview

The Pauli basis gives unique complex coordinates. Self-adjoint elements have real
coordinates. These coordinates define a real-linear equivalence for the observable space.
The trace and determinant are algebraic formulas. Multiplicativity of the determinant is
not established here.

## ii. Key results

`Qubit.isSelfAdjoint_iff_coeff` and `Qubit.observableEquiv`.

## iii. Table of contents

- A. Pauli coordinates of abstract qubit observables

## iv. References

The imported modules provide the underlying algebraic and analytic results.

-/

@[expose] public section

/-! ## A. Pauli coordinates of abstract qubit observables -/

open scoped ComplexOrder CStarAlgebra
open Module ProbabilisticTheory

namespace Qubit

variable {A : Type*} [CStarAlgebra A] [QubitAlgebra A]

/-- The Pauli coefficients of an algebra element: `coeff a 0` is the scalar part, `coeff a
(i.succ)` is the coefficient of `gen i`. Unique since `pauliBasis` is a basis. -/
noncomputable def coeff (a : A) : Fin 4 → ℂ :=
  QubitAlgebra.pauliBasis.repr a

/-- `pauliBasis 0 = 1`, i.e. `coeff a 0` really is the scalar (`1`-)coefficient — the fact
`Qubit.trace`, below, is built on. -/
lemma pauliBasis_zero : (QubitAlgebra.pauliBasis (A := A) : Fin 4 → A) 0 = 1 := by
  rw [QubitAlgebra.pauliBasis_eq, Fin.cons_zero]

/-- The coefficient of `1` in an algebra element's Pauli decomposition. -/
lemma coeff_one_zero : coeff (1 : A) 0 = 1 := by
  rw [coeff, ← pauliBasis_zero, Basis.repr_self, Finsupp.single_eq_same]

/-- The trace of an algebra element: twice its scalar (`1`-)coefficient, matching the physical
normalization `trace (1 : A) = 2`, `trace (gen i : A) = 0` — the trace of a `2 × 2` identity and
of a traceless Pauli matrix. Purely algebraic, no matrices: `coeff` already comes from
`QubitAlgebra.pauliBasis` being a basis. -/
noncomputable def trace (a : A) : ℂ :=
  2 * coeff a 0

@[simp]
lemma trace_one : trace (1 : A) = 2 := by
  rw [trace, coeff_one_zero, mul_one]

lemma trace_smul (c : ℂ) (a : A) : trace (c • a) = c * trace a := by
  rw [trace, trace, coeff, coeff, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm]

/-- The determinant of an algebra element, via the `2 × 2` Cayley–Hamilton formula `det a =
(trace a ^ 2 - trace (a * a)) / 2` — purely a formula in the trace, so needs no separate proof of
existence and no matrices. (That this is genuinely multiplicative, or agrees with the usual
determinant once `Qubit/Matrix.lean` identifies `A` with `Matrix (Fin 2) (Fin 2) ℂ`, is not
needed below and not yet checked.) -/
noncomputable def det (a : A) : ℂ :=
  (trace a ^ 2 - trace (a * a)) / 2

/-- The determinant of a scalar element: `det (c • 1) = c ^ 2`, matching `det (c • I) = c ^ 2`
for `2 × 2` matrices. -/
lemma det_smul_one (c : ℂ) : det (c • (1 : A)) = c ^ 2 := by
  have h1 : (c • (1 : A)) * (c • (1 : A)) = c ^ 2 • (1 : A) := by
    rw [smul_mul_smul_comm, mul_one, sq]
  rw [det, trace_smul, trace_one, h1, trace_smul, trace_one]
  ring

/-- Every element of `pauliBasis` is self-adjoint: it is either `1` or a generator. -/
lemma isSelfAdjoint_pauliBasis (j : Fin 4) :
    IsSelfAdjoint (QubitAlgebra.pauliBasis (A := A) j : A) := by
  rw [QubitAlgebra.pauliBasis_eq]
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [IsSelfAdjoint.one]
  · simp

/-- `coeff` reads off the coefficients of *any* explicit `pauliBasis` combination, not just the
canonical one produced by `Basis.repr` — the basis property makes the two agree. -/
lemma coeff_eq_of_eq_sum {a : A} {c : Fin 4 → ℂ}
    (h : a = ∑ j, c j • (QubitAlgebra.pauliBasis (A := A) j : A)) (i : Fin 4) :
    coeff a i = c i := by
  rw [coeff, h, map_sum]
  simp [Basis.repr_self, Finsupp.single_apply, Finset.sum_ite_eq']

/-- Taking `star` conjugates every Pauli coefficient. -/
lemma coeff_star (a : A) (i : Fin 4) :
    coeff (star a : A) i = (starRingEnd ℂ) (coeff a i) := by
  refine coeff_eq_of_eq_sum (c := fun j => (starRingEnd ℂ) (coeff a j)) ?_ i
  conv_lhs => rw [← QubitAlgebra.pauliBasis.sum_repr a]
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_smul, (isSelfAdjoint_pauliBasis (A := A) j).star_eq]
  rfl

/-- An algebra element is self-adjoint iff all four of its Pauli coefficients are real. -/
lemma isSelfAdjoint_iff_coeff (a : A) :
    IsSelfAdjoint a ↔ ∀ i, (coeff (A := A) a i).im = 0 := by
  constructor
  · intro ha i
    have h := coeff_star (A := A) a i
    rw [ha.star_eq] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  · intro h
    have ha : (a : A) = ∑ j, coeff a j • (QubitAlgebra.pauliBasis (A := A) j : A) :=
      (QubitAlgebra.pauliBasis.sum_repr a).symm
    have hstar : star (a : A) = ∑ j, coeff a j • (QubitAlgebra.pauliBasis (A := A) j : A) := by
      conv_lhs => rw [ha]
      rw [star_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_smul, (isSelfAdjoint_pauliBasis (A := A) j).star_eq, Complex.star_def,
        Complex.conj_eq_iff_im.mpr (h j)]
    rw [IsSelfAdjoint, hstar, ← ha]

/-- The real-linear equivalence between observables and `ℝ × (Fin 3 → ℝ)`: the scalar part `a₀`
and Pauli vector `v` of `a₀ • 1 + σ v`. -/
noncomputable def observableEquiv : Observable A ≃ₗ[ℝ] ℝ × (Fin 3 → ℝ) where
  toFun a := ((coeff (a : A) 0).re, fun i => (coeff (a : A) i.succ).re)
  invFun p := ⟨p.1 • 1 + σ p.2,
    IsSelfAdjoint.add
      (by rw [real_smul_eq_ofReal_smul]
          exact IsSelfAdjoint.smul (IsSelfAdjoint.all p.1) (IsSelfAdjoint.one A))
      (isSelfAdjoint_σ p.2)⟩
  map_add' a b := by
    ext <;> simp [coeff, AddSubgroup.coe_add]
  map_smul' r a := by
    have hcast : ∀ i : Fin 4, coeff (A := A) (r • (a : A)) i = r * coeff (A := A) (a : A) i := by
      intro i
      rw [real_smul_eq_ofReal_smul]
      show QubitAlgebra.pauliBasis.repr ((r : ℂ) • (a : A)) i =
        r * QubitAlgebra.pauliBasis.repr (a : A) i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    ext <;> simp [hcast, RingHom.id_apply]
  left_inv a := by
    have hre : ∀ i, ((coeff (a : A) i).re : ℂ) = coeff (a : A) i := fun i => by
      have him := (isSelfAdjoint_iff_coeff (A := A) (a : A)).mp a.2 i
      apply Complex.ext <;> simp [him]
    have ha : (a : A) = ∑ j, coeff (a : A) j • (QubitAlgebra.pauliBasis (A := A) j : A) :=
      (QubitAlgebra.pauliBasis.sum_repr (a : A)).symm
    have hsum : (a : A) = coeff (a : A) 0 • (1 : A)
        + ∑ i : Fin 3, coeff (a : A) i.succ • (QubitAlgebra.gen (A := A) i : A) := by
      conv_lhs => rw [ha]
      rw [Fin.sum_univ_succ, QubitAlgebra.pauliBasis_eq]
      simp
    ext
    show ((coeff (a : A) 0).re : ℝ) • (1 : A) + σ (fun i => (coeff (a : A) i.succ).re) = (a : A)
    rw [real_smul_eq_ofReal_smul, hre, σ]
    simp only [hre]
    exact hsum.symm
  right_inv p := by
    obtain ⟨a₀, v⟩ := p
    have heq : (a₀ • (1 : A) + σ v : A) =
        ∑ j : Fin 4, (Fin.cons (a₀ : ℂ) (fun i => (v i : ℂ)) : Fin 4 → ℂ) j •
          (QubitAlgebra.pauliBasis (A := A) j : A) := by
      rw [Fin.sum_univ_succ]
      simp only [QubitAlgebra.pauliBasis_eq, Fin.cons_zero, Fin.cons_succ, σ]
      rw [real_smul_eq_ofReal_smul]
    have hc0 := coeff_eq_of_eq_sum heq 0
    have hci : ∀ i : Fin 3, coeff (A := A) (a₀ • (1 : A) + σ v) i.succ = (v i : ℂ) :=
      fun i => coeff_eq_of_eq_sum heq i.succ
    show ((coeff (A := A) (a₀ • (1 : A) + σ v) 0).re,
      fun i => (coeff (A := A) (a₀ • (1 : A) + σ v) i.succ).re) = (a₀, v)
    simp only [hc0, hci, Fin.cons_zero, Complex.ofReal_re]

end Qubit
