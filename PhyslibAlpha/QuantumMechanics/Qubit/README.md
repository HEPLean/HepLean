# Recovered qubit development

This worktree starts at upstream/master commit `4a0b4acf`. It contains only the recovered qubit additions and the library imports.

## Abstract foundation

`Algebra/Basic.lean`, `PauliVector.lean`, `Observable.lean`, `Lie.lean` and `Presentation.lean` recover the completed parts of the parked abstract project from commit `2222bef1`.

The ambient algebra now uses Mathlib’s `CStarAlgebra` directly. Observables and their Lie bracket come from the current PhyslibAlpha probabilistic theory. Alpha normalizes the bracket as `-(i / 2)(ab - ba)`. The Lie algebra map therefore sends a vector to its full Pauli observable. The old map used half that observable with the old bracket `-i(ab - ba)`.

The abstract class assumes a Pauli basis. The quaternion construction proves the basis property for an algebraic model. It does not equip that model with a C⋆-norm or instantiate the abstract class. A matrix realization and a bridge to the existing Alpha Bloch-ball model remain open.

The remaining completed declarations from the backup files are recovered in:

- `Algebra/Dynamics.lean`: unitary Hamiltonian evolution, its zero and addition laws and the inner automorphism flow. The flow uses Alpha's existing `AutomorphismGroup` and Mathlib's `Unitary.conjStarAlgAut`.
- `Algebra/AdjointAction.lean`: the real-linear generator `v ↦ 2(h × v)` and its evaluation formula.
- `Algebra/State.lean`: the Bloch expectation vector of an existing Alpha state `𝓢[ℂ, A]`.
- `Algebra/Unitary.lean`: the rotation, scalar-unitary and special-unitary predicates.

The Hamiltonian convention is `U(t) = exp(-itH)` with `ℏ = 1`. Mathlib's `expUnitary` uses a positive imaginary exponent, so the recovered definition passes `-t • H`. The old source passed `t • H` despite documenting the negative exponent. Alpha's normalized observable bracket does not change the Hamiltonian factor `2(h × v)`.

The finite rotation action, its norm and determinant proofs, the Bloch equation and the double-cover results depended on unfinished proofs in the old source. The spectrum, effect and Bloch-ball correspondence proofs were also unfinished. Those statements remain in the source history and are not asserted here.

## Matrix calculations

`Hamiltonian.lean`, `State.lean`, `Measurement.lean` and `Control.lean` recover `Backlog/Qubit/` from commit `8488457a` in the `lie-group-one-parameter-subgroup` worktree.

States use the existing Alpha `densityMatrix` type from `StinespringDilation.lean`. Self-adjoint matrices and spectral data use Mathlib directly. The qubit modules have no direct or transitive QuantumInfo dependency.

The files contain Pauli decompositions, the explicit Hamiltonian evolution matrix, Bloch purity and entropy, conjugation evolution, observable formulas and pulse sequences. These calculations currently form a separate concrete layer. They are not yet specializations of `QubitAlgebra`.

The control results include a geometric Ramsey signal. They do not prove that an arbitrary pulse axis is normalized or identify pulse matrix evolution with that geometric signal.

## Next mathematical work

- Construct a concrete `QubitAlgebra` instance and connect it to the matrix calculations.
- Connect the abstract observable coordinates to Alpha’s qubit state-space model.
- Recover the remaining mathematical statements with proofs using the current Alpha APIs.

The human author must still check that the recovered statements express the intended physics.

## Validation on 2026-11-03

- Full build of `Physlib`, `QuantumInfo` and `PhyslibAlpha`: passed.
- Alpha Lean linters, theorem linter, module documentation, import checks and ForMathlib checks: passed.
- Auxiliary script tests and committed source style checks: passed.
- `lake exe lint_all`: ran to completion. The Physlib and QuantumInfo Lean linters passed. The redundant-import check reported errors in 46 untouched upstream Physlib files. The command itself returned zero despite these diagnostics. No Physlib source files differ from the upstream base.

The recovered Lean files contain no proof placeholders, axioms or `native_decide`.
