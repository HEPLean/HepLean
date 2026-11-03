# Recovered qubit development

This worktree starts at upstream/master commit `4a0b4acf`. It contains only the recovered qubit additions and the library imports.

## Abstract foundation

`Algebra/Basic.lean`, `PauliVector.lean`, `Observable.lean`, `Lie.lean` and `Presentation.lean` recover the completed parts of the parked abstract project from commit `2222bef1`.

The ambient algebra now uses Mathlib’s `CStarAlgebra` directly. Observables and their Lie bracket come from the current PhyslibAlpha probabilistic theory. Alpha normalizes the bracket as `-(i / 2)(ab - ba)`. The Lie algebra map therefore sends a vector to its full Pauli observable. The old map used half that observable with the old bracket `-i(ab - ba)`.

The abstract class assumes a Pauli basis. The quaternion construction proves the basis property for an algebraic model. It does not equip that model with a C⋆-norm or instantiate the abstract class. A matrix realization and a bridge to the existing Alpha Bloch-ball model remain open.

The old backup files for spectrum, effects, states, unitaries, dynamics and adjoint actions contained unfinished proofs. They remain in the source history. They are not imported into this recovery.

## Matrix calculations

`Hamiltonian.lean`, `State.lean`, `Measurement.lean` and `Control.lean` recover `Backlog/Qubit/` from commit `8488457a` in the `lie-group-one-parameter-subgroup` worktree.

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
