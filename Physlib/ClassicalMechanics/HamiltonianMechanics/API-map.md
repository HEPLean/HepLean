# Hamiltonian mechanics

## Abstract (Alpha)

Hamiltonian mechanics separates the kinematics of a system, described by its phase space, from
its dynamics, specified by a Hamiltonian. Hamilton's equations determine the motion, and Poisson
brackets describe the evolution of observables. Symmetries give conserved quantities, while
Liouville integrability requires sufficiently many independent conserved quantities in involution.
The coordinate formulations of the harmonic oscillator, simple pendulum and central-force systems
provide examples, alongside a symplectic vector-space formulation of moment maps and conservation.

## Content (Alpha)

### Phase space and observables

A configuration space Q is a smooth manifold without boundary {1}. [1] For finite-dimensional Q,
its canonical Hamiltonian phase space is the cotangent bundle T*Q: a state consists of a
configuration q and a momentum covector at q. This space carries a canonical symplectic form,
independently of the choice of Hamiltonian {6}. [TODO] In the coordinate formulation on a complete
real inner-product space X, states are pairs (p, q) in X × X, and observables are real-valued
functions f(p, q), with momentum first. [2] Identifying the cotangent phase space of a Euclidean
configuration space with this coordinate representation uses the inner product to represent
covectors as momentum vectors. [TODO]

### Hamiltonians and Hamiltonian trajectories

A Hamiltonian system consists of a phase space and a smooth real-valued Hamiltonian, possibly
time-dependent and defined on an open domain. The phase space describes kinematics; choosing the
Hamiltonian specifies dynamics. A shared structure packages these data {2}. [TODO] In coordinates,
curves p(t) and q(t) satisfy Hamilton's equations q̇ = ∇ₚH and ṗ = −∇qH exactly when the Hamilton
equation operator vanishes. [3] For a smooth Hamiltonian and a smooth phase-space curve, the
variational gradient of the action ∫ (⟨p, q̇⟩ − H(t, p, q)) dt is that operator. [4]

### Poisson brackets and observable evolution

The coordinate Poisson bracket is {f, g} = ⟨∇qf, ∇ₚg⟩ − ⟨∇ₚf, ∇qg⟩. [2] It is antisymmetric,
bilinear and satisfies the Leibniz rule, with the differentiability assumptions needed for the
gradient rules. [5] Along a differentiable solution of Hamilton's equations, a time-independent
observable differentiable at the current state satisfies d f(p(t), q(t))/dt = {f, H(t)}(p(t), q(t)).
[6] The canonical coordinate relations are {qᵢ, pⱼ} = δᵢⱼ, {qᵢ, qⱼ} = {pᵢ, pⱼ} = 0, and smooth
observables satisfy the Jacobi identity. [TODO]

### Symmetries and conserved quantities

On a finite-dimensional real symplectic vector space, an affine infinitesimally symplectic Lie
algebra action has a moment map whose components generate the action's vector fields through
their symplectic gradients. [7] If an autonomous Hamiltonian is invariant under a generator, the
corresponding moment-map component is constant along its Hamiltonian trajectories. [8] The
symplectic vector-field description and the coordinate Hamilton equations describe the same
dynamics through a shared phase-space interface. [TODO]

### Integrability

For an autonomous Hamiltonian on a 2d-dimensional Euclidean phase space, Liouville integrability
on an open dense domain U consists of d smooth observables, including the Hamiltonian, that
pairwise Poisson-commute and whose phase-space gradients are linearly independent on U. [9] Each
has zero time derivative along a differentiable Hamiltonian trajectory at times when the state
lies in U. [10] With one degree of freedom, the Hamiltonian alone gives integrability on any open
dense domain where it is smooth and its phase-space gradient is nonzero. [11] The Liouville–Arnold
theorem identifies compact connected regular common level sets as invariant tori and supplies
local action–angle coordinates {6}. [TODO]

### Existing examples and their connections

The harmonic oscillator {3} has canonical momentum p = m q̇ and Hamiltonian
H = ‖p‖²/(2m) + k ‖q‖²/2. Along smooth trajectories, its Hamiltonian equations agree with its
Newtonian and variational formulations. [12] For the simple pendulum {4}, using a real lift θ of
the angle and moment of inertia I, the momentum is p = I θ̇ and the Hamiltonian is
H = ‖p‖²/(2I) + V(θ). Its Hamiltonian, Newtonian and variational formulations also agree for smooth
lifted trajectories. [13]

A three-dimensional central-force system has positive mass m and radial potential V, with
H = ‖p‖²/(2m) + V(‖q‖). Its Hamiltonian is smooth away from q = 0. [14] Its angular momentum is
L = q × p; L² and Lz Poisson-commute with each other, and each Poisson-commutes with H away from
q = 0. [15] Their functional independence on a suitable open dense domain gives central-force
Liouville integrability. [TODO]

A Euclidean point-particle configuration space admits reusable constructors for its phase space
and, given positive mass m and a smooth potential V, for the Lagrangian
L(q, v) = m ‖v‖²/2 − V(q) and Hamiltonian H(p, q) = ‖p‖²/(2m) + V(q). The momentum p = m v
connects these descriptions {5}. [TODO]

## Lean References

1. Physlib/ClassicalMechanics/ConfigurationSpace/Basic.lean — `ConfigurationSpace`
2. Physlib/ClassicalMechanics/HamiltonianMechanics/PoissonBracket.lean — `poissonBracket`
3. Physlib/ClassicalMechanics/HamiltonianMechanics/HamiltonsEquations.lean —
   `hamiltonEqOp`, `hamiltonEqOp_eq_zero_iff_hamiltons_equations`
4. Physlib/ClassicalMechanics/HamiltonianMechanics/HamiltonsEquations.lean —
   `hamiltons_equations_varGradient`
5. Physlib/ClassicalMechanics/HamiltonianMechanics/PoissonBracket.lean —
   `poissonBracket_antisymm`, `poissonBracket_self`, `poissonBracket_add_left`,
   `poissonBracket_add_right`, `poissonBracket_const_mul_left`, `poissonBracket_const_mul_right`,
   `poissonBracket_mul_left`, `poissonBracket_mul_right`
6. Physlib/ClassicalMechanics/HamiltonianMechanics/PoissonBracket.lean —
   `deriv_comp_eq_poissonBracket`
7. PhyslibAlpha/ClassicalMechanics/MomentMap/Basic.lean — `IsSymplecticForm`,
   `AffineSymplecticAction`, `IsSymplecticGradient`,
   `AffineSymplecticAction.vectorField_isSymplecticGradient`
8. PhyslibAlpha/ClassicalMechanics/MomentMap/Basic.lean —
   `AffineSymplecticAction.noether`, `AffineSymplecticAction.noether_const`
9. PhyslibAlpha/ClassicalMechanics/LiouvilleIntegrable/Basic.lean — `LiouvilleIntegrableOn`
10. PhyslibAlpha/ClassicalMechanics/LiouvilleIntegrable/Basic.lean —
    `LiouvilleIntegrableOn.deriv_comp_eq_zero`
11. PhyslibAlpha/ClassicalMechanics/LiouvilleIntegrable/Basic.lean —
    `LiouvilleIntegrableOn.oneDegreeOfFreedom`
12. Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean — `toCanonicalMomentum_eq`,
    `hamiltonian_eq`, `equationOfMotion_tfae`
13. Physlib/ClassicalMechanics/Pendulum/SimplePendulum/Hamiltonian.lean — `canonicalMomentum_eq`,
    `hamiltonian_eq`, `equationOfMotion_tfae`
14. PhyslibAlpha/ClassicalMechanics/CentralForce/Basic.lean — `CentralForce`, `hamiltonian`,
    `contDiffOn_hamiltonian`
15. PhyslibAlpha/ClassicalMechanics/CentralForce/AngularMomentum.lean — `angularMomentum`,
    `angularMomentumSq`, `angularMomentumZ`, `poissonBracket_angularMomentumSq_angularMomentumZ`,
    `poissonBracket_angularMomentumSq_hamiltonian`, `poissonBracket_angularMomentumZ_hamiltonian`

## References

1. Configuration Space API map — Physlib/ClassicalMechanics/ConfigurationSpace/API-map.md
2. Physlib GitHub issue #2003, Foundations for Hamiltonian Systems,
   https://github.com/leanprover-community/physlib/issues/2003
3. Configuration space of the harmonic oscillator API map —
   Physlib/ClassicalMechanics/HarmonicOscillator/Geometric/API-map.md
4. Simple pendulum API map — Physlib/ClassicalMechanics/Pendulum/SimplePendulum/API-map.md
5. Lagrangian mechanics API map — Physlib/ClassicalMechanics/Lagrangian/API-map.md
6. V. I. Arnold, *Mathematical Methods of Classical Mechanics*.
