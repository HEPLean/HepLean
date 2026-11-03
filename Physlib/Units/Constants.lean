/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Relativity.SpeedOfLight
public import Physlib.QuantumMechanics.PlanckConstant
public import Physlib.StatisticalMechanics.BoltzmannConstant
/-!

# Physical constants

An index of the physical constants in Physlib, and the format in which each of them is defined.

## i. Overview

A physical constant is a definite physical quantity, fixed once and for all, and the number
recording it depends on the system of units in which it is read. Each constant is defined in its
own file, beside the physics it belongs to, by a type whose elements are the values the constant
takes in a chosen but arbitrary system of units, the dimension of that type, and the value the
constant takes in our world as a dimensionful quantity, that is, as a quantity given in every
system of units at once.

This module imports the file of every constant, so that importing it gives all of them, and lists
them below. Use these constants rather than defining new ones or writing out their numerical
values. A new constant goes in its own file, in the format of section A, and is added to the list
in section B and to the imports of this module.

## ii. Key results

This module has no declarations of its own. The constants it collects are:

- `speedOfLight` : The speed of light in our world, in `Physlib/Relativity/SpeedOfLight.lean`.

## iii. Table of contents

- A. The format of a constant
- B. The constants in this format
- C. Constants not yet in this format

## iv. References

* The defining constants of the SI. [ref: bipm_si_brochure_2019]

-/

/-!

## A. The format of a constant

The file of a constant with type `X` and value `x` in our world has the following sections.

- The type: a structure `X` with fields `val : ℝ` and `pos : 0 < val`.
- Instances: `X.instPositiveRealUnitCore`, the coercion `Coe X ℝ` and the simp lemma
  `X.positiveRealUnitCore_val`.
- Positivity: `X.val_pos`, `X.val_nonneg` and `X.val_ne_zero`.
- The dimension: `X.instHasDim`. Together with the action of `ℝ≥0ˣ` supplied by
  `PositiveRealUnitCore.instMulActionUnitsNNReal`, it makes `X` a type carrying a dimension.
- The value in our world: `x : Dimensionful X`, defined as `toDimensionful SI` applied to the value
  of the constant in SI units, and the simp lemma `x_in_SI`, proved by
  `CarriesDimension.toDimensionful_apply_self`.
- Specific to this constant, if needed: other forms of the constant, relations to other
  constants, and any further structure on `X`.

The value `x` is named after the type in lower camel case, for example `speedOfLight` for
`SpeedOfLight`. Its docstring gives the number with its SI unit and says whether it is exact, as
for the defining constants of the SI, or measured, in which case it names the CODATA edition the
number is taken from. A `One` instance is not part of the format; a constant that needs one keeps
it with the results specific to that constant. The module documentation of the file has the
standard layout, with the six parts above as its sections A to F.

A type of this format consists of strictly positive reals, so no action of `ℝ≥0` on it is
compatible with the magnitude, which is why `CarriesDimension` is stated for the units of `ℝ≥0`;
see `Physlib/Units/Basic.lean`.

## B. The constants in this format

- The speed of light: type `SpeedOfLight`, value `speedOfLight`, dimension `L T⁻¹`, and value
  `299792458 m s⁻¹` in SI units, which is exact. In `Physlib/Relativity/SpeedOfLight.lean`.

## C. Constants not yet in this format

- Planck's constant and the reduced Planck's constant, `Constants.h` and `Constants.ℏ`, in
  `Physlib/QuantumMechanics/PlanckConstant.lean`.
- The Boltzmann constant, `Constants.kB`, in
  `Physlib/StatisticalMechanics/BoltzmannConstant.lean`.

-/
