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

An index of the physical constants in Physlib, and the format of their files.

## i. Overview

Each constant has its own file, which this module imports. Use these constants instead of defining
new ones or writing out their values. A new constant gets a file in the format of section A, a row
in the table below, an import above and a condition in `exists_units_constants_eq_one`.

## ii. Key results

| Constant | Dimension | Value in SI units |
|---|---|---|
| `speedOfLight` | `L T⁻¹` | `299792458 m s⁻¹`, exact |

Not yet in this format: `Constants.h`, `Constants.ℏ` and `Constants.kB`.

- `exists_units_constants_eq_one` : There are units in which the constants above are `1`.

## iii. Table of contents

- A. The format of a constant
- B. Natural units

## iv. References

* The defining constants of the SI. [ref: bipm_si_brochure_2019]

## A. The format of a constant

The file of a constant with type `X` and value `x` has these sections, as in
`Physlib/Relativity/SpeedOfLight.lean`.

| Section | Contents |
|---|---|
| A. The type | `structure X` with fields `val : ℝ` and `pos : 0 < val` |
| B. Instances | `X.instPositiveRealUnitCore`, `Coe X ℝ`, `X.positiveRealUnitCore_val` |
| C. Positivity | `X.val_pos`, `X.val_nonneg`, `X.val_ne_zero` |
| D. The dimension | `X.instHasDim` |
| E. The value in our world | `x : Dimensionful X` and `x_in_SI` |
| F. Specific to this constant | Optional, for example `One` or other forms of the constant |

The value `x` is `X` in lower camel case, defined by `toDimensionful SI`, and `x_in_SI` is proved by
`toDimensionful_apply_self`. The docstring of `x` gives the number with its SI unit, followed by
`exact` or, for a measured constant, the CODATA edition.

-/

@[expose] public section

open NNReal Dimension LTMCTUnitChoices

/-!

## B. Natural units

-/

/-- There are units in which the constants of this index are `1`. -/
lemma exists_units_constants_eq_one : ∃ u : LTMCTUnitChoices, (speedOfLight u).val = 1 := by
  refine ⟨{SI with length := PositiveRealUnitCore.scale 299792458 LengthUnit.meters}, ?_⟩
  change ((SI.dimScale _ (L𝓭 * T𝓭⁻¹) : ℝ≥0) : ℝ) * 299792458 = 1
  simp only [map_mul, map_inv, NNReal.coe_mul, NNReal.coe_inv, dimScale_L𝓭, dimScale_T𝓭]
  change (1 / (299792458 * 1) : ℝ) * (1 / 1)⁻¹ * 299792458 = 1
  norm_num
