/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.Basic
/-!

# The Pati-Salam Model

The Pati-Salam model is a petite unified theory that unifies the Standard Model gauge group into
`SU(4) x SU(2) x SU(2)`.

This file currently contains informal-results about the Pati-Salam group.

-/

namespace PatiSalam
/-!

## The Pati-Salam gauge group.

-/

/-- The gauge group of the Pati-Salam model (unquotiented by ℤ₂), i.e., `SU(4) × SU(2) × SU(2)`. -/
informal_definition GaugeGroupI where
  deps := []

/-- The homomorphism of the Standard Model gauge group into the Pati-Salam gauge group, i.e., the
group homomorphism `SU(3) × SU(2) × U(1) → SU(4) × SU(2) × SU(2)` taking `(h, g, α)` to
`(blockdiag (α h, α ^ (-3)), g, diag (α ^ 3, α ^(-3))`.

See page 54 of https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition inclSM where
  deps := [``GaugeGroupI, ``StandardModel.GaugeGroupI]

/-- The kernel of the map `inclSM` is equal to the subgroup `StandardModel.gaugeGroupℤ₃SubGroup`.

See footnote 10 of https://arxiv.org/pdf/2201.07245
-/
informal_lemma inclSM_ker where
  deps := [``inclSM, ``StandardModel.gaugeGroupℤ₃SubGroup]

/-- The group embedding from `StandardModel.GaugeGroupℤ₃` to `GaugeGroupI` induced by `inclSM` by
quotienting by the kernel `inclSM_ker`.
-/
informal_definition embedSMℤ₃ where
  deps := [``inclSM, ``StandardModel.GaugeGroupℤ₃, ``GaugeGroupI, ``inclSM_ker]

/-- The equivalence between `GaugeGroupI` and `Spin(6) × Spin(4)`. -/
informal_definition gaugeGroupISpinEquiv where
  deps := [``GaugeGroupI]

/-- The ℤ₂-subgroup of the un-quotiented gauge group which acts trivially on all particles in the
standard model, i.e., the ℤ₂-subgroup of `GaugeGroupI` with the non-trivial element `(-1, -1, -1)`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition gaugeGroupℤ₂SubGroup where
  deps := [``GaugeGroupI]

/-- The gauge group of the Pati-Salam model with a ℤ₂ quotient, i.e., the quotient of `GaugeGroupI`
by the ℤ₂-subgroup `gaugeGroupℤ₂SubGroup`.

See https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition GaugeGroupℤ₂ where
  deps := [``GaugeGroupI, ``gaugeGroupℤ₂SubGroup]

/-- The group `StandardModel.gaugeGroupℤ₆SubGroup` under the homomorphism `embedSM` factors through
the subgroup `gaugeGroupℤ₂SubGroup`.
-/
informal_lemma sm_ℤ₆_factor_through_gaugeGroupℤ₂SubGroup where
  deps := [``inclSM, ``StandardModel.gaugeGroupℤ₆SubGroup, ``gaugeGroupℤ₂SubGroup]

/-- The group homomorphism from `StandardModel.GaugeGroupℤ₆` to `GaugeGroupℤ₂` induced by `embedSM`.
-/
informal_definition embedSMℤ₆Toℤ₂ where
  deps := [``inclSM, ``StandardModel.GaugeGroupℤ₆, ``GaugeGroupℤ₂,
    ``sm_ℤ₆_factor_through_gaugeGroupℤ₂SubGroup]

end PatiSalam
