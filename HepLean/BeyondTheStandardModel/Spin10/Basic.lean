/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.BeyondTheStandardModel.PatiSalam.Basic
import HepLean.BeyondTheStandardModel.GeorgiGlashow.Basic
/-!

# The Spin(10) Model

Note: By physicists this is usually called SO(10). However, the true gauge group involved
is Spin(10).

-/

namespace Spin10Model

/-- The gauge group of the Spin(10) model, i.e., the group `Spin(10)`. -/
informal_definition GaugeGroupI where
  deps := []

/-- The inclusion of the Pati-Salam gauge group into Spin(10), i.e., the lift of the embedding
`SO(6) × SO(4) → SO(10)` to universal covers, giving a homomorphism `Spin(6) × Spin(4) → Spin(10)`.
Precomposed with the isomorphism, `PatiSalam.gaugeGroupISpinEquiv`, between `SU(4) × SU(2) × SU(2)`
and `Spin(6) × Spin(4)`.

See page 56 of https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition inclPatiSalam where
  deps := [``GaugeGroupI, ``PatiSalam.GaugeGroupI, ``PatiSalam.gaugeGroupISpinEquiv]

/-- The inclusion of the Standard Model gauge group into Spin(10), i.e., the compoisiton of
`embedPatiSalam` and `PatiSalam.inclSM`.

See page 56 of https://math.ucr.edu/home/baez/guts.pdf
-/
informal_definition inclSM where
  deps := [``inclPatiSalam, ``PatiSalam.inclSM]

/-- The inclusion of the Georgi-Glashow gauge group into Spin(10), i.e., the Lie group homomorphism
from `SU(n) → Spin(2n)` discussed on page 46 of https://math.ucr.edu/home/baez/guts.pdf for `n = 5`.
-/
informal_definition inclGeorgiGlashow where
  deps := [``GaugeGroupI, ``GeorgiGlashow.GaugeGroupI]

/-- The inclusion of the Standard Model gauge group into Spin(10), i.e., the composition of
`inclGeorgiGlashow` and `GeorgiGlashow.inclSM`.
-/
informal_definition inclSMThruGeorgiGlashow where
  deps := [``inclGeorgiGlashow, ``GeorgiGlashow.inclSM]

/-- The inclusion `inclSM` is equal to the inclusion `inclSMThruGeorgiGlashow`. -/
informal_lemma inclSM_eq_inclSMThruGeorgiGlashow where
  deps := [``inclSM, ``inclSMThruGeorgiGlashow]

end Spin10Model
