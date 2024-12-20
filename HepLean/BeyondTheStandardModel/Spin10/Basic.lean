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

informal_definition GaugeGroupI where
  math :≈ "The group `Spin(10)`."
  physics :≈ "The gauge group of the Spin(10) model (aka SO(10)-model.)"

informal_definition inclPatiSalam where
  physics :≈ "The inclusion of the Pati-Salam gauge group into Spin(10)."
  math :≈ "The lift of the embedding `SO(6) x SO(4) → SO(10)` to universal covers,
    giving a homomorphism `Spin(6) x Spin(4) → Spin(10)`. Precomposed with the isomorphism,
    ``PatiSalam.gaugeGroupISpinEquiv, between `SU(4) x SU(2) x SU(2)` and `Spin(6) x Spin(4)`."
  ref :≈ "Page 56 of https://math.ucr.edu/home/baez/guts.pdf"
  deps :≈ [``GaugeGroupI, ``PatiSalam.GaugeGroupI, ``PatiSalam.gaugeGroupISpinEquiv]

informal_definition inclSM where
  physics :≈ "The inclusion of the Standard Model gauge group into Spin(10)."
  math :≈ "The compoisiton of ``embedPatiSalam and ``PatiSalam.inclSM."
  ref :≈ "Page 56 of https://math.ucr.edu/home/baez/guts.pdf"
  deps :≈ [``inclPatiSalam, ``PatiSalam.inclSM]

informal_definition inclGeorgiGlashow where
  physics :≈ "The inclusion of the Georgi-Glashow gauge group into Spin(10)."
  math :≈ "The Lie group homomorphism from SU(n) → Spin(2n) dicussed on page 46 of
    https://math.ucr.edu/home/baez/guts.pdf for n = 5."
  deps :≈ [``GaugeGroupI, ``GeorgiGlashow.GaugeGroupI]

informal_definition inclSMThruGeorgiGlashow where
  physics :≈ "The inclusion of the Standard Model gauge group into Spin(10)."
  math :≈ "The composition of ``inclGeorgiGlashow and ``GeorgiGlashow.inclSM."
  deps :≈ [``inclGeorgiGlashow, ``GeorgiGlashow.inclSM]

informal_lemma inclSM_eq_inclSMThruGeorgiGlashow where
  math :≈ "The inclusion ``inclSM is equal to the inclusion ``inclSMThruGeorgiGlashow."
  deps :≈ [``inclSM, ``inclSMThruGeorgiGlashow]

end Spin10Model
