/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.Basic
/-!

# The Georgi-Glashow Model

The Georgi-Glashow model is a grand unified theory that unifies the Standard Model gauge group into
`SU(5)`.

This file currently contains informal-results about the Georgi-Glashow group.

-/

namespace GeorgiGlashow

informal_definition GaugeGroupI where
  math :≈ "The group `SU(5)`."
  physics :≈ "The gauge group of the Georgi-Glashow model."

informal_definition inclSM where
  physics :≈ "The homomorphism of the Standard Model gauge group into the
    Georgi-Glashow gauge group."
  math :≈ "The group homomorphism `SU(3) x SU(2) x U(1) -> SU(5)`
    taking (h, g, α) to (blockdiag (α ^ 3 g, α ^ (-2) h)."
  ref :≈ "Page 34 of https://math.ucr.edu/home/baez/guts.pdf"
  deps :≈ [``GaugeGroupI, ``StandardModel.GaugeGroupI]

informal_lemma inclSM_ker where
  math :≈ "The kernel of the map ``inclSM is equal to the subgroup
    ``StandardModel.gaugeGroupℤ₆SubGroup."
  ref :≈ "Page 34 of https://math.ucr.edu/home/baez/guts.pdf"
  deps :≈ [``inclSM, ``StandardModel.gaugeGroupℤ₆SubGroup]

informal_definition embedSMℤ₆ where
  math :≈ "The group embedding from ``StandardModel.GaugeGroupℤ₆ to ``GaugeGroupI
    induced by ``inclSM by quotienting by the kernal ``inclSM_ker."
  deps :≈ [``inclSM, ``StandardModel.GaugeGroupℤ₆, ``GaugeGroupI, ``inclSM_ker]

end GeorgiGlashow
