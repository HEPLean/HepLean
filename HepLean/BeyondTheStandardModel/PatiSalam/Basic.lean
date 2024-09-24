/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.Basic
import HepLean.Meta.Informal
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

informal_definition GaugeGroupI where
  math :≈ "The group `SU(4) x SU(2) x SU(2)`."
  physics :≈ "The gauge group of the Pati-Salam model (unquotiented by ℤ₂)."

informal_definition inclSM where
  physics :≈ "The homomorphism of the Standard Model gauge group into the Pati-Salam gauge group."
  math :≈ "The group homomorphism `SU(3) x SU(2) x U(1) -> SU(4) x SU(2) x SU(2)`
    taking (h, g, α) to (blockdiag (α h, α ^ (-3)), g, diag(α ^ (3), α ^(-3)))."
  ref :≈ "Page 54 of https://math.ucr.edu/home/baez/guts.pdf"
  deps :≈ [``GaugeGroupI, ``StandardModel.GaugeGroupI]

informal_lemma inclSM_ker where
  math :≈ "The kernel of the map ``inclSM is equal to the subgroup
    ``StandardModel.gaugeGroupℤ₃SubGroup."
  ref :≈ "Footnote 10 of https://arxiv.org/pdf/2201.07245"
  deps :≈ [``inclSM, ``StandardModel.gaugeGroupℤ₃SubGroup]

informal_definition embedSMℤ₃ where
  math :≈ "The group embedding from ``StandardModel.GaugeGroupℤ₃ to ``GaugeGroupI
    induced by ``inclSM by quotienting by the kernal ``inclSM_ker."
  deps :≈ [``inclSM, ``StandardModel.GaugeGroupℤ₃, ``GaugeGroupI, ``inclSM_ker]

informal_definition gaugeGroupISpinEquiv where
  math :≈ "The equivalence between `GaugeGroupI` and `Spin(6) × Spin(4)`."
  deps :≈ [``GaugeGroupI]

informal_definition gaugeGroupℤ₂SubGroup where
  physics :≈ "The ℤ₂-subgroup of the un-quotiented gauge group which acts trivially on
    all particles in the standard model."
  math :≈ "The ℤ₂-subgroup of ``GaugeGroupI with the non-trivial element (-1, -1, -1)."
  ref :≈ "https://math.ucr.edu/home/baez/guts.pdf"
  deps :≈ [``GaugeGroupI]

informal_definition GaugeGroupℤ₂ where
  physics :≈ "The gauge group of the Pati-Salam model with a ℤ₂ quotient."
  math :≈ "The quotient of ``GaugeGroupI by the ℤ₂-subgroup `gaugeGroupℤ₂SubGroup`."
  ref :≈ "https://math.ucr.edu/home/baez/guts.pdf"
  deps :≈ [``GaugeGroupI, ``gaugeGroupℤ₂SubGroup]

informal_lemma sm_ℤ₆_factor_through_gaugeGroupℤ₂SubGroup where
  math :≈ "The group ``StandardModel.gaugeGroupℤ₆SubGroup under the homomorphism ``embedSM factors
    through the subgroup ``gaugeGroupℤ₂SubGroup."
  deps :≈ [``inclSM, ``StandardModel.gaugeGroupℤ₆SubGroup, ``gaugeGroupℤ₂SubGroup]

informal_definition embedSMℤ₆Toℤ₂ where
  math :≈ "The group homomorphism from ``StandardModel.GaugeGroupℤ₆ to ``GaugeGroupℤ₂
    induced by ``embedSM."
  deps :≈ [``inclSM, ``StandardModel.GaugeGroupℤ₆, ``GaugeGroupℤ₂,
    ``sm_ℤ₆_factor_through_gaugeGroupℤ₂SubGroup]

end PatiSalam
