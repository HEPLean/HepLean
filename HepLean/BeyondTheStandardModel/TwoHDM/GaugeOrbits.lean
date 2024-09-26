/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.BeyondTheStandardModel.TwoHDM.Basic
/-!

# Gauge orbits for the 2HDM

The main reference for material in this section is https://arxiv.org/pdf/hep-ph/0605184.

-/

namespace TwoHDM

informal_definition prodMatrix where
  math :≈ "For two Higgs fields `Φ₁` and `Φ₂`, the map from space time to 2 x 2 complex matrices
  defined by ((Φ₁^†Φ₁, Φ₂^†Φ₁), (Φ₁^†Φ₂, Φ₂^†Φ₂)). "
  ref :≈ "https://arxiv.org/pdf/hep-ph/0605184 eq 3.8."
  deps :≈ [``StandardModel.HiggsVec, ``SpaceTime]

informal_lemma prodMatrix_positive_semidefinite where
  math :≈ "For all x in ``SpaceTime, ``prodMatrix at `x` is positive semidefinite."
  deps :≈ [``prodMatrix, ``SpaceTime]

informal_lemma prodMatrix_hermitian where
  math :≈ "For all x in ``SpaceTime, ``prodMatrix at `x` is hermitian."
  deps :≈ [``prodMatrix, ``SpaceTime]

informal_lemma prodMatrix_smooth where
  math :≈ "The map ``prodMatrix is a smooth function on spacetime."
  deps :≈ [``prodMatrix]

end TwoHDM
