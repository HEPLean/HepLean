/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.Group.Orthochronous
/-!
# The Restricted Lorentz Group

This file is currently a stub.

-/
TODO "Add definition of the restricted Lorentz group."
TODO "Prove member of the restricted Lorentz group is combo of boost and rotation."
TODO "Prove restricted Lorentz group equivalent to connected component of identity."

noncomputable section

open Matrix
open Complex
open ComplexConjugate

namespace LorentzGroup

informal_definition Restricted where
  math :≈ "The subgroup of the Lorentz group consisting of elements which
    are proper and orthochronous."
  deps :≈ [``LorentzGroup, ``IsProper, ``IsOrthochronous]

end LorentzGroup
