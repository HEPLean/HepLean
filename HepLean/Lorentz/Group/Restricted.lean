/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.Group.Orthochronous
import HepLean.Meta.Informal.Basic
/-!
# The Restricted Lorentz Group

This file is currently a stub.

-/
TODO "Add definition of the restricted Lorentz group."
TODO "Prove that every member of the restricted Lorentz group is
  combiniation of a boost and a rotation."
TODO "Prove restricted Lorentz group equivalent to connected component of identity
  of the Lorentz group."

namespace LorentzGroup

/-- The subgroup of the Lorentz group consisting of elements which are proper and orthochronous. -/
informal_definition Restricted where
  deps := [``LorentzGroup, ``IsProper, ``IsOrthochronous]

end LorentzGroup
