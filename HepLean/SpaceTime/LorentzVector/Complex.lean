/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import HepLean.SpaceTime.SL2C.Basic
import HepLean.SpaceTime.LorentzVector.Modules
import HepLean.Meta.Informal
import Mathlib.RepresentationTheory.Rep
import HepLean.Tensors.Basic
/-!

# Complex Lorentz vectors

We define complex Lorentz vectors in 4d space-time as representations of SL(2, C).

-/

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

namespace Lorentz

/-- The representation of `SL(2, ℂ)` on complex vectors corresponding to contravariant
  Lorentz vectors. -/
def complexContr : Rep ℂ SL(2, ℂ) := Rep.of ContrℂModule.SL2CRep

/-- The representation of `SL(2, ℂ)` on complex vectors corresponding to contravariant
  Lorentz vectors. -/
def complexCo : Rep ℂ SL(2, ℂ) := Rep.of CoℂModule.SL2CRep

end Lorentz
end
