/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import HepLean.SpaceTime.SL2C.Basic
import HepLean.SpaceTime.LorentzVector.Complex.Modules
import HepLean.Meta.Informal
import Mathlib.RepresentationTheory.Rep
import HepLean.SpaceTime.LorentzVector.Real.Modules
/-!

# Real Lorentz vectors

We define real Lorentz vectors in as representations of the Lorentz group.

-/

noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open SpaceTime

namespace Lorentz

/-- The representation of `LorentzGroup d` on real vectors corresponding to contravariant
  Lorentz vectors. In index notation these have an up index `ψⁱ`. -/
def Contr (d : ℕ) : Rep ℝ (LorentzGroup d) := Rep.of ContrMod.rep

/-- The representation of `LorentzGroup d` on real vectors corresponding to covariant
  Lorentz vectors. In index notation these have an up index `ψⁱ`. -/
def Co (d : ℕ) : Rep ℝ (LorentzGroup d) := Rep.of CoMod.rep

end Lorentz
end
