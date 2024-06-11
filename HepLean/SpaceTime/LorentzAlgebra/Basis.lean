/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzAlgebra.Basic
/-!
# Basis of the Lorentz Algebra

We define the standard basis of the Lorentz group.

-/

namespace spaceTime

namespace lorentzAlgebra
open Matrix

/-- The matrices which form the basis of the Lorentz algebra. -/
@[simp]
def σMat (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ := fun ρ δ ↦
  η^[ρ]_[μ] * η_[ν]_[δ] - η_[μ]_[δ] * η^[ρ]_[ν]

end lorentzAlgebra

end spaceTime
