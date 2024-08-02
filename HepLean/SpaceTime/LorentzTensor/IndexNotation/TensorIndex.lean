/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.IndexNotation.IndexListColor
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# The structure of a tensor with a string of indices

-/

namespace TensorStructure
open TensorColor
open IndexNotation

variable {R : Type} [CommSemiring R] (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color}
  {cW : W → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν η : 𝓣.Color}

variable [IndexNotation 𝓣.Color] [Fintype 𝓣.Color] [DecidableEq 𝓣.Color]

/-- The structure an tensor with a index specification e.g. `ᵘ¹ᵤ₂`. -/
structure TensorIndex (cn : Fin n → 𝓣.Color) where
  /-- The underlying tensor. -/
  tensor : 𝓣.Tensor cn
  /-- The list of indices. -/
  index : IndexListColor 𝓣.toTensorColor
  /-- The number of indices matches the number of vector spaces in the tensor. -/
  nat_eq : n = index.1.length
  /-- The equivalence classes of colors of the tensor and the index list agree. -/
  quot_eq : 𝓣.colorQuot ∘ index.1.colorMap ∘ Fin.cast nat_eq = 𝓣.colorQuot ∘ cn

namespace TensorIndex

variable {𝓣 : TensorStructure R} [IndexNotation 𝓣.Color] [Fintype 𝓣.Color] [DecidableEq 𝓣.Color]
variable {n m : ℕ} {cn : Fin n → 𝓣.Color} {cm : Fin m → 𝓣.Color} (T : TensorIndex 𝓣 cn)


end TensorIndex

end TensorStructure
