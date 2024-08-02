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

structure TensorIndex (cn : Fin n → 𝓣.Color) where
  tensor : 𝓣.Tensor cn
  index : IndexListColor 𝓣.toTensorColor
  nat_eq : n = index.1.length
  quot_eq : 𝓣.colorQuot ∘ index.1.colorMap ∘ Fin.cast nat_eq = 𝓣.colorQuot ∘ cn

namespace TensorIndex

variable {𝓣 : TensorStructure R} [IndexNotation 𝓣.Color] [Fintype 𝓣.Color] [DecidableEq 𝓣.Color]
variable {n m : ℕ} {cn : Fin n → 𝓣.Color} {cm : Fin m → 𝓣.Color} (T : TensorIndex 𝓣 cn)
section noncomputable

def smul (r : R) : TensorIndex 𝓣 cn := ⟨r • T.tensor, T.index, T.nat_eq, T.quot_eq⟩

end

end TensorIndex

end TensorStructure
