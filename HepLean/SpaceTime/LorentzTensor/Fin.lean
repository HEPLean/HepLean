/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Lorentz tensors indexed by Fin n

In physics, in many (if not all) cases, we index our Lorentz tensors by `Fin n`.

In this file we set up the machinery to deal with Lorentz tensors indexed by `Fin n`
in a way that is convenient for physicists, and general caculation.

## Note

This file is currently a stub.

-/

open TensorProduct

noncomputable section

namespace TensorStructure

variable {n m : ℕ}

variable {R : Type} [CommSemiring R] (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color}
  {cW : W → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}
  {cn : Fin n → 𝓣.Color} {cm : Fin m → 𝓣.Color}

/-- Casting a tensor defined on `Fin n` to `Fin m` where `n = m`. -/
@[simp]
def finCast (h : n = m) (hc : cn = cm ∘ Fin.castOrderIso h) : 𝓣.Tensor cn ≃ₗ[R] 𝓣.Tensor cm :=
  𝓣.mapIso (Fin.castOrderIso h) hc

/-- An equivalence between `𝓣.Tensor cn ⊗[R] 𝓣.Tensor cm` indexed by `Fin n` and `Fin m`,
  and `𝓣.Tensor (Sum.elim cn cm ∘ finSumFinEquiv.symm)` indexed by `Fin (n + m)`. -/
@[simp]
def finSumEquiv : 𝓣.Tensor cn ⊗[R] 𝓣.Tensor cm ≃ₗ[R]
    𝓣.Tensor (Sum.elim cn cm ∘ finSumFinEquiv.symm) :=
  (𝓣.tensoratorEquiv cn cm).trans (𝓣.mapIso finSumFinEquiv (by funext a; simp))

end TensorStructure

end
