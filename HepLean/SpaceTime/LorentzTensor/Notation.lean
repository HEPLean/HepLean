/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Notation for Lorentz Tensors

This file is currently a stub.

We plan to set up index-notation for dealing with tensors.

Some examples:

- `ψᵘ¹ᵘ²φᵤ₁` should correspond to the contraction of the first index of `ψ` and the
  only index of `φ`.
- `ψᵘ¹ᵘ² = ψᵘ²ᵘ¹` should define the symmetry of `ψ` under the exchange of its indices.
- `θᵤ₂(ψᵘ¹ᵘ²φᵤ₁) = (θᵤ₂ψᵘ¹ᵘ²)φᵤ₁` should correspond to an associativity properity of
  contraction.

It should also be possible to define this generically for any `LorentzTensorStructure`.

-/
