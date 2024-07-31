/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Basic
import Init.NotationExtra
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

Further we plan to make easy to define tensors with indices. E.g. `(ψ : Tenᵘ¹ᵘ²ᵤ₃)`
  should correspond to a (real Lorentz) tensors with 3 indices, two upper and one lower.
  For `(ψ : Tenᵘ¹ᵘ²ᵤ₃)`, if one writes e.g. `ψᵤ₁ᵘ²ᵤ₃`, this should correspond to a
  lowering of the first index of `ψ`.

Further, it will be nice if we can have implicit contractions of indices
  e.g. in Weyl fermions.

-/
open Lean
open Lean
open Lean.Parser
open Lean.Elab
open Lean.Elab.Command
variable {R : Type} [CommSemiring R]

class IndexNotation (𝓣 : TensorStructure R) where
  nota : 𝓣.Color → Char

namespace IndexNotation

variable (𝓣 : TensorStructure R) [IndexNotation 𝓣]
variable [Fintype 𝓣.Color] [DecidableEq 𝓣.Color]

def IsIndexSpecifier (c : Char) : Bool :=
  if ∃ (μ : 𝓣.Color), c = nota μ then true else false

def IsIndexId (c : Char) : Bool :=
  if c = '₀' ∨ c = '₁' ∨ c = '₂' ∨ c = '₃' ∨ c = '₄' ∨ c = '₅' ∨ c = '₆'
  ∨ c = '₇' ∨ c = '₈' ∨ c = '₉' ∨ c = '⁰' ∨ c = '¹' ∨ c = '²' ∨ c = '³' ∨ c = '⁴'
  ∨ c = '⁵' ∨ c = '⁶' ∨ c = '⁷' ∨ c = '⁸' ∨ c = '⁹' then true else false

partial def takeWhileFnFstAux (n : ℕ) (p1 : Char → Bool) (p : Char → Bool) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.input.atEnd i then s
  else if ¬ ((n = 0 ∧ p1 (c.input.get' i h)) ∨ (n ≠ 0 ∧ p (c.input.get' i h))) then s
  else takeWhileFnFstAux n.succ p1 p c (s.next' c.input i h)

def takeWhileFnFst (p1 : Char → Bool) (p : Char → Bool) : ParserFn := takeWhileFnFstAux 0 p1 p

/-- Parser for index structures. -/
def indexParser : ParserFn :=  (takeWhileFnFst (IsIndexSpecifier 𝓣) IsIndexId)

def indexParserMany : ParserFn := Lean.Parser.many1Fn (indexParser 𝓣)

end IndexNotation
