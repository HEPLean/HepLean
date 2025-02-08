/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.Basic
import HepLean.PerturbationTheory.CreateAnnihilate
/-!

# Creation and annihilation states

Called `CrAnFieldOp` for short here.

Given a field specification, in addition to defining states
(see: `HepLean.PerturbationTheory.FieldSpecification.Basic`),
we can also define creation and annihilation states.
These are similar to states but come with an additional specification of whether they correspond to
creation or annihilation operators.

In particular we have the following creation and annihilation states for each field:
- Negative asymptotic states - with the implicit specification that it is a creation state.
- Position states with a creation specification.
- Position states with an annihilation specification.
- Positive asymptotic states - with the implicit specification that it is an annihilation state.

In this module in addition to defining `CrAnFieldOp` we also define some maps:
- The map `crAnFieldOpToFieldOp` takes a `CrAnFieldOp` to its state in `FieldOp`.
- The map `crAnFieldOpToCreateAnnihilate` takes a `CrAnFieldOp` to its corresponding
`CreateAnnihilate` value.
- The map `crAnStatistics` takes a `CrAnFieldOp` to its corresponding `FieldStatistic`
(bosonic or fermionic).

-/
namespace FieldSpecification
variable (𝓕 : FieldSpecification)

/-- To each field operator the specification of the type of creation and annihilation parts.
  For asymptotic states there is only one allowed part, whilst for position
  field operator there is two. -/
def fieldOpToCrAnType : 𝓕.FieldOp → Type
  | FieldOp.inAsymp _ => Unit
  | FieldOp.position _ => CreateAnnihilate
  | FieldOp.outAsymp _ => Unit

/-- The instance of a finite type on `𝓕.fieldOpToCreateAnnihilateType i`. -/
instance : ∀ i, Fintype (𝓕.fieldOpToCrAnType i) := fun i =>
  match i with
  | FieldOp.inAsymp _ => inferInstanceAs (Fintype Unit)
  | FieldOp.position _ => inferInstanceAs (Fintype CreateAnnihilate)
  | FieldOp.outAsymp _ => inferInstanceAs (Fintype Unit)

/-- The instance of a decidable equality on `𝓕.fieldOpToCreateAnnihilateType i`. -/
instance : ∀ i, DecidableEq (𝓕.fieldOpToCrAnType i) := fun i =>
  match i with
  | FieldOp.inAsymp _ => inferInstanceAs (DecidableEq Unit)
  | FieldOp.position _ => inferInstanceAs (DecidableEq CreateAnnihilate)
  | FieldOp.outAsymp _ => inferInstanceAs (DecidableEq Unit)

/-- The equivalence between `𝓕.fieldOpToCreateAnnihilateType i` and
  `𝓕.fieldOpToCreateAnnihilateType j` from an equality `i = j`. -/
def fieldOpToCreateAnnihilateTypeCongr : {i j : 𝓕.FieldOp} → i = j →
    𝓕.fieldOpToCrAnType i ≃ 𝓕.fieldOpToCrAnType j
  | _, _, rfl => Equiv.refl _

/--
For a field specification `𝓕`, elements in `𝓕.CrAnFieldOp`, the type
of creation and annihilation field operators, corresponds to
- an incoming asymptotic field operator `.inAsymp` in `𝓕.FieldOp`.
- a position operator `.position` in `𝓕.FieldOp` and an element of
  `CreateAnnihilate` specifying the creation or annihilation part of that position operator.
- an outgoing asymptotic field operator `.outAsymp` in `𝓕.FieldOp`.

Note that the incoming and outgoing asymptotic field operators are implicitly creation and
annihilation operators respectively.
-/
def CrAnFieldOp : Type := Σ (s : 𝓕.FieldOp), 𝓕.fieldOpToCrAnType s

/-- The map from creation and annihilation field operator to their underlying states. -/
def crAnFieldOpToFieldOp : 𝓕.CrAnFieldOp → 𝓕.FieldOp := Sigma.fst

@[simp]
lemma crAnFieldOpToFieldOp_prod (s : 𝓕.FieldOp) (t : 𝓕.fieldOpToCrAnType s) :
    𝓕.crAnFieldOpToFieldOp ⟨s, t⟩ = s := rfl

/-- The map from creation and annihilation states to the type `CreateAnnihilate`
  specifying if a state is a creation or an annihilation state. -/
def crAnFieldOpToCreateAnnihilate : 𝓕.CrAnFieldOp → CreateAnnihilate
  | ⟨FieldOp.inAsymp _, _⟩ => CreateAnnihilate.create
  | ⟨FieldOp.position _, CreateAnnihilate.create⟩ => CreateAnnihilate.create
  | ⟨FieldOp.position _, CreateAnnihilate.annihilate⟩ => CreateAnnihilate.annihilate
  | ⟨FieldOp.outAsymp _, _⟩ => CreateAnnihilate.annihilate

/-- For a field specification `𝓕`, and an element `φ` in `𝓕.CrAnFieldOp`, the field
  statistic `crAnStatistics φ` is defined to be the statistic associated with the field `𝓕.Field`
  (or `𝓕.FieldOp`) underlying `φ`.

  The following notation is used in relation to `crAnStatistics`:
  - For `φ` an element of `𝓕.CrAnFieldOp`, `𝓕 |>ₛ φ` is `crAnStatistics φ`.
  - For `φs` a list of `𝓕.CrAnFieldOp`, `𝓕 |>ₛ φs` is the product of `crAnStatistics φ` over
    the list `φs`.
-/
def crAnStatistics : 𝓕.CrAnFieldOp → FieldStatistic :=
  𝓕.fieldOpStatistic ∘ 𝓕.crAnFieldOpToFieldOp

@[inherit_doc crAnStatistics]
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ =>
    (crAnStatistics 𝓕) φ

@[inherit_doc crAnStatistics]
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ => FieldStatistic.ofList
    (crAnStatistics 𝓕) φ

/-- The `CreateAnnihilate` value of a `CrAnFieldOp`s, i.e. whether it is a creation or
  annihilation operator. -/
scoped[FieldSpecification] infixl:80 "|>ᶜ" =>
    crAnFieldOpToCreateAnnihilate

remark notation_remark := "When working with a field specification `𝓕` we will use
some notation within doc-strings and in code. The main notation used is:
- In doc-strings when field statistics occur in exchange signs we may drop the `𝓕 |>ₛ _`.
- In doc-strings we will often write lists of `FieldOp` or `CrAnFieldOp` `φs` as e.g. `φ₀…φₙ`,
  which should be interpreted within the context in which it appears.
- In doc-strings we may use e.g. `φᶜ` to indicate the creation part of an operator and
  `φᵃ` to indicate the annihilation part of an operator.

Some examples:
- `𝓢(φ, φs)` corresponds to `𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs)`
- `φ₀…φᵢ₋₁φᵢ₊₁…φₙ` corresponds to a (given) list `φs = φ₀…φₙ` with the element at the `i`th position
  removed.
"

end FieldSpecification
