/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.PerturbationTheory.FieldSpecification.Basic
import PhysLean.PerturbationTheory.CreateAnnihilate
/-!

# Creation and annihilation states

Called `CrAnFieldOp` for short here.

Given a field specification, in addition to defining states
(see: `PhysLean.PerturbationTheory.FieldSpecification.Basic`),
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
For a field specification `𝓕`, the (sigma) type `𝓕.CrAnFieldOp`
corresponds to the type of creation and annihilation parts of field operators.
It formally defined to consist of the following elements:
- For each incoming asymptotic field operator `φ` in `𝓕.FieldOp` an element
  written as `⟨φ, ()⟩` in `𝓕.CrAnFieldOp`, corresponding to the creation part of `φ`.
  Here `φ` has no annihilation part. (Here `()` is the unique element of `Unit`.)
- For each position field operator `φ` in `𝓕.FieldOp` an element of `𝓕.CrAnFieldOp`
  written as `⟨φ, .create⟩`, corresponding to the creation part of `φ`.
- For each position field operator `φ` in `𝓕.FieldOp` an element of `𝓕.CrAnFieldOp`
  written as `⟨φ, .annihilate⟩`, corresponding to the annihilation part of `φ`.
- For each outgoing asymptotic field operator `φ` in `𝓕.FieldOp` an element
  written as `⟨φ, ()⟩` in `𝓕.CrAnFieldOp`, corresponding to the annihilation part of `φ`.
  Here `φ` has no creation part. (Here `()` is the unique element of `Unit`.)

As an example, if `f` corresponds to a Weyl-fermion field, it would contribute
  the following elements to `𝓕.CrAnFieldOp`
- For each spin `s`, an element corresponding to an incoming asymptotic operator: `a(p, s)`.
- For each each Lorentz
  index `a`, an element corresponding to the creation part of a position operator:

  `∑ s, ∫ d³p/(…) (xₐ (p,s)  a(p, s) e ^ (-i p x))`.
- For each each Lorentz
  index `a`,an element corresponding to annihilation part of a position operator:

  `∑ s, ∫ d³p/(…) (yₐ(p,s) a†(p, s) e ^ (-i p x))`.
- For each spin `s`, element corresponding to an outgoing asymptotic operator: `a†(p, s)`.

-/
def CrAnFieldOp : Type := Σ (s : 𝓕.FieldOp), 𝓕.fieldOpToCrAnType s

/-- The map from creation and annihilation field operator to their underlying states. -/
def crAnFieldOpToFieldOp : 𝓕.CrAnFieldOp → 𝓕.FieldOp := Sigma.fst

@[simp]
lemma crAnFieldOpToFieldOp_prod (s : 𝓕.FieldOp) (t : 𝓕.fieldOpToCrAnType s) :
    𝓕.crAnFieldOpToFieldOp ⟨s, t⟩ = s := rfl

/-- For a field specification `𝓕`, `𝓕.crAnFieldOpToCreateAnnihilate` is the map from
  `𝓕.CrAnFieldOp` to `CreateAnnihilate` taking `φ` to `create` if
- `φ` corresponds to an incoming asymptotic field operator or the creation part of a position based
  field operator.

otherwise it takes `φ` to `annihilate`.
 -/
def crAnFieldOpToCreateAnnihilate : 𝓕.CrAnFieldOp → CreateAnnihilate
  | ⟨FieldOp.inAsymp _, _⟩ => CreateAnnihilate.create
  | ⟨FieldOp.position _, CreateAnnihilate.create⟩ => CreateAnnihilate.create
  | ⟨FieldOp.position _, CreateAnnihilate.annihilate⟩ => CreateAnnihilate.annihilate
  | ⟨FieldOp.outAsymp _, _⟩ => CreateAnnihilate.annihilate

/-- For a field specification `𝓕`, and an element `φ` in `𝓕.CrAnFieldOp`, the field
  statistic `crAnStatistics φ` is defined to be the statistic associated with the field `𝓕.Field`
  (or the `𝓕.FieldOp`) underlying `φ`.

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

remark notation_remark := "When working with a field specification `𝓕` the
following notation will be used within doc-strings:
- when field statistics occur in exchange signs the `𝓕 |>ₛ _` may be dropped.
- lists of `FieldOp` or `CrAnFieldOp` `φs` may be written as `φ₀…φₙ`,
  which should be interpreted within the context in which it appears.
- `φᶜ` may be used to indicate the creation part of an operator and
  `φᵃ` to indicate the annihilation part of an operator.

Some examples of these notation-conventions are:
- `𝓢(φ, φs)` which corresponds to `𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ φs)`
- `φ₀…φᵢ₋₁φᵢ₊₁…φₙ` which corresponds to a (given) list `φs = φ₀…φₙ` with the element at the
  `i`th position removed.
"

end FieldSpecification
