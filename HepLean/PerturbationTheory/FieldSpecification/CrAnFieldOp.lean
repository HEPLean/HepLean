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

/-- To each field operator the specificaition of the type of creation and annihlation parts.
  For asymptotic staes there is only one allowed part, whilst for position
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
For a field specification `𝓕`, the type `𝓕.CrAnFieldOp` is defined such that every element
corresponds to
- an incoming asymptotic field operator `.inAsymp` and the unique element of `Unit`,
  corresponding to the statement that an `inAsymp` state is a creation operator.
- a position operator `.position` and an element of `CreateAnnihilate`,
  corresponding to either the creation part or the annihilation part of a position operator.
- an outgoing asymptotic field operator `.outAsymp` and the unique element of `Unit`,
  corresponding to the statement that an `outAsymp` state is an annihilation operator.
-/
def CrAnFieldOp : Type := Σ (s : 𝓕.FieldOp), 𝓕.fieldOpToCrAnType s

/-- The map from creation and annihlation field operator to their underlying states. -/
def crAnFieldOpToFieldOp : 𝓕.CrAnFieldOp → 𝓕.FieldOp := Sigma.fst

@[simp]
lemma crAnFieldOpToFieldOp_prod (s : 𝓕.FieldOp) (t : 𝓕.fieldOpToCrAnType s) :
    𝓕.crAnFieldOpToFieldOp ⟨s, t⟩ = s := rfl

/-- The map from creation and annihlation states to the type `CreateAnnihilate`
  specifying if a state is a creation or an annihilation state. -/
def crAnFieldOpToCreateAnnihilate : 𝓕.CrAnFieldOp → CreateAnnihilate
  | ⟨FieldOp.inAsymp _, _⟩ => CreateAnnihilate.create
  | ⟨FieldOp.position _, CreateAnnihilate.create⟩ => CreateAnnihilate.create
  | ⟨FieldOp.position _, CreateAnnihilate.annihilate⟩ => CreateAnnihilate.annihilate
  | ⟨FieldOp.outAsymp _, _⟩ => CreateAnnihilate.annihilate

/-- Takes a `CrAnFieldOp` state to its corresponding fields statistic (bosonic or fermionic). -/
def crAnStatistics : 𝓕.CrAnFieldOp → FieldStatistic :=
  𝓕.statesStatistic ∘ 𝓕.crAnFieldOpToFieldOp

/-- The field statistic of a `CrAnFieldOp`. -/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ =>
    (crAnStatistics 𝓕) φ

/-- The field statistic of a list of `CrAnFieldOp`s. -/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ => FieldStatistic.ofList
    (crAnStatistics 𝓕) φ

/-- The `CreateAnnihilate` value of a `CrAnFieldOp`s, i.e. whether it is a creation or
  annihilation operator. -/
scoped[FieldSpecification] infixl:80 "|>ᶜ" =>
    crAnFieldOpToCreateAnnihilate

end FieldSpecification
