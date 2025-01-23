/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.Basic
import HepLean.PerturbationTheory.CreateAnnihilate
/-!

# Creation and annihilation states

Called `CrAnStates` for short here.

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

In this module in addition to defining `CrAnStates` we also define some maps:
- The map `crAnStatesToStates` takes a `CrAnStates` to its state in `States`.
- The map `crAnStatesToCreateAnnihilate` takes a `CrAnStates` to its corresponding
`CreateAnnihilate` value.
- The map `crAnStatistics` takes a `CrAnStates` to its corresponding `FieldStatistic`
(bosonic or fermionic).

-/
namespace FieldSpecification
variable (𝓕 : FieldSpecification)

/-- To each state the specificaition of the type of creation and annihlation parts.
  For asymptotic staes there is only one allowed part, whilst for position states
  there is two. -/
def statesToCrAnType : 𝓕.States → Type
  | States.inAsymp _ => Unit
  | States.position _ => CreateAnnihilate
  | States.outAsymp _ => Unit

/-- The instance of a finite type on `𝓕.statesToCreateAnnihilateType i`. -/
instance : ∀ i, Fintype (𝓕.statesToCrAnType i) := fun i =>
  match i with
  | States.inAsymp _ => inferInstanceAs (Fintype Unit)
  | States.position _ => inferInstanceAs (Fintype CreateAnnihilate)
  | States.outAsymp _ => inferInstanceAs (Fintype Unit)

/-- The instance of a decidable equality on `𝓕.statesToCreateAnnihilateType i`. -/
instance : ∀ i, DecidableEq (𝓕.statesToCrAnType i) := fun i =>
  match i with
  | States.inAsymp _ => inferInstanceAs (DecidableEq Unit)
  | States.position _ => inferInstanceAs (DecidableEq CreateAnnihilate)
  | States.outAsymp _ => inferInstanceAs (DecidableEq Unit)

/-- The equivalence between `𝓕.statesToCreateAnnihilateType i` and
  `𝓕.statesToCreateAnnihilateType j` from an equality `i = j`. -/
def statesToCreateAnnihilateTypeCongr : {i j : 𝓕.States} → i = j →
    𝓕.statesToCrAnType i ≃ 𝓕.statesToCrAnType j
  | _, _, rfl => Equiv.refl _

/-- A creation and annihlation state is a state plus an valid specification of the
  creation or annihliation part of that state. (For asympotic states there is only one valid
  choice). -/
def CrAnStates : Type := Σ (s : 𝓕.States), 𝓕.statesToCrAnType s

/-- The map from creation and annihlation states to their underlying states. -/
def crAnStatesToStates : 𝓕.CrAnStates → 𝓕.States := Sigma.fst

@[simp]
lemma crAnStatesToStates_prod (s : 𝓕.States) (t : 𝓕.statesToCrAnType s) :
    𝓕.crAnStatesToStates ⟨s, t⟩ = s := rfl

/-- The map from creation and annihlation states to the type `CreateAnnihilate`
  specifying if a state is a creation or an annihilation state. -/
def crAnStatesToCreateAnnihilate : 𝓕.CrAnStates → CreateAnnihilate
  | ⟨States.inAsymp _, _⟩ => CreateAnnihilate.create
  | ⟨States.position _, CreateAnnihilate.create⟩ => CreateAnnihilate.create
  | ⟨States.position _, CreateAnnihilate.annihilate⟩ => CreateAnnihilate.annihilate
  | ⟨States.outAsymp _, _⟩ => CreateAnnihilate.annihilate

/-- Takes a `CrAnStates` state to its corresponding fields statistic (bosonic or fermionic). -/
def crAnStatistics : 𝓕.CrAnStates → FieldStatistic :=
  𝓕.statesStatistic ∘ 𝓕.crAnStatesToStates

/-- The field statistic of a `CrAnState`. -/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ =>
    (crAnStatistics 𝓕) φ

/-- The field statistic of a list of `CrAnState`s. -/
scoped[FieldSpecification] notation 𝓕 "|>ₛ" φ => FieldStatistic.ofList
    (crAnStatistics 𝓕) φ

/-- The `CreateAnnihilate` value of a `CrAnState`s, i.e. whether it is a creation or
  annihilation operator. -/
scoped[FieldSpecification] infixl:80 "|>ᶜ" =>
    crAnStatesToCreateAnnihilate

end FieldSpecification
