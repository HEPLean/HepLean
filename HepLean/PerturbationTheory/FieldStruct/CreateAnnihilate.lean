/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldStruct.Basic
import HepLean.PerturbationTheory.CreateAnnihilate
/-!

# Creation and annihlation parts of fields

-/

namespace FieldStruct
variable (𝓕 : FieldStruct)

/-- To each state the specificaition of the type of creation and annihlation parts.
  For asymptotic staes there is only one allowed part, whilst for position states
  there is two. -/
def statesToCrAnType : 𝓕.States → Type
  | States.negAsymp _ => Unit
  | States.position _ => CreateAnnihilate
  | States.posAsymp _ => Unit

/-- The instance of a finite type on `𝓕.statesToCreateAnnihilateType i`. -/
instance : ∀ i, Fintype (𝓕.statesToCrAnType i) := fun i =>
  match i with
  | States.negAsymp _ => inferInstanceAs (Fintype Unit)
  | States.position _ => inferInstanceAs (Fintype CreateAnnihilate)
  | States.posAsymp _ => inferInstanceAs (Fintype Unit)

/-- The instance of a decidable equality on `𝓕.statesToCreateAnnihilateType i`. -/
instance : ∀ i, DecidableEq (𝓕.statesToCrAnType i) := fun i =>
  match i with
  | States.negAsymp _ => inferInstanceAs (DecidableEq Unit)
  | States.position _ => inferInstanceAs (DecidableEq CreateAnnihilate)
  | States.posAsymp _ => inferInstanceAs (DecidableEq Unit)

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
  | ⟨States.negAsymp _, _⟩ => CreateAnnihilate.create
  | ⟨States.position _, CreateAnnihilate.create⟩ => CreateAnnihilate.create
  | ⟨States.position _, CreateAnnihilate.annihilate⟩ => CreateAnnihilate.annihilate
  | ⟨States.posAsymp _, _⟩ => CreateAnnihilate.annihilate

def crAnStatesStatistics : 𝓕.CrAnStates → FieldStatistic :=
  𝓕.statesStatistic ∘ 𝓕.crAnStatesToStates

def crAnListStatistics (φs : List 𝓕.CrAnStates) : FieldStatistic :=
  (List.map 𝓕.crAnStatesStatistics φs).prod

end FieldStruct
