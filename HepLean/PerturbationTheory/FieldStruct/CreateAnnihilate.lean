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
def statesToCreateAnnihilateType : 𝓕.States → Type
  | States.negAsymp _ => Unit
  | States.position _ => CreateAnnihilate
  | States.posAsymp _ => Unit

/-- The instance of a finite type on `𝓕.statesToCreateAnnihilateType i`. -/
instance : ∀ i, Fintype (𝓕.statesToCreateAnnihilateType i) := fun i =>
  match i with
  | States.negAsymp _ => inferInstanceAs (Fintype Unit)
  | States.position _ => inferInstanceAs (Fintype CreateAnnihilate)
  | States.posAsymp _ => inferInstanceAs (Fintype Unit)

/-- The instance of a decidable equality on `𝓕.statesToCreateAnnihilateType i`. -/
instance : ∀ i, DecidableEq (𝓕.statesToCreateAnnihilateType i) := fun i =>
  match i with
  | States.negAsymp _ => inferInstanceAs (DecidableEq Unit)
  | States.position _ => inferInstanceAs (DecidableEq CreateAnnihilate)
  | States.posAsymp _ => inferInstanceAs (DecidableEq Unit)

/-- The equivalence between `𝓕.statesToCreateAnnihilateType i` and
  `𝓕.statesToCreateAnnihilateType j` from an equality `i = j`. -/
def statesToCreateAnnihilateTypeCongr : {i j : 𝓕.States} → i = j →
  𝓕.statesToCreateAnnihilateType i ≃ 𝓕.statesToCreateAnnihilateType j
  | _, _, rfl => Equiv.refl _

/-- A creation and annihlation state is a state plus an valid specification of the
  creation or annihliation part of that state. (For asympotic states there is only one valid
  choice). -/
def CreateAnnihilateStates : Type := Σ (s : 𝓕.States), 𝓕.statesToCreateAnnihilateType s

/-- The map from creation and annihlation states to their underlying states. -/
def createAnnihilateStatesToStates : 𝓕.CreateAnnihilateStates → 𝓕.States := Sigma.fst

@[simp]
lemma createAnnihilateStatesToStates_prod (s : 𝓕.States) (t : 𝓕.statesToCreateAnnihilateType s) :
  𝓕.createAnnihilateStatesToStates ⟨s, t⟩ = s := rfl

/-- The map from creation and annihlation states to the type `CreateAnnihilate`
  specifying if a state is a creation or an annihilation state. -/
def createAnnihlateStatesToCreateAnnihilate : 𝓕.CreateAnnihilateStates → CreateAnnihilate
  | ⟨States.negAsymp _, _⟩ => CreateAnnihilate.create
  | ⟨States.position _, CreateAnnihilate.create⟩ => CreateAnnihilate.create
  | ⟨States.position _, CreateAnnihilate.annihilate⟩ => CreateAnnihilate.annihilate
  | ⟨States.posAsymp _, _⟩ => CreateAnnihilate.annihilate

/-- The normal ordering on creation and annihlation states. -/
def normalOrder : 𝓕.CreateAnnihilateStates → 𝓕.CreateAnnihilateStates → Prop :=
  fun a b => CreateAnnihilate.normalOrder (𝓕.createAnnihlateStatesToCreateAnnihilate a)
    (𝓕.createAnnihlateStatesToCreateAnnihilate b)

/-- Normal ordering is total. -/
instance : IsTotal 𝓕.CreateAnnihilateStates 𝓕.normalOrder where
  total _ _ := total_of CreateAnnihilate.normalOrder _ _

/-- Normal ordering is transitive. -/
instance : IsTrans 𝓕.CreateAnnihilateStates 𝓕.normalOrder where
  trans _ _ _ := fun h h' => IsTrans.trans (α := CreateAnnihilate) _ _ _ h h'

end FieldStruct
