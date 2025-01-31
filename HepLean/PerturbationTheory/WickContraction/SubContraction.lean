/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.WickContraction.StaticContract
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.TimeContraction
/-!

# Sub  contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
open HepLean.List
open FieldOpAlgebra

def subContraction (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) : WickContraction φs.length :=
  ⟨S, by
    intro i hi
    exact φsΛ.2.1 i (ha hi),
    by
    intro i hi j hj
    exact φsΛ.2.2 i (ha hi) j (ha hj)⟩

lemma mem_of_mem_subContraction {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin φs.length)} (ha : a ∈ (φsΛ.subContraction S hs).1) : a ∈ φsΛ.1 := by
  exact hs ha

def quotContraction (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    WickContraction [φsΛ.subContraction S ha]ᵘᶜ.length :=
  ⟨Finset.filter (fun a => Finset.map uncontractedListEmd a ∈ φsΛ.1) Finset.univ,
  by
    intro a ha'
    simp at ha'
    simpa using  φsΛ.2.1 (Finset.map uncontractedListEmd a) ha'
    , by
  intro a ha b hb
  simp at ha hb
  by_cases hab : a = b
  · simp [hab]
  · simp [hab]
    have hx := φsΛ.2.2 (Finset.map uncontractedListEmd a) ha (Finset.map uncontractedListEmd b) hb
    simp_all⟩

lemma mem_of_mem_quotContraction {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin [φsΛ.subContraction S hs]ᵘᶜ.length)}
    (ha : a ∈ (quotContraction S hs).1) : Finset.map uncontractedListEmd a ∈ φsΛ.1 := by
  simp [quotContraction] at ha
  exact ha

lemma mem_subContraction_or_quotContraction {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Finset (Fin φs.length)} (ha : a ∈ φsΛ.1) :
    a ∈ (φsΛ.subContraction S hs).1 ∨
    ∃ a', Finset.map uncontractedListEmd a' = a ∧ a' ∈ (quotContraction S hs).1 := by
  by_cases h1 : a ∈ (φsΛ.subContraction S hs).1
  · simp [h1]
  simp [h1]
  simp [subContraction] at h1
  have h2 := φsΛ.2.1 a ha
  rw [@Finset.card_eq_two] at h2
  obtain ⟨i, j, hij, rfl⟩ := h2
  have hi : i ∈ (φsΛ.subContraction S hs).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    intro p hp
    have hp' : p ∈ φsΛ.1 := hs hp
    have hp2 := φsΛ.2.2 p hp' {i, j} ha
    simp [subContraction] at hp
    rcases hp2 with hp2 | hp2
    · simp_all
    simp at hp2
    exact hp2.1
  have hj : j ∈ (φsΛ.subContraction S hs).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    intro p hp
    have hp' : p ∈ φsΛ.1 := hs hp
    have hp2 := φsΛ.2.2 p hp' {i, j} ha
    simp [subContraction] at hp
    rcases hp2 with hp2 | hp2
    · simp_all
    simp at hp2
    exact hp2.2
  obtain ⟨i, rfl⟩ := uncontractedListEmd_surjective_mem_uncontracted i hi
  obtain ⟨j, rfl⟩ := uncontractedListEmd_surjective_mem_uncontracted j hj
  use {i, j}
  simp [quotContraction]
  exact ha

@[simp]
lemma subContraction_uncontractedList_get {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    {a : Fin [subContraction S hs]ᵘᶜ.length} :
    [subContraction S hs]ᵘᶜ[a] = φs[uncontractedListEmd a] := by
  erw [← getElem_uncontractedListEmd]
  rfl

@[simp]
lemma quotContraction_fstFieldOfContract_uncontractedListEmd {S : Finset (Finset (Fin φs.length))}
    {hs : S ⊆ φsΛ.1} (a : (quotContraction S hs).1) :
    uncontractedListEmd ((quotContraction S hs).fstFieldOfContract a) =
    (φsΛ.fstFieldOfContract ⟨Finset.map uncontractedListEmd a.1, mem_of_mem_quotContraction a.2⟩) := by
  symm
  apply eq_fstFieldOfContract_of_mem _ _ _ (uncontractedListEmd ((quotContraction S hs).sndFieldOfContract a) )
  · simp only [Finset.mem_map', fstFieldOfContract_mem]
  · simp
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract (quotContraction S hs) a

@[simp]
lemma quotContraction_sndFieldOfContract_uncontractedListEmd {S : Finset (Finset (Fin φs.length))}
    {hs : S ⊆ φsΛ.1} (a : (quotContraction S hs).1) :
    uncontractedListEmd ((quotContraction S hs).sndFieldOfContract a) =
    (φsΛ.sndFieldOfContract ⟨Finset.map uncontractedListEmd a.1, mem_of_mem_quotContraction a.2⟩) := by
  symm
  apply eq_sndFieldOfContract_of_mem _ _ (uncontractedListEmd ((quotContraction S hs).fstFieldOfContract a) )
  · simp only [Finset.mem_map', fstFieldOfContract_mem]
  · simp
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract (quotContraction S hs) a

lemma quotContraction_gradingCompliant {S : Finset (Finset (Fin φs.length))} {hs : S ⊆ φsΛ.1}
    (hsΛ : φsΛ.GradingCompliant) :
    GradingCompliant [φsΛ.subContraction S hs]ᵘᶜ (quotContraction S hs) := by
  simp [GradingCompliant]
  intro a ha
  have h1' := mem_of_mem_quotContraction ha
  erw [subContraction_uncontractedList_get]
  erw [subContraction_uncontractedList_get]
  simp
  apply hsΛ


end WickContraction
