/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.Basic
/-!

# Uncontracted elements


-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)
open HepLean.List

def uncontracted : Finset (Fin n) := Finset.filter (fun i => c.getDual? i = none) (Finset.univ)

lemma congr_uncontracted {n m : ℕ} (c : ContractionsNat n) (h : n = m) :
    (c.congr h).uncontracted = Finset.map (finCongr h).toEmbedding c.uncontracted := by
  subst h
  simp

def uncontractedCongr {c c': ContractionsNat n} (h : c = c') :
    Option c.uncontracted ≃ Option c'.uncontracted :=
    Equiv.optionCongr (Equiv.subtypeEquivRight (by rw [h]; simp))

@[simp]
lemma uncontractedCongr_none {c c': ContractionsNat n} (h : c = c') :
    (uncontractedCongr h) none = none := by
  simp [uncontractedCongr]

@[simp]
lemma uncontractedCongr_some {c c': ContractionsNat n} (h : c = c') (i : c.uncontracted) :
    (uncontractedCongr h) (some i) = some (Equiv.subtypeEquivRight (by rw [h]; simp) i) := by
  simp [uncontractedCongr]


lemma mem_uncontracted_iff_not_contracted (i : Fin n)  :
    i ∈ c.uncontracted ↔ ∀ p ∈ c.1, i ∉ p := by
  simp [uncontracted, getDual?]
  apply Iff.intro
  · intro h p hp
    have hp := c.2.1 p hp
    rw [Finset.card_eq_two] at hp
    obtain ⟨a, b, ha, hb, hab⟩ := hp
    rw [Fin.find_eq_none_iff] at h
    by_contra hn
    simp at hn
    rcases hn with hn | hn
    · subst hn
      exact h b hp
    · subst hn
      rw [Finset.pair_comm] at hp
      exact h a hp
  · intro h
    rw [Fin.find_eq_none_iff]
    by_contra hn
    simp at hn
    obtain ⟨j, hj⟩ := hn
    apply h {i, j} hj
    simp

end ContractionsNat

end FieldStruct
