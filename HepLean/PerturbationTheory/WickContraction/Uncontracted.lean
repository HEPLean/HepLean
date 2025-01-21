/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.Basic
/-!

# Uncontracted elements

-/
open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List

/-- Given a Wick contraction, the finset of elements of `Fin n` which are not contracted. -/
def uncontracted : Finset (Fin n) := Finset.filter (fun i => c.getDual? i = none) (Finset.univ)

lemma congr_uncontracted {n m : ℕ} (c : WickContraction n) (h : n = m) :
    (c.congr h).uncontracted = Finset.map (finCongr h).toEmbedding c.uncontracted := by
  subst h
  simp

/-- The equivalence of `Option c.uncontracted` for two propositionally equal Wick contractions. -/
def uncontractedCongr {c c': WickContraction n} (h : c = c') :
    Option c.uncontracted ≃ Option c'.uncontracted :=
    Equiv.optionCongr (Equiv.subtypeEquivRight (by rw [h]; simp))

@[simp]
lemma uncontractedCongr_none {c c': WickContraction n} (h : c = c') :
    (uncontractedCongr h) none = none := by
  simp [uncontractedCongr]

@[simp]
lemma uncontractedCongr_some {c c': WickContraction n} (h : c = c') (i : c.uncontracted) :
    (uncontractedCongr h) (some i) = some (Equiv.subtypeEquivRight (by rw [h]; simp) i) := by
  simp [uncontractedCongr]

lemma mem_uncontracted_iff_not_contracted (i : Fin n) :
    i ∈ c.uncontracted ↔ ∀ p ∈ c.1, i ∉ p := by
  simp only [uncontracted, getDual?, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Iff.intro
  · intro h p hp
    have hp := c.2.1 p hp
    rw [Finset.card_eq_two] at hp
    obtain ⟨a, b, ha, hb, hab⟩ := hp
    rw [Fin.find_eq_none_iff] at h
    by_contra hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with hn | hn
    · subst hn
      exact h b hp
    · subst hn
      rw [Finset.pair_comm] at hp
      exact h a hp
  · intro h
    rw [Fin.find_eq_none_iff]
    by_contra hn
    simp only [not_forall, Decidable.not_not] at hn
    obtain ⟨j, hj⟩ := hn
    apply h {i, j} hj
    simp

end WickContraction
