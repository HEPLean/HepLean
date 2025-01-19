/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.Uncontracted
import HepLean.PerturbationTheory.Algebras.StateAlgebra.TimeOrder
import HepLean.PerturbationTheory.Algebras.OperatorAlgebra.TimeContraction
import HepLean.PerturbationTheory.Contractions.InsertList
/-!

# Involution associated with a contraction

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}
namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)
open HepLean.List
open FieldStatistic

def toInvolution : {f : Fin n → Fin n // Function.Involutive f} :=
  ⟨fun i => if h : (c.getDual? i).isSome then (c.getDual? i).get h else i, by
    intro i
    by_cases h : (c.getDual? i).isSome
    · simp [h]
    · simp [h]⟩

def fromInvolution (f : {f : Fin n → Fin n // Function.Involutive f}) : ContractionsNat n :=
  ⟨Finset.univ.filter (fun a => a.card = 2 ∧ ∃ i, {i, f.1 i} = a), by
  intro a
  simp
  intro h1 _ _
  exact h1, by
  intro a ha b hb
  simp at ha hb
  obtain ⟨i, hai⟩ := ha.2
  subst hai
  obtain ⟨j, hbj⟩ := hb.2
  subst hbj
  by_cases h : i = j
  · subst h
    simp
  · by_cases hi : i = f.1 j
    · subst hi
      simp
      rw [f.2]
      rw [@Finset.pair_comm]
    · apply Or.inr
      simp
      apply And.intro
      · apply And.intro
        · exact fun a => h a.symm
        · by_contra hn
          subst hn
          rw [f.2 i] at hi
          simp at hi
      · apply And.intro
        · exact fun a => hi a.symm
        · rw [Function.Injective.eq_iff]
          exact fun a => h (id (Eq.symm a))
          exact Function.Involutive.injective f.2⟩

@[simp]
lemma fromInvolution_getDual?_isSome (f : {f : Fin n → Fin n // Function.Involutive f})
    (i : Fin n) : ((fromInvolution f).getDual? i).isSome ↔ f.1 i ≠ i := by
  rw [getDual?_isSome_iff]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha⟩ := h
    have ha2 := a.2
    simp [fromInvolution, -Finset.coe_mem] at ha2
    obtain ⟨j, h⟩ := ha2.2
    rw [← h] at ha
    have hj : f.1 j ≠ j := by
      by_contra hn
      rw [hn] at h
      rw [← h] at ha2
      simp at ha2
    simp at ha
    rcases ha with ha | ha
    · subst ha
      exact hj
    · subst ha
      rw [f.2]
      exact id (Ne.symm hj)
  · intro hi
    use ⟨{i, f.1 i}, by
      simp [fromInvolution]
      rw [Finset.card_pair (id (Ne.symm hi))]⟩
    simp

lemma fromInvolution_getDual?_eq_some (f : {f : Fin n → Fin n // Function.Involutive f}) (i : Fin n)
    (h : ((fromInvolution f).getDual? i).isSome) :
    ((fromInvolution f).getDual? i) = some (f.1 i) := by
  rw [@getDual?_eq_some_iff_mem]
  simp [fromInvolution]
  apply Finset.card_pair
  simp at h
  exact fun a => h (id (Eq.symm a))

@[simp]
lemma fromInvolution_getDual?_get (f : {f : Fin n → Fin n // Function.Involutive f}) (i : Fin n)
    (h : ((fromInvolution f).getDual? i).isSome) :
    ((fromInvolution f).getDual? i).get h = (f.1 i) := by
  have h1 := fromInvolution_getDual?_eq_some f i h
  exact Option.get_of_mem h h1

lemma toInvolution_fromInvolution : fromInvolution c.toInvolution = c := by
  apply Subtype.eq
  simp [fromInvolution, toInvolution]
  ext a
  simp
  apply Iff.intro
  · intro h
    obtain ⟨i, hi⟩ := h.2
    split at hi
    · subst hi
      simp
    · simp at hi
      subst hi
      simp at h
  · intro ha
    apply And.intro (c.2.1 a ha)
    use c.fstFieldOfContract ⟨a, ha⟩
    simp
    change _ = (⟨a, ha⟩ : c.1).1
    conv_rhs => rw [finset_eq_fstFieldOfContract_sndFieldOfContract]

lemma fromInvolution_toInvolution (f : {f : Fin n → Fin n // Function.Involutive f}) :
    (fromInvolution f).toInvolution = f := by
  apply Subtype.eq
  funext i
  simp only [toInvolution, ne_eq, dite_not]
  split
  · rename_i h
    simp
  · rename_i h
    simp at h
    exact id (Eq.symm h)

def equivInvolution : ContractionsNat n ≃ {f : Fin n → Fin n // Function.Involutive f} where
  toFun := toInvolution
  invFun := fromInvolution
  left_inv := toInvolution_fromInvolution
  right_inv := fromInvolution_toInvolution

end ContractionsNat

end FieldStruct
