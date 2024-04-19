/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.SMNu.PlusU1.Basic
import HepLean.AnomalyCancellation.SMNu.PlusU1.FamilyMaps
import HepLean.AnomalyCancellation.SMNu.PlusU1.PlaneNonSols

universe v u

namespace SMRHN
namespace PlusU1

open SMνCharges
open SMνACCs
open BigOperators

def existsPlane (n : ℕ) : Prop := ∃ (B : Fin n → (PlusU1 3).charges),
   LinearIndependent ℚ B ∧ ∀ (f : Fin n → ℚ), (PlusU1 3).isSolution (∑ i, f i • B i)

lemma exists_plane_exists_basis {n : ℕ} (hE : existsPlane n) :
    ∃ (B : Fin 11 ⊕ Fin n → (PlusU1 3).charges), LinearIndependent ℚ B := by
  obtain ⟨E, hE1, hE2⟩ := hE
  obtain ⟨B, hB1, hB2⟩ := eleven_dim_plane_of_no_sols_exists
  let Y := Sum.elim B E
  use Y
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  rw [@Fintype.sum_sum_type] at hg
  rw [@add_eq_zero_iff_eq_neg] at hg
  rw [← @Finset.sum_neg_distrib] at hg
  have h1 : ∑ x : Fin n, -(g (Sum.inr x) • Y (Sum.inr x)) =
      ∑ x : Fin n, (-g (Sum.inr x)) • Y (Sum.inr x):= by
    apply Finset.sum_congr
    simp
    intro i _
    simp
  rw [h1] at hg
  have h2 : ∑ a₁ : Fin 11, g (Sum.inl a₁) • Y (Sum.inl a₁) = 0 := by
    apply hB2
    erw [hg]
    exact hE2 fun i => -g (Sum.inr i)
  rw [Fintype.linearIndependent_iff] at hB1 hE1
  have h3 : ∀ i, g (Sum.inl i) = 0 := hB1 (fun i => (g (Sum.inl i))) h2
  rw [h2] at hg
  have h4 : ∀ i, - g (Sum.inr i) = 0 := hE1 (fun i => (- g (Sum.inr i))) hg.symm
  simp at h4
  intro i
  match i with
  | Sum.inl i => exact h3 i
  | Sum.inr i => exact h4 i


theorem plane_exists_dim_le_7 {n : ℕ} (hn : existsPlane n) : n ≤ 7 := by
  obtain ⟨B, hB⟩ := exists_plane_exists_basis hn
  have h1 := LinearIndependent.fintype_card_le_finrank hB
  simp at h1
  rw [show FiniteDimensional.finrank ℚ (PlusU1 3).charges = 18 from
    FiniteDimensional.finrank_fin_fun ℚ] at h1
  exact Nat.le_of_add_le_add_left h1


end PlusU1
end SMRHN
