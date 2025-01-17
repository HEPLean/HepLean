/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Contractions.Insert
/-!

# Equivalence extracting element from contraction


-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

namespace ContractionsNat
variable {n : ℕ} (c : ContractionsNat n)
open HepLean.List
open HepLean.Fin


lemma extractEquiv_equiv {c1 c2 : (c : ContractionsNat n) × Option c.uncontracted}
    (h : c1.1 = c2.1) (ho : c1.2 = uncontractedCongr (by rw [h]) c2.2) : c1 = c2 := by
  cases c1
  cases c2
  simp_all
  simp at h
  subst h
  simp [uncontractedCongr]
  rename_i a
  match a with
  | none => simp
  | some a =>
    simp
    ext
    simp


def extractEquiv (i : Fin n.succ) : ContractionsNat n.succ ≃
    (c : ContractionsNat n) × Option c.uncontracted  where
  toFun := fun c => ⟨erase c i, getDualErase c i⟩
  invFun := fun ⟨c, j⟩ => insert c i j
  left_inv f := by
    simp
  right_inv f := by
    refine extractEquiv_equiv ?_ ?_
    simp
    simp
    have h1 := insert_getDualErase f.fst i f.snd
    exact insert_getDualErase _ i _

lemma extractEquiv_symm_none_uncontracted (i : Fin n.succ)  (c : ContractionsNat n) :
    ((extractEquiv i).symm ⟨c, none⟩).uncontracted =
    (Insert.insert i (c.uncontracted.map i.succAboveEmb)) := by
  exact insert_none_uncontracted c i

@[simp]
lemma extractEquiv_apply_congr_symm_apply {n m : ℕ} (k : ℕ)
    (hnk :  k < n.succ) (hkm : k < m.succ) (hnm : n = m) (c : ContractionsNat n)
     (i  : c.uncontracted) :
    congr (by rw [hnm]) ((extractEquiv ⟨k, hkm⟩
    (congr (by rw [hnm]) ((extractEquiv ⟨k, hnk⟩).symm ⟨c, i⟩)))).1 = c := by
  subst hnm
  simp

instance fintype_zero : Fintype (ContractionsNat 0) where
  elems := {nil}
  complete := by
    intro c
    simp
    apply Subtype.eq
    simp [nil]
    ext a
    apply Iff.intro
    · intro h
      have hc := c.2.1 a h
      rw [Finset.card_eq_two] at hc
      obtain ⟨x, y, hxy, ha⟩ := hc
      exact Fin.elim0 x
    · simp

lemma sum_contractionsNat_nil (f : ContractionsNat 0 → M) [AddCommMonoid M] :
    ∑ c, f c = f nil := by
  rw [Finset.sum_eq_single_of_mem]
  simp
  intro b hb
  fin_cases b
  simp

instance fintype_succ : (n : ℕ) → Fintype (ContractionsNat n)
  | 0 => fintype_zero
  | Nat.succ n => by
    letI := fintype_succ n
    exact Fintype.ofEquiv _ (extractEquiv 0).symm


lemma sum_extractEquiv_congr [AddCommMonoid M] {n m : ℕ} (i : Fin n) (f : ContractionsNat n → M)
    (h : n = m.succ) :
    ∑ c, f c = ∑ (c : ContractionsNat m), ∑ (k : Option c.uncontracted),
    f (congr h.symm ((extractEquiv (finCongr h i)).symm ⟨c, k⟩))  := by
  subst h
  simp only [finCongr_refl, Equiv.refl_apply, congr_refl]
  rw [← (extractEquiv i).symm.sum_comp]
  rw [Finset.sum_sigma']
  rfl

end ContractionsNat

end FieldStruct
