/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.Insert
/-!

# Equivalence extracting element from contraction

-/

namespace FieldStruct
variable {𝓕 : FieldStruct}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open HepLean.Fin

lemma extractEquiv_equiv {c1 c2 : (c : WickContraction n) × Option c.uncontracted}
    (h : c1.1 = c2.1) (ho : c1.2 = uncontractedCongr (by rw [h]) c2.2) : c1 = c2 := by
  cases c1
  cases c2
  simp_all only [Sigma.mk.inj_iff]
  simp only at h
  subst h
  simp only [uncontractedCongr, Equiv.optionCongr_apply, heq_eq_eq, true_and]
  rename_i a
  match a with
  | none => simp
  | some a =>
    simp only [Option.map_some', Option.some.injEq]
    ext
    simp

def extractEquiv (i : Fin n.succ) : WickContraction n.succ ≃
    (c : WickContraction n) × Option c.uncontracted where
  toFun := fun c => ⟨erase c i, getDualErase c i⟩
  invFun := fun ⟨c, j⟩ => insert c i j
  left_inv f := by
    simp
  right_inv f := by
    refine extractEquiv_equiv ?_ ?_
    simp only [insert_erase]
    simp only [Nat.succ_eq_add_one]
    have h1 := insert_getDualErase f.fst i f.snd
    exact insert_getDualErase _ i _

lemma extractEquiv_symm_none_uncontracted (i : Fin n.succ) (c : WickContraction n) :
    ((extractEquiv i).symm ⟨c, none⟩).uncontracted =
    (Insert.insert i (c.uncontracted.map i.succAboveEmb)) := by
  exact insert_none_uncontracted c i

@[simp]
lemma extractEquiv_apply_congr_symm_apply {n m : ℕ} (k : ℕ)
    (hnk : k < n.succ) (hkm : k < m.succ) (hnm : n = m) (c : WickContraction n)
    (i : c.uncontracted) : congr (by rw [hnm]) ((extractEquiv ⟨k, hkm⟩
    (congr (by rw [hnm]) ((extractEquiv ⟨k, hnk⟩).symm ⟨c, i⟩)))).1 = c := by
  subst hnm
  simp

instance fintype_zero : Fintype (WickContraction 0) where
  elems := {nil}
  complete := by
    intro c
    simp only [Finset.mem_singleton]
    apply Subtype.eq
    simp only [nil]
    ext a
    apply Iff.intro
    · intro h
      have hc := c.2.1 a h
      rw [Finset.card_eq_two] at hc
      obtain ⟨x, y, hxy, ha⟩ := hc
      exact Fin.elim0 x
    · simp

lemma sum_WickContraction_nil (f : WickContraction 0 → M) [AddCommMonoid M] :
    ∑ c, f c = f nil := by
  rw [Finset.sum_eq_single_of_mem]
  simp only [Finset.mem_univ]
  intro b hb
  fin_cases b
  simp

instance fintype_succ : (n : ℕ) → Fintype (WickContraction n)
  | 0 => fintype_zero
  | Nat.succ n => by
    letI := fintype_succ n
    exact Fintype.ofEquiv _ (extractEquiv 0).symm

lemma sum_extractEquiv_congr [AddCommMonoid M] {n m : ℕ} (i : Fin n) (f : WickContraction n → M)
    (h : n = m.succ) :
    ∑ c, f c = ∑ (c : WickContraction m), ∑ (k : Option c.uncontracted),
    f (congr h.symm ((extractEquiv (finCongr h i)).symm ⟨c, k⟩)) := by
  subst h
  simp only [finCongr_refl, Equiv.refl_apply, congr_refl]
  rw [← (extractEquiv i).symm.sum_comp]
  rw [Finset.sum_sigma']
  rfl

end WickContraction

end FieldStruct
