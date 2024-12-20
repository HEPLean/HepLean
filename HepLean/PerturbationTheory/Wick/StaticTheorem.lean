/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Contractions
/-!

# Static Wick's theorem

-/

namespace Wick

noncomputable section

open HepLean.List
open FieldStatistic

variable {𝓕 : Type} {f : 𝓕 → Type} [∀ i, Fintype (f i)] (q : 𝓕 → FieldStatistic)
  (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le]

lemma static_wick_nil {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A)
    (S : Contractions.Splitting f le) :
    F (ofListLift f [] 1) = ∑ c : Contractions [],
    c.toCenterTerm f q le F S *
    F (koszulOrder (fun i => q i.fst) le (ofListLift f c.normalize 1)) := by
  rw [← Contractions.nilEquiv.symm.sum_comp]
  simp only [Finset.univ_unique, PUnit.default_eq_unit, Contractions.nilEquiv, Equiv.coe_fn_symm_mk,
    Finset.sum_const, Finset.card_singleton, one_smul]
  dsimp [Contractions.normalize, Contractions.toCenterTerm]
  simp [ofListLift_empty]

lemma static_wick_cons [IsTrans ((i : 𝓕) × f i) le] [IsTotal ((i : 𝓕) × f i) le]
    {A : Type} [Semiring A] [Algebra ℂ A] (r : List 𝓕) (a : 𝓕)
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le F]
    (S : Contractions.Splitting f le)
    (ih : F (ofListLift f r 1) =
    ∑ c : Contractions r, c.toCenterTerm f q le F S * F (koszulOrder (fun i => q i.fst) le
      (ofListLift f c.normalize 1))) :
    F (ofListLift f (a :: r) 1) = ∑ c : Contractions (a :: r),
      c.toCenterTerm f q le F S *
      F (koszulOrder (fun i => q i.fst) le (ofListLift f c.normalize 1)) := by
  rw [ofListLift_cons_eq_ofListLift, map_mul, ih, Finset.mul_sum,
    ← Contractions.consEquiv.symm.sum_comp]
  erw [Finset.sum_sigma]
  congr
  funext c
  have hb := S.h𝓑 a
  rw [← mul_assoc]
  have hi := c.toCenterTerm_center f q le F S
  rw [Subalgebra.mem_center_iff] at hi
  rw [hi, mul_assoc, ← map_mul, hb, add_mul, map_add]
  conv_lhs =>
    enter [2, 1]
    rw [ofList_eq_smul_one, Algebra.smul_mul_assoc, ofList_singleton]
  rw [mul_koszulOrder_le]
  conv_lhs =>
    enter [2, 1]
    rw [← map_smul, ← Algebra.smul_mul_assoc]
    rw [← ofList_singleton, ← ofList_eq_smul_one]
  conv_lhs =>
    enter [2, 2]
    rw [ofList_eq_smul_one, Algebra.smul_mul_assoc, map_smul]
  rw [le_all_mul_koszulOrder_ofListLift_expand]
  conv_lhs =>
    enter [2, 2]
    rw [smul_add, Finset.smul_sum]
    rw [← map_smul, ← map_smul, ← Algebra.smul_mul_assoc, ← ofList_eq_smul_one]
    enter [2, 2]
    intro n
    rw [← Algebra.smul_mul_assoc, smul_comm, ← map_smul, ← LinearMap.map_smul₂,
      ← ofList_eq_smul_one]
  rw [← add_assoc, ← map_add, ← map_add, ← add_mul, ← hb, ← ofListLift_cons_eq_ofListLift, mul_add]
  rw [Fintype.sum_option]
  congr 1
  rw [Finset.mul_sum]
  congr
  funext n
  rw [← mul_assoc]
  rfl
  exact S.h𝓑p a
  exact S.h𝓑n a

theorem static_wick_theorem [IsTrans ((i : 𝓕) × f i) le] [IsTotal ((i : 𝓕) × f i) le]
    {A : Type} [Semiring A] [Algebra ℂ A] (r : List 𝓕)
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le F]
    (S : Contractions.Splitting f le) :
    F (ofListLift f r 1) = ∑ c : Contractions r, c.toCenterTerm f q le F S *
    F (koszulOrder (fun i => q i.fst) le (ofListLift f c.normalize 1)) := by
  induction r with
  | nil => exact static_wick_nil q le F S
  | cons a r ih => exact static_wick_cons q le r a F S ih

end
end Wick
