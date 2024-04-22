/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.Basic
import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Fin
/-!
# Pure U(1) ACC system.

We define the anomaly cancellation conditions for a pure U(1) gague theory with `n` fermions.

-/
universe v u
open Nat


open  Finset

namespace PureU1
open BigOperators

/-- The vector space of charges. -/
@[simps!]
def PureU1Charges (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk n

open BigOperators in
/-- The gravitational anomaly. -/
def accGrav (n : ℕ) : ((PureU1Charges n).charges →ₗ[ℚ] ℚ) where
  toFun S := ∑ i : Fin n, S i
  map_add' S T := Finset.sum_add_distrib
  map_smul' a S := by
   simp [HSMul.hSMul, SMul.smul]
   rw [← Finset.mul_sum]


/-- The symmetric trilinear form used to define the cubic anomaly. -/
@[simps!]
def accCubeTriLinSymm {n : ℕ} : TriLinearSymm (PureU1Charges n).charges := TriLinearSymm.mk₃
  (fun  S =>  ∑ i, S.1 i * S.2.1 i * S.2.2 i)
  (by
    intro a S L T
    simp [HSMul.hSMul]
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    ring)
  (by
    intro S L T R
    simp only [PureU1Charges_numberCharges, ACCSystemCharges.chargesAddCommMonoid_add]
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    ring
    )
  (by
    intro S L T
    simp only [PureU1Charges_numberCharges]
    apply Fintype.sum_congr
    intro i
    ring
  )
  (by
    intro S L T
    simp only [PureU1Charges_numberCharges]
    apply Fintype.sum_congr
    intro i
    ring
  )



/-- The cubic anomaly equation. -/
@[simp]
def accCube (n : ℕ)  : HomogeneousCubic ((PureU1Charges n).charges) :=
  (accCubeTriLinSymm).toCubic


lemma accCube_explicit (n : ℕ) (S : (PureU1Charges n).charges) :
    accCube n S = ∑ i : Fin n, S i ^ 3:= by
  rw [accCube, TriLinearSymm.toCubic]
  change  accCubeTriLinSymm S S S = _
  rw [accCubeTriLinSymm]
  simp only [PureU1Charges_numberCharges, TriLinearSymm.mk₃_toFun_apply_apply]
  apply Finset.sum_congr
  simp only
  ring_nf
  simp

end PureU1

/-- The ACC system for a pure $U(1)$ gauge theory with $n$ fermions. -/
@[simps!]
def PureU1 (n : ℕ) : ACCSystem where
  numberLinear := 1
  linearACCs := fun i =>
    match i with
    | 0 => PureU1.accGrav n
  numberQuadratic := 0
  quadraticACCs := Fin.elim0
  cubicACC := PureU1.accCube n

/-- An equivalence of vector spaces of charges when the number of fermions is equal. -/
def pureU1EqCharges {n m : ℕ} (h : n = m):
    (PureU1 n).charges  ≃ₗ[ℚ] (PureU1 m).charges where
  toFun f := f ∘ Fin.cast h.symm
  invFun f := f ∘ Fin.cast h
  map_add' _ _ := rfl
  map_smul' _ _:= rfl
  left_inv _ := rfl
  right_inv _ := rfl

open BigOperators

lemma pureU1_linear {n : ℕ} (S : (PureU1 n.succ).LinSols) :
    ∑ i, S.val i = 0 := by
  have hS := S.linearSol
  simp at hS
  exact hS 0

lemma pureU1_cube {n : ℕ} (S : (PureU1 n.succ).Sols) :
    ∑ i, (S.val i) ^ 3 = 0 := by
  have hS := S.cubicSol
  erw [PureU1.accCube_explicit] at hS
  exact hS

lemma pureU1_last {n : ℕ} (S : (PureU1 n.succ).LinSols) :
    S.val (Fin.last n) = - ∑ i : Fin n, S.val i.castSucc := by
  have hS := pureU1_linear S
  simp at hS
  rw [Fin.sum_univ_castSucc] at hS
  linear_combination hS

lemma pureU1_anomalyFree_ext {n : ℕ} {S T : (PureU1 n.succ).LinSols}
    (h : ∀ (i : Fin n), S.val i.castSucc = T.val i.castSucc) : S = T := by
  apply ACCSystemLinear.LinSols.ext
  funext i
  by_cases hi : i ≠ Fin.last n
  have hiCast : ∃ j : Fin n, j.castSucc = i := by
    exact Fin.exists_castSucc_eq.mpr hi
  obtain ⟨j, hj⟩ := hiCast
  rw [← hj]
  exact h j
  simp at hi
  rw [hi]
  rw [pureU1_last, pureU1_last]
  simp only [neg_inj]
  apply Finset.sum_congr
  simp only
  intro j _
  exact h j

namespace PureU1

lemma sum_of_charges {n : ℕ} (f : Fin k → (PureU1 n).charges) (j : Fin n) :
    (∑ i : Fin k, (f i)) j = ∑ i : Fin k, (f i) j := by
  induction k
  simp
  rfl
  rename_i k hl
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlt := hl (f ∘ Fin.castSucc)
  erw [← hlt]
  simp


lemma sum_of_anomaly_free_linear {n : ℕ} (f : Fin k → (PureU1 n).LinSols) (j : Fin n) :
    (∑ i : Fin k, (f i)).1 j = (∑ i : Fin k, (f i).1 j) := by
  induction k
  simp
  rfl
  rename_i k hl
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlt := hl (f ∘ Fin.castSucc)
  erw [← hlt]
  simp


end PureU1
