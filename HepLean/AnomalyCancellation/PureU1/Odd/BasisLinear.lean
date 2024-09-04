/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.PureU1.Sorts
import HepLean.AnomalyCancellation.PureU1.BasisLinear
import HepLean.AnomalyCancellation.PureU1.VectorLike
import Mathlib.Logic.Equiv.Fin
/-!
# Basis of `LinSols` in the odd case

We give a basis of `LinSols` in the odd case. This basis has the special property
that splits into two planes on which every point is a solution to the ACCs.
-/
universe v u

open Nat
open Finset
open BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeOddPlane

lemma split_odd! (n : ℕ) : (1 + n) + n = 2 * n +1 := by
  omega

lemma split_adda (n : ℕ) : ((1+n)+1) + n.succ = 2 * n.succ + 1 := by
  omega

section theDeltas

/-- A helper function for what follows. -/
def δ₁ (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.castAdd 1 j))

/-- A helper function for what follows. -/
def δ₂ (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.natAdd (n+1) j)

/-- A helper function for what follows. -/
def δ₃ : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.natAdd n 1))

/-- A helper function for what follows. -/
def δ!₁ (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd! n) (Fin.castAdd n (Fin.natAdd 1 j))

/-- A helper function for what follows. -/
def δ!₂ (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd! n) (Fin.natAdd (1 + n) j)

/-- A helper function for what follows. -/
def δ!₃ : Fin (2 * n + 1) :=
  Fin.cast (split_odd! n) (Fin.castAdd n (Fin.castAdd n 1))

/-- A helper function for what follows. -/
def δa₁ : Fin (2 * n.succ + 1) :=
  Fin.cast (split_adda n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.castAdd n 1)))

/-- A helper function for what follows. -/
def δa₂ (j : Fin n) : Fin (2 * n.succ + 1) :=
  Fin.cast (split_adda n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.natAdd 1 j)))

/-- A helper function for what follows. -/
def δa₃ : Fin (2 * n.succ + 1) :=
  Fin.cast (split_adda n) (Fin.castAdd n.succ (Fin.natAdd (1+n) 1))

/-- A helper function for what follows. -/
def δa₄ (j : Fin n.succ) : Fin (2 * n.succ + 1) :=
  Fin.cast (split_adda n) (Fin.natAdd ((1+n)+1) j)

lemma δa₁_δ₁ : @δa₁ n = δ₁ 0 := by
  exact Fin.rev_inj.mp rfl

lemma δa₁_δ!₃ : @δa₁ n = δ!₃ := by
  rfl

lemma δa₂_δ₁ (j : Fin n) : δa₂ j = δ₁ j.succ := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, δa₂, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, δ₁, Fin.val_succ]
  exact Nat.add_comm 1 ↑j

lemma δa₂_δ!₁ (j : Fin n) : δa₂ j = δ!₁ j.castSucc := by
  rw [Fin.ext_iff]
  rfl

lemma δa₃_δ₃ : @δa₃ n = δ₃ := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, δa₃, Fin.isValue, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd,
    Fin.coe_fin_one, add_zero, δ₃]
  exact Nat.add_comm 1 n

lemma δa₃_δ!₁ : δa₃ = δ!₁ (Fin.last n) := by
  rfl

lemma δa₄_δ₂ (j : Fin n.succ) : δa₄ j = δ₂ j := by
  rw [Fin.ext_iff]
  simp only [succ_eq_add_one, δa₄, Fin.coe_cast, Fin.coe_natAdd, δ₂, add_left_inj]
  exact Nat.add_comm 1 n

lemma δa₄_δ!₂ (j : Fin n.succ) : δa₄ j = δ!₂ j := by
  rw [Fin.ext_iff]
  rfl

lemma δ₂_δ!₂ (j : Fin n) : δ₂ j = δ!₂ j := by
  rw [Fin.ext_iff]
  simp only [δ₂, Fin.coe_cast, Fin.coe_natAdd, δ!₂, add_left_inj]
  exact Nat.add_comm n 1

lemma sum_δ (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S δ₃ + ∑ i : Fin n, ((S ∘ δ₁) i + (S ∘ δ₂) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n + 1 + n), S (Fin.cast (split_odd n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (split_odd n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  nth_rewrite 2 [add_comm]
  rw [add_assoc]
  rw [Finset.sum_add_distrib]
  rfl

lemma sum_δ! (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S δ!₃ + ∑ i : Fin n, ((S ∘ δ!₁) i + (S ∘ δ!₂) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin ((1+n)+n), S (Fin.cast (split_odd! n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (split_odd! n)).symm.toEquiv]
    · intro i
      simp only [mem_univ, Fin.castOrderIso, RelIso.coe_fn_toEquiv]
    · exact fun _ _ => rfl
  rw [h1, Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  rw [add_assoc, Finset.sum_add_distrib]
  rfl

end theDeltas

section theBasisVectors

/-- The first part of the basis as charge assignments. -/
def basisAsCharges (j : Fin n) : (PureU1 (2 * n + 1)).Charges :=
  fun i =>
  if i = δ₁ j then
    1
  else
    if i = δ₂ j then
      - 1
    else
      0

/-- The second part of the basis as charge assignments. -/
def basis!AsCharges (j : Fin n) : (PureU1 (2 * n + 1)).Charges :=
  fun i =>
  if i = δ!₁ j then
    1
  else
    if i = δ!₂ j then
      - 1
    else
      0

lemma basis_on_δ₁_self (j : Fin n) : basisAsCharges j (δ₁ j) = 1 := by
  simp [basisAsCharges]

lemma basis!_on_δ!₁_self (j : Fin n) : basis!AsCharges j (δ!₁ j) = 1 := by
  simp [basis!AsCharges]

lemma basis_on_δ₁_other {k j : Fin n} (h : k ≠ j) :
    basisAsCharges k (δ₁ j) = 0 := by
  simp only [basisAsCharges, PureU1_numberCharges]
  simp only [δ₁, δ₂]
  split
  · rename_i h1
    rw [Fin.ext_iff] at h1
    simp_all
    rw [Fin.ext_iff] at h
    simp_all
  · split
    · rename_i h1 h2
      simp_all
      rw [Fin.ext_iff] at h2
      simp only [Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd] at h2
      omega
    · rfl

lemma basis!_on_δ!₁_other {k j : Fin n} (h : k ≠ j) :
    basis!AsCharges k (δ!₁ j) = 0 := by
  simp only [basis!AsCharges, PureU1_numberCharges]
  simp only [δ!₁, δ!₂]
  split
  · rename_i h1
    rw [Fin.ext_iff] at h1
    simp_all
    rw [Fin.ext_iff] at h
    simp_all
  · split
    · rename_i h1 h2
      simp_all
      rw [Fin.ext_iff] at h2
      simp only [Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd] at h2
      omega
    rfl

lemma basis_on_other {k : Fin n} {j : Fin (2 * n + 1)} (h1 : j ≠ δ₁ k) (h2 : j ≠ δ₂ k) :
    basisAsCharges k j = 0 := by
  simp only [basisAsCharges, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma basis!_on_other {k : Fin n} {j : Fin (2 * n + 1)} (h1 : j ≠ δ!₁ k) (h2 : j ≠ δ!₂ k) :
    basis!AsCharges k j = 0 := by
  simp only [basis!AsCharges, PureU1_numberCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma basis_δ₂_eq_minus_δ₁ (j i : Fin n) :
    basisAsCharges j (δ₂ i) = - basisAsCharges j (δ₁ i) := by
  simp only [basisAsCharges, PureU1_numberCharges, δ₂, δ₁]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

lemma basis!_δ!₂_eq_minus_δ!₁ (j i : Fin n) :
    basis!AsCharges j (δ!₂ i) = - basis!AsCharges j (δ!₁ i) := by
  simp only [basis!AsCharges, PureU1_numberCharges, δ!₂, δ!₁]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  · subst h1
    exact Fin.elim0 i
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

lemma basis_on_δ₂_self (j : Fin n) : basisAsCharges j (δ₂ j) = - 1 := by
  rw [basis_δ₂_eq_minus_δ₁, basis_on_δ₁_self]

lemma basis!_on_δ!₂_self (j : Fin n) : basis!AsCharges j (δ!₂ j) = - 1 := by
  rw [basis!_δ!₂_eq_minus_δ!₁, basis!_on_δ!₁_self]

lemma basis_on_δ₂_other {k j : Fin n} (h : k ≠ j) : basisAsCharges k (δ₂ j) = 0 := by
  rw [basis_δ₂_eq_minus_δ₁, basis_on_δ₁_other h]
  rfl

lemma basis!_on_δ!₂_other {k j : Fin n} (h : k ≠ j) : basis!AsCharges k (δ!₂ j) = 0 := by
  rw [basis!_δ!₂_eq_minus_δ!₁, basis!_on_δ!₁_other h]
  rfl

lemma basis_on_δ₃ (j : Fin n) : basisAsCharges j δ₃ = 0 := by
  simp only [basisAsCharges, PureU1_numberCharges]
  split <;> rename_i h
  · rw [Fin.ext_iff] at h
    simp only [δ₃, Fin.isValue, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, Fin.coe_fin_one,
      add_zero, δ₁] at h
    omega
  · split <;> rename_i h2
    · rw [Fin.ext_iff] at h2
      simp only [δ₃, Fin.isValue, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_natAdd, Fin.coe_fin_one,
        add_zero, δ₂] at h2
      omega
    · rfl

lemma basis!_on_δ!₃ (j : Fin n) : basis!AsCharges j δ!₃ = 0 := by
  simp only [basis!AsCharges, PureU1_numberCharges]
  split <;> rename_i h
  · rw [Fin.ext_iff] at h
    simp only [δ!₃, Fin.isValue, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_fin_one, δ!₁,
      Fin.coe_natAdd] at h
    omega
  · split <;> rename_i h2
    · rw [Fin.ext_iff] at h2
      simp only [δ!₃, Fin.isValue, Fin.coe_cast, Fin.coe_castAdd, Fin.coe_fin_one, δ!₂,
        Fin.coe_natAdd] at h2
      omega
    · rfl

lemma basis_linearACC (j : Fin n) : (accGrav (2 * n + 1)) (basisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  erw [sum_δ]
  simp [basis_δ₂_eq_minus_δ₁, basis_on_δ₃]

lemma basis!_linearACC (j : Fin n) : (accGrav (2 * n + 1)) (basis!AsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_δ!, basis!_on_δ!₃]
  simp [basis!_δ!₂_eq_minus_δ!₁]

/-- The first part of the basis as `LinSols`. -/
@[simps!]
def basis (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨basisAsCharges j, by
    intro i
    simp only [PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact basis_linearACC j⟩

/-- The second part of the basis as `LinSols`. -/
@[simps!]
def basis! (j : Fin n) : (PureU1 (2 * n + 1)).LinSols :=
  ⟨basis!AsCharges j, by
    intro i
    simp only [PureU1_numberLinear] at i
    match i with
    | 0 =>
    exact basis!_linearACC j⟩

/-- The whole basis as `LinSols`. -/
def basisa : Fin n ⊕ Fin n → (PureU1 (2 * n + 1)).LinSols := fun i =>
  match i with
  | .inl i => basis i
  | .inr i => basis! i

end theBasisVectors

/-- Swapping the elements δ!₁ j and δ!₂ j is equivalent to adding a vector basis!AsCharges j. -/
lemma swap!_as_add {S S' : (PureU1 (2 * n + 1)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n + 1)).linSolRep
    (pairSwap (δ!₁ j) (δ!₂ j))) S = S') :
    S'.val = S.val + (S.val (δ!₂ j) - S.val (δ!₁ j)) • basis!AsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = δ!₁ j
  · subst hi
    simp [HSMul.hSMul, basis!_on_δ!₁_self, pairSwap_inv_fst]
  · by_cases hi2 : i = δ!₂ j
    · subst hi2
      simp [HSMul.hSMul,basis!_on_δ!₂_self, pairSwap_inv_snd]
    · simp only [Equiv.invFun_as_coe, HSMul.hSMul, ACCSystemCharges.chargesAddCommMonoid_add,
      ACCSystemCharges.chargesModule_smul]
      rw [basis!_on_other hi hi2]
      change S.val ((pairSwap (δ!₁ j) (δ!₂ j)).invFun i) =_
      erw [pairSwap_inv_other (Ne.symm hi) (Ne.symm hi2)]
      simp

/-- A point in the span of the first part of the basis as a charge. -/
def P (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := ∑ i, f i • basisAsCharges i

/-- A point in the span of the second part of the basis as a charge. -/
def P! (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := ∑ i, f i • basis!AsCharges i

/-- A point in the span of the basis as a charge. -/
def Pa (f : Fin n → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n + 1)).Charges := P f + P! g

lemma P_δ₁ (f : Fin n → ℚ) (j : Fin n) : P f (δ₁ j) = f j := by
  rw [P, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis_on_δ₁_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [basis_on_δ₁_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P!_δ!₁ (f : Fin n → ℚ) (j : Fin n) : P! f (δ!₁ j) = f j := by
  rw [P!, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis!_on_δ!₁_self]
    exact Rat.mul_one (f j)
  · intro k _ hkj
    rw [basis!_on_δ!₁_other hkj]
    exact Rat.mul_zero (f k)
  · simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P_δ₂ (f : Fin n → ℚ) (j : Fin n) : P f (δ₂ j) = - f j := by
  rw [P, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis_on_δ₂_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [basis_on_δ₂_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma P!_δ!₂ (f : Fin n → ℚ) (j : Fin n) : P! f (δ!₂ j) = - f j := by
  rw [P!, sum_of_charges]
  simp only [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  · rw [basis!_on_δ!₂_self]
    exact mul_neg_one (f j)
  · intro k _ hkj
    rw [basis!_on_δ!₂_other hkj]
    exact Rat.mul_zero (f k)
  · simp

lemma P_δ₃ (f : Fin n → ℚ) : P f (δ₃) = 0 := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis_on_δ₃]

lemma P!_δ!₃ (f : Fin n → ℚ) : P! f (δ!₃) = 0 := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis!_on_δ!₃]

lemma Pa_δa₁ (f g : Fin n.succ → ℚ) : Pa f g δa₁ = f 0 := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [δa₁_δ₁]
  rw [δa₁_δ!₃]
  rw [P_δ₁, P!_δ!₃]
  exact Rat.add_zero (f 0)

lemma Pa_δa₂ (f g : Fin n.succ → ℚ) (j : Fin n) : Pa f g (δa₂ j) = f j.succ + g j.castSucc := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [δa₂_δ₁]
  rw [δa₂_δ!₁]
  rw [P_δ₁, P!_δ!₁]

lemma Pa_δa₃ (f g : Fin n.succ → ℚ) : Pa f g (δa₃) = g (Fin.last n) := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [δa₃_δ₃]
  rw [δa₃_δ!₁]
  rw [P_δ₃, P!_δ!₁]
  exact Rat.zero_add (g (Fin.last n))

lemma Pa_δa₄ (f g : Fin n.succ → ℚ) (j : Fin n.succ) : Pa f g (δa₄ j) = - f j - g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  nth_rewrite 1 [δa₄_δ₂]
  rw [δa₄_δ!₂]
  rw [P_δ₂, P!_δ!₂]
  ring

lemma P_linearACC (f : Fin n → ℚ) : (accGrav (2 * n + 1)) (P f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_δ]
  simp [P_δ₂, P_δ₁, P_δ₃]

lemma P!_linearACC (f : Fin n → ℚ) : (accGrav (2 * n + 1)) (P! f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_δ!]
  simp [P!_δ!₂, P!_δ!₁, P!_δ!₃]

lemma P_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (P f) = 0 := by
  rw [accCube_explicit, sum_δ, P_δ₃]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp [P_δ₁, P_δ₂]
  ring

lemma P!_accCube (f : Fin n → ℚ) : accCube (2 * n +1) (P! f) = 0 := by
  rw [accCube_explicit, sum_δ!, P!_δ!₃]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Function.comp_apply, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp only [P!_δ!₁, P!_δ!₂]
  ring

lemma P_P_P!_accCube (g : Fin n → ℚ) (j : Fin n) :
    accCubeTriLinSymm (P g) (P g) (basis!AsCharges j)
    = (P g (δ!₁ j))^2 - (g j)^2 := by
  simp only [accCubeTriLinSymm, PureU1Charges_numberCharges, TriLinearSymm.mk₃_toFun_apply_apply]
  rw [sum_δ!, basis!_on_δ!₃]
  simp only [mul_zero, Function.comp_apply, zero_add]
  rw [Finset.sum_eq_single j, basis!_on_δ!₁_self, basis!_on_δ!₂_self]
  · rw [← δ₂_δ!₂, P_δ₂]
    ring
  · intro k _ hkj
    erw [basis!_on_δ!₁_other hkj.symm, basis!_on_δ!₂_other hkj.symm]
    simp only [mul_zero, add_zero]
  · simp

lemma P_zero (f : Fin n → ℚ) (h : P f = 0) : ∀ i, f i = 0 := by
  intro i
  erw [← P_δ₁ f]
  rw [h]
  rfl

lemma P!_zero (f : Fin n → ℚ) (h : P! f = 0) : ∀ i, f i = 0 := by
  intro i
  rw [← P!_δ!₁ f]
  rw [h]
  rfl

lemma Pa_zero (f g : Fin n.succ → ℚ) (h : Pa f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := Pa_δa₁ f g
  rw [h] at h₃
  change 0 = _ at h₃
  simp only at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := lt_of_succ_lt hiv
    have hi2 := hi hivi
    have h1 := Pa_δa₄ f g ⟨iv, hivi⟩
    rw [h, hi2] at h1
    change 0 = _ at h1
    simp only [neg_zero, succ_eq_add_one, zero_sub, zero_eq_neg] at h1
    have h2 := Pa_δa₂ f g ⟨iv, succ_lt_succ_iff.mp hiv⟩
    simp [h, h1] at h2
    exact h2.symm
  exact hinduc i.val i.prop

lemma Pa_zero! (f g : Fin n.succ → ℚ) (h : Pa f g = 0) :
    ∀ i, g i = 0 := by
  have hf := Pa_zero f g h
  rw [Pa, P] at h
  simp only [succ_eq_add_one, hf, zero_smul, sum_const_zero, zero_add] at h
  exact P!_zero g h

/-- A point in the span of the first part of the basis. -/
def P' (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols := ∑ i, f i • basis i

/-- A point in the span of the second part of the basis. -/
def P!' (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).LinSols := ∑ i, f i • basis! i

/-- A point in the span of the whole basis. -/
def Pa' (f : (Fin n) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n + 1)).LinSols :=
    ∑ i, f i • basisa i

lemma Pa'_P'_P!' (f : (Fin n) ⊕ (Fin n) → ℚ) :
    Pa' f = P' (f ∘ Sum.inl) + P!' (f ∘ Sum.inr) := by
  exact Fintype.sum_sum_type _

lemma P'_val (f : Fin n → ℚ) : (P' f).val = P f := by
  simp only [P', P]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

lemma P!'_val (f : Fin n → ℚ) : (P!' f).val = P! f := by
  simp only [P!', P!]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  rfl

theorem basis_linear_independent : LinearIndependent ℚ (@basis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change P' f = 0 at h
  have h1 : (P' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [P'_val] at h1
  exact P_zero f h1

theorem basis!_linear_independent : LinearIndependent ℚ (@basis! n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change P!' f = 0 at h
  have h1 : (P!' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [P!'_val] at h1
  exact P!_zero f h1

theorem basisa_linear_independent : LinearIndependent ℚ (@basisa n.succ) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pa' f = 0 at h
  have h1 : (Pa' f).val = 0 :=
    (AddSemiconjBy.eq_zero_iff (ACCSystemLinear.LinSols.val 0)
    (congrFun (congrArg HAdd.hAdd (congrArg ACCSystemLinear.LinSols.val (id (Eq.symm h))))
    (ACCSystemLinear.LinSols.val 0))).mp rfl
  rw [Pa'_P'_P!'] at h1
  change (P' (f ∘ Sum.inl)).val + (P!' (f ∘ Sum.inr)).val = 0 at h1
  rw [P!'_val, P'_val] at h1
  change Pa (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := Pa_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := Pa_zero! (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all only [succ_eq_add_one, Function.comp_apply]
  cases i
  · simp_all
  · simp_all

lemma Pa'_eq (f f' : (Fin n.succ) ⊕ (Fin n.succ) → ℚ) : Pa' f = Pa' f' ↔ f = f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · funext i
    rw [Pa', Pa'] at h
    have h1 : ∑ i : Fin n.succ ⊕ Fin n.succ, (f i + (- f' i)) • basisa i = 0 := by
      simp only [add_smul, neg_smul]
      rw [Finset.sum_add_distrib]
      rw [h]
      rw [← Finset.sum_add_distrib]
      simp
    have h2 : ∀ i, (f i + (- f' i)) = 0 := by
      exact Fintype.linearIndependent_iff.mp (@basisa_linear_independent n)
        (fun i => f i + -f' i) h1
    have h2i := h2 i
    linarith
  · rw [h]

/-! TODO: Replace the definition of `join` with a Mathlib definition, most likely `Sum.elim`. -/
/-- A helper function for what follows. -/
def join (g f : Fin n → ℚ) : Fin n ⊕ Fin n → ℚ := fun i =>
  match i with
  | .inl i => g i
  | .inr i => f i

lemma join_ext (g g' : Fin n → ℚ) (f f' : Fin n → ℚ) :
    join g f = join g' f' ↔ g = g' ∧ f = f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · apply And.intro
    · funext i
      exact congr_fun h (Sum.inl i)
    · funext i
      exact congr_fun h (Sum.inr i)
  · rw [h.left, h.right]

lemma join_Pa (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    Pa' (join g f) = Pa' (join g' f') ↔ Pa g f = Pa g' f' := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [Pa'_eq, join_ext] at h
    rw [h.left, h.right]
  · apply ACCSystemLinear.LinSols.ext
    rw [Pa'_P'_P!', Pa'_P'_P!']
    simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val, P'_val, P!'_val]
    exact h

lemma Pa_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n.succ → ℚ) :
    Pa g f = Pa g' f' ↔ g = g' ∧ f = f' := by
  rw [← join_Pa]
  rw [← join_ext]
  exact Pa'_eq _ _

lemma basisa_card : Fintype.card ((Fin n.succ) ⊕ (Fin n.succ)) =
    FiniteDimensional.finrank ℚ (PureU1 (2 * n.succ + 1)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp only [Fintype.card_sum, Fintype.card_fin]
  exact Eq.symm (Nat.two_mul n.succ)

/-- The basis formed out of our basisa vectors. -/
noncomputable def basisaAsBasis :
    Basis (Fin n.succ ⊕ Fin n.succ) ℚ (PureU1 (2 * n.succ + 1)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basisa_linear_independent n) basisa_card

lemma span_basis (S : (PureU1 (2 * n.succ + 1)).LinSols) :
    ∃ (g f : Fin n.succ → ℚ), S.val = P g + P! f := by
  have h := (mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisaAsBasis S)
  obtain ⟨f, hf⟩ := h
  simp only [succ_eq_add_one, basisaAsBasis, coe_basisOfLinearIndependentOfCardEqFinrank,
    Fintype.sum_sum_type] at hf
  change P' _ + P!' _ = S at hf
  use f ∘ Sum.inl
  use f ∘ Sum.inr
  rw [← hf]
  simp only [succ_eq_add_one, ACCSystemLinear.linSolsAddCommMonoid_add_val, P'_val, P!'_val]
  rfl

lemma span_basis_swap! {S : (PureU1 (2 * n.succ + 1)).LinSols} (j : Fin n.succ)
    (hS : ((FamilyPermutations (2 * n.succ + 1)).linSolRep
    (pairSwap (δ!₁ j) (δ!₂ j))) S = S') (g f : Fin n.succ → ℚ) (hS1 : S.val = P g + P! f) :
    ∃ (g' f' : Fin n.succ → ℚ),
    S'.val = P g' + P! f' ∧ P! f' = P! f +
    (S.val (δ!₂ j) - S.val (δ!₁ j)) • basis!AsCharges j ∧ g' = g := by
  let X := P! f + (S.val (δ!₂ j) - S.val (δ!₁ j)) • basis!AsCharges j
  have hf : P! f ∈ Submodule.span ℚ (Set.range basis!AsCharges) := by
    rw [(mem_span_range_iff_exists_fun ℚ)]
    use f
    rfl
  have hP : (S.val (δ!₂ j) - S.val (δ!₁ j)) • basis!AsCharges j ∈
      Submodule.span ℚ (Set.range basis!AsCharges) := by
    apply Submodule.smul_mem
    apply SetLike.mem_of_subset
    apply Submodule.subset_span
    simp_all only [Set.mem_range, exists_apply_eq_apply]
  have hX : X ∈ Submodule.span ℚ (Set.range (basis!AsCharges)) := by
    apply Submodule.add_mem
    exact hf
    exact hP
  have hXsum := (mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change P! f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true]
  change S'.val = P g + (P! f + _)
  rw [← add_assoc, ← hS1]
  apply swap!_as_add at hS
  exact hS

end VectorLikeOddPlane

end PureU1
