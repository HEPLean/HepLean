/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.PureU1.Sort
import HepLean.AnomalyCancellation.PureU1.BasisLinear
import HepLean.AnomalyCancellation.PureU1.VectorLike
import Mathlib.Logic.Equiv.Fin
/-!
# Basis of `LinSols` in the even case

We give a basis of `LinSols` in the even case. This basis has the special property
that splits into two planes on which every point is a solution to the ACCs.
-/
universe v u

open Nat
open Finset
open BigOperators

namespace PureU1

variable {n : ℕ}

namespace VectorLikeEvenPlane

lemma n_cond₂ (n : ℕ) : 1 + ((n + n) + 1) = 2 * n.succ := by
  linarith

section theδs

/-- A helper function for what follows. -/
def δ₁ (j : Fin n.succ) : Fin (2 * n.succ) := Fin.cast (split_equal n.succ) (Fin.castAdd n.succ j)

/-- A helper function for what follows. -/
def δ₂ (j : Fin n.succ) : Fin (2 * n.succ) := Fin.cast (split_equal n.succ) (Fin.natAdd n.succ j)

/-- A helper function for what follows. -/
def δ!₁ (j : Fin n) : Fin (2 * n.succ) := Fin.cast (n_cond₂ n)
  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)))

/-- A helper function for what follows. -/
def δ!₂ (j : Fin n) : Fin (2 * n.succ) := Fin.cast (n_cond₂ n)
  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n j)))

/-- A helper function for what follows. -/
def δ!₃ : Fin (2 * n.succ) := (Fin.cast (n_cond₂ n) (Fin.castAdd ((n + n) + 1) 0))

/-- A helper function for what follows. -/
def δ!₄ : Fin (2 * n.succ) := (Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.natAdd (n + n) 0)))

lemma ext_δ (S T : Fin (2 * n.succ) → ℚ) (h1 : ∀ i, S (δ₁ i) = T (δ₁ i))
    (h2 : ∀ i, S (δ₂ i) = T (δ₂ i)) : S = T := by
  funext i
  by_cases hi : i.val < n.succ
  let j : Fin n.succ := ⟨i, hi⟩
  have h2 := h1 j
  have h3 : δ₁ j = i := by
    simp [δ₁, Fin.ext_iff]
  rw [h3] at h2
  exact h2
  let j : Fin n.succ := ⟨i - n.succ, by omega⟩
  have h2 := h2 j
  have h3 : δ₂ j = i := by
    simp [δ₂, Fin.ext_iff]
    omega
  rw [h3] at h2
  exact h2

lemma sum_δ₁_δ₂ (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = ∑ i : Fin n.succ, ((S ∘ δ₁) i + (S ∘ δ₂) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n.succ + n.succ), S (Fin.cast (split_equal n.succ) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (split_equal n.succ)).symm.toEquiv]
    intro i
    simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    intro i
    simp
  rw [h1]
  rw [Fin.sum_univ_add, Finset.sum_add_distrib]
  rfl

lemma sum_δ₁_δ₂' (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = ∑ i : Fin n.succ, ((S ∘ δ₁) i + (S ∘ δ₂) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n.succ + n.succ), S (Fin.cast (split_equal n.succ) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (split_equal n.succ)).symm.toEquiv]
    intro i
    simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    intro i
    simp
  rw [h1]
  rw [Fin.sum_univ_add, Finset.sum_add_distrib]
  rfl

lemma sum_δ!₁_δ!₂ (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = S δ!₃ + S δ!₄ + ∑ i : Fin n, ((S ∘ δ!₁) i + (S ∘ δ!₂) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (1 + ((n + n) + 1)), S (Fin.cast (n_cond₂ n) i) := by
    rw [Finset.sum_equiv (Fin.castOrderIso (n_cond₂ n)).symm.toEquiv]
    intro i
    simp only [mem_univ, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv]
    intro i
    simp
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Finset.sum_add_distrib]
  simp only [univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton, Function.comp_apply]
  repeat rw [Rat.add_assoc]
  apply congrArg
  rw [Rat.add_comm]
  rw [← Rat.add_assoc]
  nth_rewrite 2 [Rat.add_comm]
  repeat rw [Rat.add_assoc]
  nth_rewrite 2 [Rat.add_comm]
  rfl

lemma δ!₃_δ₁0 : @δ!₃ n = δ₁ 0 := by
  rfl

lemma δ!₄_δ₂Last: @δ!₄ n = δ₂ (Fin.last n) := by
  rw [Fin.ext_iff]
  simp [δ!₄, δ₂]
  omega

lemma δ!₁_δ₁ (j : Fin n) : δ!₁ j = δ₁ j.succ := by
  rw [Fin.ext_iff, δ₁, δ!₁]
  simp only [Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, Fin.val_succ]
  ring

lemma δ!₂_δ₂ (j : Fin n) : δ!₂ j = δ₂ j.castSucc := by
  rw [Fin.ext_iff, δ₂, δ!₂]
  simp only [Fin.coe_cast, Fin.coe_natAdd, Fin.coe_castAdd, Fin.coe_castSucc]
  ring_nf
  rw [Nat.succ_eq_add_one]
  ring

end theδs

/-- The first part of the basis as charges. -/
def basisAsCharges (j : Fin n.succ) : (PureU1 (2 * n.succ)).Charges :=
  fun i =>
  if i = δ₁ j then
    1
  else
    if i = δ₂ j then
      - 1
    else
      0

/-- The second part of the basis as charges. -/
def basis!AsCharges (j : Fin n) : (PureU1 (2 * n.succ)).Charges :=
  fun i =>
  if i = δ!₁ j then
    1
  else
    if i = δ!₂ j then
      - 1
    else
      0

lemma basis_on_δ₁_self (j : Fin n.succ) : basisAsCharges j (δ₁ j) = 1 := by
  simp [basisAsCharges]

lemma basis!_on_δ!₁_self (j : Fin n) : basis!AsCharges j (δ!₁ j) = 1 := by
  simp [basis!AsCharges]

lemma basis_on_δ₁_other {k j : Fin n.succ} (h : k ≠ j) :
    basisAsCharges k (δ₁ j) = 0 := by
  simp [basisAsCharges]
  simp [δ₁, δ₂]
  split
  rename_i h1
  rw [Fin.ext_iff] at h1
  simp_all
  rw [Fin.ext_iff] at h
  simp_all
  split
  rename_i h1 h2
  simp_all
  rw [Fin.ext_iff] at h2
  simp at h2
  omega
  rfl

lemma basis_on_other {k : Fin n.succ} {j : Fin (2 * n.succ)} (h1 : j ≠ δ₁ k) (h2 : j ≠ δ₂ k) :
    basisAsCharges k j = 0 := by
  simp [basisAsCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma basis!_on_other {k : Fin n} {j : Fin (2 * n.succ)} (h1 : j ≠ δ!₁ k) (h2 : j ≠ δ!₂ k) :
    basis!AsCharges k j = 0 := by
  simp [basis!AsCharges]
  simp_all only [ne_eq, ↓reduceIte]

lemma basis!_on_δ!₁_other {k j : Fin n} (h : k ≠ j) :
    basis!AsCharges k (δ!₁ j) = 0 := by
  simp [basis!AsCharges]
  simp [δ!₁, δ!₂]
  split
  rename_i h1
  rw [Fin.ext_iff] at h1
  simp_all
  rw [Fin.ext_iff] at h
  simp_all
  split
  rename_i h1 h2
  simp_all
  rw [Fin.ext_iff] at h2
  simp at h2
  omega
  rfl

lemma basis_δ₂_eq_minus_δ₁ (j i : Fin n.succ) :
    basisAsCharges j (δ₂ i) = - basisAsCharges j (δ₁ i) := by
  simp [basisAsCharges, δ₂, δ₁]
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
  simp [basis!AsCharges, δ!₂, δ!₁]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  subst h1
  exact Fin.elim0 i
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

lemma basis_on_δ₂_self (j : Fin n.succ) : basisAsCharges j (δ₂ j) = - 1 := by
  rw [basis_δ₂_eq_minus_δ₁, basis_on_δ₁_self]

lemma basis!_on_δ!₂_self (j : Fin n) : basis!AsCharges j (δ!₂ j) = - 1 := by
  rw [basis!_δ!₂_eq_minus_δ!₁, basis!_on_δ!₁_self]

lemma basis_on_δ₂_other {k j : Fin n.succ} (h : k ≠ j) : basisAsCharges k (δ₂ j) = 0 := by
  rw [basis_δ₂_eq_minus_δ₁, basis_on_δ₁_other h]
  rfl

lemma basis!_on_δ!₂_other {k j : Fin n} (h : k ≠ j) : basis!AsCharges k (δ!₂ j) = 0 := by
  rw [basis!_δ!₂_eq_minus_δ!₁, basis!_on_δ!₁_other h]
  rfl

lemma basis!_on_δ!₃ (j : Fin n) : basis!AsCharges j δ!₃ = 0 := by
  simp [basis!AsCharges]
  split <;> rename_i h
  rw [Fin.ext_iff] at h
  simp [δ!₃, δ!₁] at h
  omega
  split <;> rename_i h2
  rw [Fin.ext_iff] at h2
  simp [δ!₃, δ!₂] at h2
  omega
  rfl

lemma basis!_on_δ!₄ (j : Fin n) : basis!AsCharges j δ!₄ = 0 := by
  simp [basis!AsCharges]
  split <;> rename_i h
  rw [Fin.ext_iff] at h
  simp [δ!₄, δ!₁] at h
  omega
  split <;> rename_i h2
  rw [Fin.ext_iff] at h2
  simp [δ!₄, δ!₂] at h2
  omega
  rfl

lemma basis_linearACC (j : Fin n.succ) : (accGrav (2 * n.succ)) (basisAsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_δ₁_δ₂]
  simp [basis_δ₂_eq_minus_δ₁]

lemma basis!_linearACC (j : Fin n) : (accGrav (2 * n.succ)) (basis!AsCharges j) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_δ!₁_δ!₂, basis!_on_δ!₃, basis!_on_δ!₄]
  simp [basis!_δ!₂_eq_minus_δ!₁]

lemma basis_accCube (j : Fin n.succ) :
    accCube (2 * n.succ) (basisAsCharges j) = 0 := by
  rw [accCube_explicit, sum_δ₁_δ₂]
  apply Finset.sum_eq_zero
  intro i _
  simp [basis_δ₂_eq_minus_δ₁]
  ring

lemma basis!_accCube (j : Fin n) :
    accCube (2 * n.succ) (basis!AsCharges j) = 0 := by
  rw [accCube_explicit, sum_δ!₁_δ!₂]
  rw [basis!_on_δ!₄, basis!_on_δ!₃]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Function.comp_apply,
    zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp [basis!_δ!₂_eq_minus_δ!₁]
  ring

/-- The first part of the basis as `LinSols`. -/
@[simps!]
def basis (j : Fin n.succ) : (PureU1 (2 * n.succ)).LinSols :=
  ⟨basisAsCharges j, by
    intro i
    simp at i
    match i with
    | 0 =>
    exact basis_linearACC j⟩

/-- The second part of the basis as `LinSols`. -/
@[simps!]
def basis! (j : Fin n) : (PureU1 (2 * n.succ)).LinSols :=
  ⟨basis!AsCharges j, by
    intro i
    simp at i
    match i with
    | 0 =>
    exact basis!_linearACC j⟩

/-- The whole basis as `LinSols`. -/
def basisa : (Fin n.succ) ⊕ (Fin n) → (PureU1 (2 * n.succ)).LinSols := fun i =>
  match i with
  | .inl i => basis i
  | .inr i => basis! i

/-- Swapping the elements δ!₁ j and δ!₂ j is equivalent to adding a vector basis!AsCharges j. -/
lemma swap!_as_add {S S' : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (pairSwap (δ!₁ j) (δ!₂ j))) S = S') :
    S'.val = S.val + (S.val (δ!₂ j) - S.val (δ!₁ j)) • basis!AsCharges j := by
  funext i
  rw [← hS, FamilyPermutations_anomalyFreeLinear_apply]
  by_cases hi : i = δ!₁ j
  subst hi
  simp [HSMul.hSMul, basis!_on_δ!₁_self, pairSwap_inv_fst]
  by_cases hi2 : i = δ!₂ j
  subst hi2
  simp [HSMul.hSMul, basis!_on_δ!₂_self, pairSwap_inv_snd]
  simp [HSMul.hSMul]
  rw [basis!_on_other hi hi2]
  change S.val ((pairSwap (δ!₁ j) (δ!₂ j)).invFun i) =_
  erw [pairSwap_inv_other (Ne.symm hi) (Ne.symm hi2)]
  simp

/-- A point in the span of the first part of the basis as a charge. -/
def P (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).Charges := ∑ i, f i • basisAsCharges i

/-- A point in the span of the second part of the basis as a charge. -/
def P! (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges := ∑ i, f i • basis!AsCharges i

/-- A point in the span of the basis as a charge. -/
def Pa (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n.succ)).Charges := P f + P! g

lemma P_δ₁ (f : Fin n.succ → ℚ) (j : Fin n.succ) : P f (δ₁ j) = f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis_on_δ₁_self]
  simp only [mul_one]
  intro k _ hkj
  rw [basis_on_δ₁_other hkj]
  simp only [mul_zero]
  simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P!_δ!₁ (f : Fin n → ℚ) (j : Fin n) : P! f (δ!₁ j) = f j := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis!_on_δ!₁_self]
  simp only [mul_one]
  intro k _ hkj
  rw [basis!_on_δ!₁_other hkj]
  simp only [mul_zero]
  simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma Pa_δ!₁ (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (δ!₁ j) = f j.succ + g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [P!_δ!₁, δ!₁_δ₁, P_δ₁]

lemma P_δ₂ (f : Fin n.succ → ℚ) (j : Fin n.succ) : P f (δ₂ j) = - f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis_on_δ₂_self]
  simp only [mul_neg, mul_one]
  intro k _ hkj
  rw [basis_on_δ₂_other hkj]
  simp only [mul_zero]
  simp

lemma P!_δ!₂ (f : Fin n → ℚ) (j : Fin n) : P! f (δ!₂ j) = - f j := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis!_on_δ!₂_self]
  simp only [mul_neg, mul_one]
  intro k _ hkj
  rw [basis!_on_δ!₂_other hkj]
  simp only [mul_zero]
  simp

lemma Pa_δ!₂ (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (δ!₂ j) = - f j.castSucc - g j := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [P!_δ!₂, δ!₂_δ₂, P_δ₂]
  ring

lemma P!_δ!₃ (f : Fin n → ℚ) : P! f (δ!₃) = 0 := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis!_on_δ!₃]

lemma Pa_δ!₃ (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : Pa f g (δ!₃) = f 0 := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [P!_δ!₃, δ!₃_δ₁0, P_δ₁]
  simp

lemma P!_δ!₄ (f : Fin n → ℚ) : P! f (δ!₄) = 0 := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis!_on_δ!₄]

lemma Pa_δ!₄ (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : Pa f g (δ!₄) = - f (Fin.last n) := by
  rw [Pa]
  simp only [ACCSystemCharges.chargesAddCommMonoid_add]
  rw [P!_δ!₄, δ!₄_δ₂Last, P_δ₂]
  simp

lemma P_δ₁_δ₂ (f : Fin n.succ → ℚ) : P f ∘ δ₂ = - P f ∘ δ₁ := by
  funext j
  simp only [PureU1_numberCharges, Function.comp_apply, Pi.neg_apply]
  rw [P_δ₁, P_δ₂]

lemma P_linearACC (f : Fin n.succ → ℚ) : (accGrav (2 * n.succ)) (P f) = 0 := by
  rw [accGrav]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_δ₁_δ₂]
  simp [P_δ₂, P_δ₁]

lemma P_accCube (f : Fin n.succ → ℚ) : accCube (2 * n.succ) (P f) = 0 := by
  rw [accCube_explicit, sum_δ₁_δ₂]
  apply Finset.sum_eq_zero
  intro i _
  simp [P_δ₁, P_δ₂]
  ring

lemma P!_accCube (f : Fin n → ℚ) : accCube (2 * n.succ) (P! f) = 0 := by
  rw [accCube_explicit, sum_δ!₁_δ!₂, P!_δ!₃, P!_δ!₄]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Function.comp_apply,
    zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp [P!_δ!₁, P!_δ!₂]
  ring

lemma P_P_P!_accCube (g : Fin n.succ → ℚ) (j : Fin n) :
    accCubeTriLinSymm (P g) (P g) (basis!AsCharges j)
    = g (j.succ) ^ 2 - g (j.castSucc) ^ 2 := by
  simp [accCubeTriLinSymm]
  rw [sum_δ!₁_δ!₂, basis!_on_δ!₃, basis!_on_δ!₄]
  simp only [mul_zero, add_zero, Function.comp_apply, zero_add]
  rw [Finset.sum_eq_single j, basis!_on_δ!₁_self, basis!_on_δ!₂_self]
  simp [δ!₁_δ₁, δ!₂_δ₂]
  rw [P_δ₁, P_δ₂]
  ring
  intro k _ hkj
  erw [basis!_on_δ!₁_other hkj.symm, basis!_on_δ!₂_other hkj.symm]
  simp only [mul_zero, add_zero]
  simp

lemma P_P!_P!_accCube (g : Fin n → ℚ) (j : Fin n.succ) :
    accCubeTriLinSymm (P! g) (P! g) (basisAsCharges j)
    = (P! g (δ₁ j))^2 - (P! g (δ₂ j))^2 := by
  simp [accCubeTriLinSymm]
  rw [sum_δ₁_δ₂]
  simp only [Function.comp_apply]
  rw [Finset.sum_eq_single j, basis_on_δ₁_self, basis_on_δ₂_self]
  simp [δ!₁_δ₁, δ!₂_δ₂]
  ring
  intro k _ hkj
  erw [basis_on_δ₁_other hkj.symm, basis_on_δ₂_other hkj.symm]
  simp only [mul_zero, add_zero]
  simp

lemma P_zero (f : Fin n.succ → ℚ) (h : P f = 0) : ∀ i, f i = 0 := by
  intro i
  erw [← P_δ₁ f]
  rw [h]
  rfl

lemma P!_zero (f : Fin n → ℚ) (h : P! f = 0) : ∀ i, f i = 0 := by
  intro i
  rw [← P!_δ!₁ f]
  rw [h]
  rfl

lemma Pa_zero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := Pa_δ!₃ f g
  rw [h] at h₃
  change 0 = f 0 at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := by omega
    have hi2 := hi hivi
    have h1 := Pa_δ!₁ f g ⟨iv, by omega⟩
    have h2 := Pa_δ!₂ f g ⟨iv, by omega⟩
    rw [h] at h1 h2
    simp at h1 h2
    erw [hi2] at h2
    change 0 = _ at h2
    simp at h2
    rw [h2] at h1
    simp at h1
    exact h1.symm
  exact hinduc i.val i.prop

lemma Pa_zero! (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, g i = 0 := by
  have hf := Pa_zero f g h
  rw [Pa, P] at h
  simp [hf] at h
  exact P!_zero g h

/-- A point in the span of the first part of the basis. -/
def P' (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).LinSols := ∑ i, f i • basis i

/-- A point in the span of the second part of the basis. -/
def P!' (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).LinSols := ∑ i, f i • basis! i

/-- A point in the span of the whole basis. -/
def Pa' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n.succ)).LinSols :=
    ∑ i, f i • basisa i

lemma Pa'_P'_P!' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) :
    Pa' f = P' (f ∘ Sum.inl) + P!' (f ∘ Sum.inr):= by
  exact Fintype.sum_sum_type _

lemma P'_val (f : Fin n.succ → ℚ) : (P' f).val = P f := by
  simp [P', P]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  simp [HSMul.hSMul]

lemma P!'_val (f : Fin n → ℚ) : (P!' f).val = P! f := by
  simp [P!', P!]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  simp [HSMul.hSMul]

theorem basis_linear_independent : LinearIndependent ℚ (@basis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change P' f = 0 at h
  have h1 : (P' f).val = 0 := by
    simp [h]
    rfl
  rw [P'_val] at h1
  exact P_zero f h1

theorem basis!_linear_independent : LinearIndependent ℚ (@basis! n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change P!' f = 0 at h
  have h1 : (P!' f).val = 0 := by
    simp [h]
    rfl
  rw [P!'_val] at h1
  exact P!_zero f h1

theorem basisa_linear_independent : LinearIndependent ℚ (@basisa n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pa' f = 0 at h
  have h1 : (Pa' f).val = 0 := by
    simp [h]
    rfl
  rw [Pa'_P'_P!'] at h1
  change (P' (f ∘ Sum.inl)).val + (P!' (f ∘ Sum.inr)).val = 0 at h1
  rw [P!'_val, P'_val] at h1
  change Pa (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := Pa_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := Pa_zero! (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all
  cases i
  simp_all
  simp_all

lemma Pa'_eq (f f' : (Fin n.succ) ⊕ (Fin n) → ℚ) : Pa' f = Pa' f' ↔ f = f' := by
  apply Iff.intro
  intro h
  funext i
  rw [Pa', Pa'] at h
  have h1 : ∑ i : Fin (succ n) ⊕ Fin n, (f i + (- f' i)) • basisa i = 0 := by
    simp only [add_smul, neg_smul]
    rw [Finset.sum_add_distrib]
    rw [h]
    rw [← Finset.sum_add_distrib]
    simp
  have h2 : ∀ i, (f i + (- f' i)) = 0 := by
    exact Fintype.linearIndependent_iff.mp (@basisa_linear_independent (n))
     (fun i => f i + -f' i) h1
  have h2i := h2 i
  linarith
  intro h
  rw [h]

/-! TODO: Replace the definition of `join` with a Mathlib definition, most likely `Sum.elim`. -/
/-- A helper function for what follows. -/
def join (g : Fin n.succ → ℚ) (f : Fin n → ℚ) : (Fin n.succ) ⊕ (Fin n) → ℚ := fun i =>
  match i with
  | .inl i => g i
  | .inr i => f i

lemma join_ext (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    join g f = join g' f' ↔ g = g' ∧ f = f' := by
  apply Iff.intro
  intro h
  apply And.intro
  funext i
  exact congr_fun h (Sum.inl i)
  funext i
  exact congr_fun h (Sum.inr i)
  intro h
  rw [h.left, h.right]

lemma join_Pa (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    Pa' (join g f) = Pa' (join g' f') ↔ Pa g f = Pa g' f' := by
  apply Iff.intro
  intro h
  rw [Pa'_eq] at h
  rw [join_ext] at h
  rw [h.left, h.right]
  intro h
  apply ACCSystemLinear.LinSols.ext
  rw [Pa'_P'_P!', Pa'_P'_P!']
  simp [P'_val, P!'_val]
  exact h

lemma Pa_eq (g g' : Fin n.succ → ℚ) (f f' : Fin n → ℚ) :
    Pa g f = Pa g' f' ↔ g = g' ∧ f = f' := by
  rw [← join_Pa]
  rw [← join_ext]
  exact Pa'_eq _ _

lemma basisa_card : Fintype.card ((Fin n.succ) ⊕ (Fin n)) =
    FiniteDimensional.finrank ℚ (PureU1 (2 * n.succ)).LinSols := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp only [Fintype.card_sum, Fintype.card_fin, mul_eq]
  omega

/-- The basis formed out of our basisa vectors. -/
noncomputable def basisaAsBasis :
    Basis (Fin (succ n) ⊕ Fin n) ℚ (PureU1 (2 * succ n)).LinSols :=
  basisOfLinearIndependentOfCardEqFinrank (@basisa_linear_independent n) basisa_card

lemma span_basis (S : (PureU1 (2 * n.succ)).LinSols) :
    ∃ (g : Fin n.succ → ℚ) (f : Fin n → ℚ), S.val = P g + P! f := by
  have h := (mem_span_range_iff_exists_fun ℚ).mp (Basis.mem_span basisaAsBasis S)
  obtain ⟨f, hf⟩ := h
  simp [basisaAsBasis] at hf
  change P' _ + P!' _ = S at hf
  use f ∘ Sum.inl
  use f ∘ Sum.inr
  rw [← hf]
  simp [P'_val, P!'_val]
  rfl

lemma P!_in_span (f : Fin n → ℚ) : P! f ∈ Submodule.span ℚ (Set.range basis!AsCharges) := by
     rw [(mem_span_range_iff_exists_fun ℚ)]
     use f
     rfl

lemma smul_basis!AsCharges_in_span (S : (PureU1 (2 * n.succ )).LinSols) (j : Fin n) :
    (S.val (δ!₂ j) - S.val (δ!₁ j)) • basis!AsCharges j ∈
    Submodule.span ℚ (Set.range basis!AsCharges) := by
  apply Submodule.smul_mem
  apply SetLike.mem_of_subset
  apply Submodule.subset_span
  simp_all only [Set.mem_range, exists_apply_eq_apply]

lemma span_basis_swap! {S : (PureU1 (2 * n.succ)).LinSols} (j : Fin n)
    (hS : ((FamilyPermutations (2 * n.succ)).linSolRep
    (pairSwap (δ!₁ j) (δ!₂ j))) S = S') (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
     (h : S.val = P g + P! f):
    ∃
    (g' : Fin n.succ → ℚ) (f' : Fin n → ℚ) ,
     S'.val = P g' + P! f' ∧ P! f' = P! f +
    (S.val (δ!₂ j) - S.val (δ!₁ j)) • basis!AsCharges j ∧ g' = g := by
  let X := P! f + (S.val (δ!₂ j) - S.val (δ!₁ j)) • basis!AsCharges j
  have hX : X ∈ Submodule.span ℚ (Set.range (basis!AsCharges)) := by
    apply Submodule.add_mem
    exact (P!_in_span f)
    exact (smul_basis!AsCharges_in_span S j)
  have hXsum := (mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  use g
  use f'
  change P! f' = _ at hf'
  erw [hf']
  simp only [and_self, and_true]
  change S'.val = P g + (P! f + _)
  rw [← add_assoc, ← h]
  apply swap!_as_add at hS
  exact hS

lemma vectorLikeEven_in_span (S : (PureU1 (2 * n.succ)).LinSols)
    (hS : VectorLikeEven S.val) :
   ∃ (M : (FamilyPermutations (2 * n.succ)).group),
    (FamilyPermutations (2 * n.succ)).linSolRep M S
    ∈ Submodule.span ℚ (Set.range basis) := by
  use (Tuple.sort S.val).symm
  change sortAFL S ∈ Submodule.span ℚ (Set.range basis)
  rw [mem_span_range_iff_exists_fun ℚ]
  let f : Fin n.succ → ℚ := fun i => (sortAFL S).val (δ₁ i)
  use f
  apply ACCSystemLinear.LinSols.ext
  rw [sortAFL_val]
  erw [P'_val]
  apply ext_δ
  intro i
  rw [P_δ₁]
  rfl
  intro i
  rw [P_δ₂]
  have ht := hS i
  change sort S.val (δ₁ i) = - sort S.val (δ₂ i) at ht
  have h : sort S.val (δ₂ i) = - sort S.val (δ₁ i) := by
    rw [ht]
    ring
  rw [h]
  simp
  rfl

end VectorLikeEvenPlane

end PureU1
