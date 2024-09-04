/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Algebra.QuadraticDiscriminant
/-!
DO NOT USE THIS FILE AS AN IMPORT.

## Derivation of the main result of 1907.00514

This file is a demonstration of the derivation of the main result of a paper in high energy physics
using results only from Mathlib.

The paper is:
Hypercharge Quantisation and Fermat's Last Theorem
by Nakarin Lohitsiri and  David Tong.

Despite this file being long, it is important to note that many of the results here,
can be used to prove other results. It, for examples, sets up the physical context
in which the result appears.

It has being checked that every result in this file is needed, in the sense that removing it
breaks a later result. In the future it would be nice to have a tool that can automatically
generate these sorts of files.

This file is 27258 characters long compared to 21697 of the original tex file of the paper.
-/

section

/-- The structure defining a homogeneous quadratic equation. -/
@[simp]
def HomogeneousQuadratic (V : Type) [AddCommMonoid V] [Module ℚ V] : Type :=
  V →ₑ[((fun a => a ^ 2) : ℚ → ℚ)] ℚ

namespace HomogeneousQuadratic

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun : FunLike (HomogeneousQuadratic V) V ℚ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all

end HomogeneousQuadratic

/-- The structure of a symmetric bilinear function. -/
structure BiLinearSymm (V : Type) [AddCommMonoid V] [Module ℚ V] extends V →ₗ[ℚ] V →ₗ[ℚ] ℚ where
  swap' : ∀ S T, toFun S T = toFun T S

namespace BiLinearSymm
open BigOperators

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

/-- The construction of a symmetric bilinear map from `smul` and `map_add` in the first factor,
and swap. -/
@[simps!]
def mk₂ (f : V × V → ℚ) (map_smul : ∀ a S T, f (a • S, T) = a * f (S, T))
    (map_add : ∀ S1 S2 T, f (S1 + S2, T) = f (S1, T) + f (S2, T))
    (swap : ∀ S T, f (S, T) = f (T, S)) : BiLinearSymm V where
  toFun := fun S => {
    toFun := fun T => f (S, T)
    map_add' := by
      intro T1 T2
      simp only
      rw [swap, map_add]
      exact Mathlib.Tactic.LinearCombination.add_pf (swap T1 S) (swap T2 S)
    map_smul' := by
      intro a T
      simp only [eq_ratCast, Rat.cast_eq_id, id_eq, smul_eq_mul]
      rw [swap, map_smul]
      exact congrArg (HMul.hMul a) (swap T S)
  }
  map_smul' := fun a S => LinearMap.ext fun T => map_smul a S T
  map_add' := fun S1 S2 => LinearMap.ext fun T => map_add S1 S2 T
  swap' := swap

end BiLinearSymm

/-- The structure of a homogeneous cubic equation. -/
@[simp]
def HomogeneousCubic (V : Type) [AddCommMonoid V] [Module ℚ V] : Type :=
  V →ₑ[((fun a => a ^ 3) : ℚ → ℚ)] ℚ

namespace HomogeneousCubic

variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun : FunLike (HomogeneousCubic V) V ℚ where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all

end HomogeneousCubic

/-- The structure of a symmetric trilinear function. -/
structure TriLinearSymm (V : Type) [AddCommMonoid V] [Module ℚ V] extends
    V →ₗ[ℚ] V →ₗ[ℚ] V →ₗ[ℚ] ℚ where
  swap₁' : ∀ S T L, toFun S T L = toFun T S L
  swap₂' : ∀ S T L, toFun S T L = toFun S L T

namespace TriLinearSymm
open BigOperators
variable {V : Type} [AddCommMonoid V] [Module ℚ V]

instance instFun : FunLike (TriLinearSymm V) V (V →ₗ[ℚ] V →ₗ[ℚ] ℚ) where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp_all

/-- The construction of a symmetric trilinear map from `smul` and `map_add` in the first factor,
and two swap. -/
@[simps!]
def mk₃ (f : V × V × V→ ℚ) (map_smul : ∀ a S T L, f (a • S, T, L) = a * f (S, T, L))
    (map_add : ∀ S1 S2 T L, f (S1 + S2, T, L) = f (S1, T, L) + f (S2, T, L))
    (swap₁ : ∀ S T L, f (S, T, L) = f (T, S, L))
    (swap₂ : ∀ S T L, f (S, T, L) = f (S, L, T)) : TriLinearSymm V where
  toFun := fun S => (BiLinearSymm.mk₂ (fun T => f (S, T))
    (by
      intro a T L
      simp only
      rw [swap₁, map_smul, swap₁])
    (by
      intro S1 S2 T
      simp only
      rw [swap₁, map_add, swap₁, swap₁ S2 S T])
    (by
      intro L T
      exact swap₂ S L T)).toLinearMap
  map_add' S1 S2 := by
    apply LinearMap.ext
    intro T
    apply LinearMap.ext
    intro S
    exact map_add S1 S2 T S
  map_smul' a S :=
    LinearMap.ext fun T => LinearMap.ext fun L => map_smul a S T L
  swap₁' := swap₁
  swap₂' := swap₂

lemma swap₁ (f : TriLinearSymm V) (S T L : V) : f S T L = f T S L :=
  f.swap₁' S T L

lemma swap₂ (f : TriLinearSymm V) (S T L : V) : f S T L = f S L T :=
  f.swap₂' S T L

lemma swap₃ (f : TriLinearSymm V) (S T L : V) : f S T L = f L T S := by
  rw [f.swap₁, f.swap₂, f.swap₁]

lemma map_smul₁ (f : TriLinearSymm V) (a : ℚ) (S T L : V) :
    f (a • S) T L = a * f S T L := by
  erw [f.map_smul a S]
  rfl

lemma map_smul₂ (f : TriLinearSymm V) (S : V) (a : ℚ) (T L : V) :
    f S (a • T) L = a * f S T L := by
  rw [f.swap₁, f.map_smul₁, f.swap₁]

lemma map_smul₃ (f : TriLinearSymm V) (S T : V) (a : ℚ) (L : V) :
    f S T (a • L) = a * f S T L := by
  rw [f.swap₃, f.map_smul₁, f.swap₃]

/-- The homogenous cubic equation obtainable from a symmetric trilinear function. -/
@[simps!]
def toCubic {charges : Type} [AddCommMonoid charges] [Module ℚ charges]
    (τ : TriLinearSymm charges) : HomogeneousCubic charges where
  toFun S := τ S S S
  map_smul' a S := by
    simp only [smul_eq_mul]
    rw [τ.map_smul₁, τ.map_smul₂, τ.map_smul₃]
    ring

end TriLinearSymm
end

section

/-- A system of charges, specified by the number of charges. -/
structure ACCSystemCharges where
  /-- The number of charges. -/
  numberCharges : ℕ

/--
  Creates an `ACCSystemCharges` object with the specified number of charges.
-/
def ACCSystemChargesMk (n : ℕ) : ACCSystemCharges where
  numberCharges := n

namespace ACCSystemCharges

/-- The charges as functions from `Fin χ.numberCharges → ℚ`. -/
def Charges (χ : ACCSystemCharges) : Type := Fin χ.numberCharges → ℚ

/--
  An instance to provide the necessary operations and properties for `charges` to form an additive
  commutative monoid.
-/
@[simps!]
instance chargesAddCommMonoid (χ : ACCSystemCharges) : AddCommMonoid χ.Charges :=
  Pi.addCommMonoid

/--
  An instance to provide the necessary operations and properties for `charges` to form a module
  over the field `ℚ`.
-/
@[simps!]
instance chargesModule (χ : ACCSystemCharges) : Module ℚ χ.Charges :=
  Pi.module _ _ _

end ACCSystemCharges

/-- The type of charges plus the linear ACCs. -/
structure ACCSystemLinear extends ACCSystemCharges where
  /-- The number of linear ACCs. -/
  numberLinear : ℕ
  /-- The linear ACCs. -/
  linearACCs : Fin numberLinear → (toACCSystemCharges.Charges →ₗ[ℚ] ℚ)

namespace ACCSystemLinear

/-- The type of solutions to the linear ACCs. -/
structure LinSols (χ : ACCSystemLinear) where
  /-- The underlying charge. -/
  val : χ.1.Charges
  /-- The condition that the charge satisfies the linear ACCs. -/
  linearSol : ∀ i : Fin χ.numberLinear, χ.linearACCs i val = 0

/-- Two solutions are equal if the underlying charges are equal. -/
@[ext]
lemma LinSols.ext {χ : ACCSystemLinear} {S T : χ.LinSols} (h : S.val = T.val) : S = T := by
  cases' S
  simp_all only


end ACCSystemLinear

/-- The type of charges plus the linear ACCs plus the quadratic ACCs. -/
structure ACCSystemQuad extends ACCSystemLinear where
  /-- The number of quadratic ACCs. -/
  numberQuadratic : ℕ
  /-- The quadratic ACCs. -/
  quadraticACCs : Fin numberQuadratic → HomogeneousQuadratic toACCSystemCharges.Charges

namespace ACCSystemQuad

/-- The type of solutions to the linear and quadratic ACCs. -/
structure QuadSols (χ : ACCSystemQuad) extends χ.LinSols where
  /-- The condition that the charge satisfies the quadratic ACCs. -/
  quadSol : ∀ i : Fin χ.numberQuadratic, (χ.quadraticACCs i) val = 0

end ACCSystemQuad

/-- The type of charges plus the anomaly cancellation conditions. -/
structure ACCSystem extends ACCSystemQuad where
  /-- The cubic ACC. -/
  cubicACC : HomogeneousCubic toACCSystemCharges.Charges

namespace ACCSystem

/-- The type of solutions to the anomaly cancellation conditions. -/
structure Sols (χ : ACCSystem) extends χ.QuadSols where
  /-- The condition that the charge satisfies the cubic ACC. -/
  cubicSol : χ.cubicACC val = 0

end ACCSystem

end

section

universe v u
open Nat
open BigOperators

/-- Associate to each (including RHN) SM fermion a set of charges-/
@[simps!]
def SMCharges (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk (5 * n)

/-- The vector space associated with a single species of fermions. -/
@[simps!]
def SMSpecies (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk n

namespace SMCharges

variable {n : ℕ}

/-- An equivalence between the set `(SMCharges n).charges` and the set
  `(Fin 5 → Fin n → ℚ)`. -/
@[simps!]
def toSpeciesEquiv : (SMCharges n).Charges ≃ (Fin 5 → Fin n → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans ((@finProdFinEquiv 5 n).arrowCongr (Equiv.refl ℚ))).symm

/-- For a given `i ∈ Fin 5`, the projection of a charge onto that species. -/
@[simps!]
def toSpecies (i : Fin 5) : (SMCharges n).Charges →ₗ[ℚ] (SMSpecies n).Charges where
  toFun S := toSpeciesEquiv S i
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl

lemma charges_eq_toSpecies_eq (S T : (SMCharges n).Charges) :
    S = T ↔ ∀ i, toSpecies i S = toSpecies i T := by
  refine Iff.intro (fun a i => congrArg (⇑(toSpecies i)) a) (fun h => ?_)
  apply toSpeciesEquiv.injective
  exact (Set.eqOn_univ (toSpeciesEquiv S) (toSpeciesEquiv T)).mp fun ⦃x⦄ _ => h x


/-- The `Q` charges as a map `Fin n → ℚ`. -/
abbrev Q := @toSpecies n 0

/-- The `U` charges as a map `Fin n → ℚ`. -/
abbrev U := @toSpecies n 1

/-- The `D` charges as a map `Fin n → ℚ`. -/
abbrev D := @toSpecies n 2

/-- The `L` charges as a map `Fin n → ℚ`. -/
abbrev L := @toSpecies n 3

/-- The `E` charges as a map `Fin n → ℚ`. -/
abbrev E := @toSpecies n 4

end SMCharges

namespace SMACCs

open SMCharges

variable {n : ℕ}

/-- The gravitational anomaly equation. -/
@[simp]
def accGrav : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i + 2 * L S i + E S i)
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp [Pi.add_apply, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp only
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    --rw [show Rat.cast a = a from rfl]
    ring

/-- The `SU(2)` anomaly equation. -/
@[simp]
def accSU2 : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i)
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp [Pi.add_apply, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp only
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    --rw [show Rat.cast a = a from rfl]
    ring

/-- The `SU(3)` anomaly equations. -/
@[simp]
def accSU3 : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * Q S i + U S i + D S i)
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp [Pi.add_apply, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp only
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    --rw [show Rat.cast a = a from rfl]
    ring

/-- The trilinear function defining the cubic. -/
@[simps!]
def cubeTriLin : TriLinearSymm (SMCharges n).Charges := TriLinearSymm.mk₃
  (fun S => ∑ i, (6 * ((Q S.1 i) * (Q S.2.1 i) * (Q S.2.2 i))
    + 3 * ((U S.1 i) * (U S.2.1 i) * (U S.2.2 i))
    + 3 * ((D S.1 i) * (D S.2.1 i) * (D S.2.2 i))
    + 2 * ((L S.1 i) * (L S.2.1 i) * (L S.2.2 i))
    + ((E S.1 i) * (E S.2.1 i) * (E S.2.2 i))))
  (by
    intro a S T R
    simp only
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_smul]
    simp only [HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T R L
    simp only
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply, Fin.isValue]
    ring)
  (by
    intro S T L
    simp only [SMSpecies_numberCharges, toSpecies_apply, Fin.isValue]
    apply Fintype.sum_congr
    intro i
    ring)
  (by
    intro S T L
    simp only [SMSpecies_numberCharges, toSpecies_apply, Fin.isValue]
    apply Fintype.sum_congr
    intro i
    ring)

/-- The cubic acc. -/
@[simp]
def accCube : HomogeneousCubic (SMCharges n).Charges := cubeTriLin.toCubic

end SMACCs

end

section

universe v u

namespace SM
open SMCharges
open SMACCs
open BigOperators

/-- The ACC system for the standard model without RHN and without the gravitational ACC. -/
@[simps!]
def SMNoGrav (n : ℕ) : ACCSystem where
  numberLinear := 2
  linearACCs := fun i =>
    match i with
    | 0 => @accSU2 n
    | 1 => accSU3
  numberQuadratic := 0
  quadraticACCs := by
    intro i
    exact Fin.elim0 i
  cubicACC := accCube

namespace SMNoGrav

variable {n : ℕ}

lemma SU2Sol (S : (SMNoGrav n).LinSols) : accSU2 S.val = 0 := by
  have hS := S.linearSol
  simp only [SMNoGrav_numberLinear, SMNoGrav_linearACCs, Fin.isValue] at hS
  exact hS 0

lemma SU3Sol (S : (SMNoGrav n).LinSols) : accSU3 S.val = 0 := by
  have hS := S.linearSol
  simp only [SMNoGrav_numberLinear, SMNoGrav_linearACCs, Fin.isValue] at hS
  exact hS 1

lemma cubeSol (S : (SMNoGrav n).Sols) : accCube S.val = 0 := by
  exact S.cubicSol

/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `AnomalyFreeLinear`. -/
def chargeToLinear (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).LinSols :=
  ⟨S, by
    intro i
    simp only [SMNoGrav_numberLinear] at i
    match i with
    | 0 => exact hSU2
    | 1 => exact hSU3⟩

end SMNoGrav

end SM

end

section

universe v u
namespace SM
namespace SMNoGrav
namespace One

open SMCharges
open SMACCs
open BigOperators

/-- The parameters for a linear parameterization to the solution of the linear ACCs. -/
structure linearParameters where
  /-- The parameter `Q'`. -/
  Q' : ℚ
  /-- The parameter `Y`. -/
  Y : ℚ
  /-- The parameter `E'`. -/
  E' : ℚ

namespace linearParameters

@[ext]
lemma ext {S T : linearParameters} (hQ : S.Q' = T.Q') (hY : S.Y = T.Y) (hE : S.E' = T.E') :
    S = T := by
  cases' S
  simp_all only

/-- The map from the linear parameters to elements of `(SMNoGrav 1).charges`. -/
@[simp]
def asCharges (S : linearParameters) : (SMNoGrav 1).Charges := fun i =>
  match i with
  | (0 : Fin 5) => S.Q'
  | (1 : Fin 5) => S.Y - S.Q'
  | (2 : Fin 5) => - (S.Y + S.Q')
  | (3: Fin 5) => - 3 * S.Q'
  | (4 : Fin 5) => S.E'

lemma speciesVal {i : Fin 5} (S : linearParameters) :
    (toSpecies i) S.asCharges (0 : Fin 1) = S.asCharges i := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl

/-- The map from the linear paramaters to elements of `(SMNoGrav 1).LinSols`. -/
def asLinear (S : linearParameters) : (SMNoGrav 1).LinSols :=
  chargeToLinear S.asCharges (by
    simp only [accSU2, SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk]
    erw [speciesVal, speciesVal]
    simp)
    (by
    simp only [accSU3, SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk]
    repeat erw [speciesVal]
    simp only [asCharges, neg_add_rev]
    ring)

lemma asLinear_val (S : linearParameters) : S.asLinear.val = S.asCharges := by
  rfl

lemma cubic (S : linearParameters) :
    accCube (S.asCharges) = - 54 * S.Q'^3 - 18 * S.Q' * S.Y ^ 2 + S.E'^3 := by
  simp only [HomogeneousCubic, accCube, cubeTriLin, TriLinearSymm.toCubic_apply,
    TriLinearSymm.mk₃_toFun_apply_apply]
  simp only [SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton]
  repeat erw [speciesVal]
  simp only [asCharges, neg_add_rev, neg_mul, mul_neg, neg_neg]
  ring

lemma cubic_zero_Q'_zero (S : linearParameters) (hc : accCube (S.asCharges) = 0)
    (h : S.Q' = 0) : S.E' = 0 := by
  rw [cubic, h] at hc
  simp at hc
  exact hc

lemma cubic_zero_E'_zero (S : linearParameters) (hc : accCube (S.asCharges) = 0)
    (h : S.E' = 0) : S.Q' = 0 := by
  rw [cubic, h] at hc
  simp at hc
  have h1 : -(54 * S.Q' ^ 3) - 18 * S.Q' * S.Y ^ 2 = - 18 * (3 * S.Q' ^ 2 + S.Y ^ 2) * S.Q' := by
    ring
  rw [h1] at hc
  simp at hc
  cases' hc with hc hc
  · have h2 := (add_eq_zero_iff_of_nonneg (by nlinarith) (sq_nonneg S.Y)).mp hc
    simp at h2
    exact h2.1
  · exact hc

/-- The bijection between the type of linear parameters and `(SMNoGrav 1).LinSols`. -/
def bijection : linearParameters ≃ (SMNoGrav 1).LinSols where
  toFun S := S.asLinear
  invFun S := ⟨SMCharges.Q S.val (0 : Fin 1), (SMCharges.U S.val (0 : Fin 1) -
      SMCharges.D S.val (0 : Fin 1))/2,
      SMCharges.E S.val (0 : Fin 1)⟩
  left_inv S := by
    apply linearParameters.ext
    · rfl
    · simp only [Fin.isValue]
      repeat erw [speciesVal]
      simp only [asCharges, neg_add_rev]
      ring
    · rfl
  right_inv S := by
    simp only [Fin.isValue, toSpecies_apply]
    apply ACCSystemLinear.LinSols.ext
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [asLinear_val]
    funext j
    have hj : j = (0 : Fin 1) := by
      simp only [Fin.isValue]
      ext
      simp
    subst hj
    erw [speciesVal]
    have h1 := SU3Sol S
    simp at h1
    have h2 := SU2Sol S
    simp at h2
    match i with
    | 0 => rfl
    | 1 =>
      field_simp
      linear_combination -(1 * h1)
    | 2 =>
      field_simp
      linear_combination -(1 * h1)
    | 3 =>
      field_simp
      linear_combination -(1 * h2)
    | 4 => rfl

/-- The bijection between the linear parameters and `(SMNoGrav 1).LinSols` in the special
case when Q and E are both not zero. -/
def bijectionQEZero : {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} ≃
    {S : (SMNoGrav 1).LinSols // Q S.val (0 : Fin 1) ≠ 0 ∧ E S.val (0 : Fin 1) ≠ 0} where
  toFun S := ⟨bijection S, S.2⟩
  invFun S := ⟨bijection.symm S, S.2⟩
  left_inv S := Subtype.ext (bijection.left_inv S.1)
  right_inv S := Subtype.ext (bijection.right_inv S.1)

lemma grav (S : linearParameters) :
    accGrav S.asCharges = 0 ↔ S.E' = 6 * S.Q' := by
  rw [accGrav]
  simp only [SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk]
  repeat erw [speciesVal]
  simp only [asCharges, neg_add_rev, neg_mul, mul_neg]
  ring_nf
  rw [add_comm, add_eq_zero_iff_eq_neg]
  simp

end linearParameters

/-- The parameters for solutions to the linear ACCs with the condition that Q and E are
  non-zero. -/
structure linearParametersQENeqZero where
  /-- The parameter `x`. -/
  x : ℚ
  /-- The parameter `v`. -/
  v : ℚ
  /-- The parameter `w`. -/
  w : ℚ
  hx : x ≠ 0
  hvw : v + w ≠ 0

namespace linearParametersQENeqZero

@[ext]
lemma ext {S T : linearParametersQENeqZero} (hx : S.x = T.x) (hv : S.v = T.v)
    (hw : S.w = T.w) : S = T := by
  cases' S
  simp_all only

/-- A map from `linearParametersQENeqZero` to `linearParameters`. -/
@[simps!]
def toLinearParameters (S : linearParametersQENeqZero) :
    {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} :=
  ⟨⟨S.x, 3 * S.x * (S.v - S.w) / (S.v + S.w), - 6 * S.x / (S.v + S.w)⟩,
    by
      apply And.intro S.hx
      simp only [neg_mul, ne_eq, div_eq_zero_iff, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
        false_or]
      rw [not_or]
      exact And.intro S.hx S.hvw⟩

/-- A map from `linearParameters` to `linearParametersQENeqZero` in the special case when
`Q'` and `E'` of the linear parameters are non-zero. -/
@[simps!]
def tolinearParametersQNeqZero (S : {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0}) :
    linearParametersQENeqZero :=
  ⟨S.1.Q', - (3 * S.1.Q' + S.1.Y) / S.1.E', - (3 * S.1.Q' - S.1.Y)/ S.1.E', S.2.1,
    by
      simp only [ne_eq, neg_add_rev, neg_sub]
      field_simp
      ring_nf
      simp only [neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, or_false]
      exact S.2⟩

/-- A bijection between the type `linearParametersQENeqZero` and linear parameters
  with `Q'` and `E'` non-zero. -/
@[simps!]
def bijectionLinearParameters :
    linearParametersQENeqZero ≃ {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} where
  toFun := toLinearParameters
  invFun := tolinearParametersQNeqZero
  left_inv S := by
    have hvw := S.hvw
    have hQ := S.hx
    apply linearParametersQENeqZero.ext
    · rfl
    · field_simp
      ring
    · simp only [tolinearParametersQNeqZero_w, toLinearParameters_coe_Y, toLinearParameters_coe_Q',
        toLinearParameters_coe_E']
      field_simp
      ring
  right_inv S := by
    apply Subtype.ext
    have hQ := S.2.1
    have hE := S.2.2
    apply linearParameters.ext
    · rfl
    · field_simp
      ring_nf
      field_simp [hQ, hE]
    · field_simp
      ring_nf
      field_simp [hQ, hE]

/-- The bijection between `linearParametersQENeqZero` and `LinSols` with `Q` and `E` non-zero. -/
def bijection : linearParametersQENeqZero ≃
    {S : (SMNoGrav 1).LinSols // Q S.val (0 : Fin 1) ≠ 0 ∧ E S.val (0 : Fin 1) ≠ 0} :=
  bijectionLinearParameters.trans (linearParameters.bijectionQEZero)

lemma cubic (S : linearParametersQENeqZero) :
    accCube (bijection S).1.val = 0 ↔ S.v ^ 3 + S.w ^ 3 = -1 := by
  erw [linearParameters.cubic]
  simp only [ne_eq, bijectionLinearParameters_apply_coe_Q', neg_mul,
    bijectionLinearParameters_apply_coe_Y, div_pow, bijectionLinearParameters_apply_coe_E']
  have hvw := S.hvw
  have hQ := S.hx
  field_simp
  have h1 : (-(54 * S.x ^ 3 * (S.v + S.w) ^ 2) - 18 * S.x * (3 * S.x * (S.v - S.w)) ^ 2) *
      (S.v + S.w) ^ 3 + (-(6 * S.x)) ^ 3 * (S.v + S.w) ^ 2 =
      - 216 * S.x ^3 * (S.v ^3 + S.w ^3 +1) * (S.v + S.w) ^ 2 := by
    ring
  rw [h1]
  simp_all
  exact add_eq_zero_iff_eq_neg

lemma cubic_v_or_w_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (FLTThree : FermatLastTheoremWith ℚ 3) :
    S.v = 0 ∨ S.w = 0 := by
  rw [S.cubic] at h
  have h1 : (-1)^3 = (-1 : ℚ) := by rfl
  rw [← h1] at h
  by_contra hn
  simp [not_or] at hn
  have h2 := FLTThree S.v S.w (-1) hn.1 hn.2 (Ne.symm (ne_of_beq_false (by rfl)))
  exact h2 h

lemma cubic_v_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (hv : S.v = 0) : S.w = -1 := by
  rw [S.cubic, hv] at h
  simp at h
  have h' : (S.w + 1) * (1 * S.w * S.w + (-1) * S.w + 1) = 0 := by
    ring_nf
    exact add_eq_zero_iff_neg_eq.mpr (id (Eq.symm h))
  have h'' : (1 * S.w * S.w + (-1) * S.w + 1) ≠ 0 := by
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ S.w
    intro s
    by_contra hn
    have h : s ^ 2 < 0 := by
      rw [← hn]
      rfl
    nlinarith
  simp_all
  exact eq_neg_of_add_eq_zero_left h'

lemma cube_w_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (hw : S.w = 0) : S.v = -1 := by
  rw [S.cubic, hw] at h
  simp at h
  have h' : (S.v + 1) * (1 * S.v * S.v + (-1) * S.v + 1) = 0 := by
    ring_nf
    exact add_eq_zero_iff_neg_eq.mpr (id (Eq.symm h))
  have h'' : (1 * S.v * S.v + (-1) * S.v + 1) ≠ 0 := by
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ S.v
    intro s
    by_contra hn
    have h : s ^ 2 < 0 := by
      rw [← hn]
      rfl
    nlinarith
  simp_all
  exact eq_neg_of_add_eq_zero_left h'

lemma cube_w_v (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (FLTThree : FermatLastTheoremWith ℚ 3) :
    (S.v = -1 ∧ S.w = 0) ∨ (S.v = 0 ∧ S.w = -1) := by
  have h' := cubic_v_or_w_zero S h FLTThree
  cases' h' with hx hx
  · simp [hx]
    exact cubic_v_zero S h hx
  · simp [hx]
    exact cube_w_zero S h hx

lemma grav (S : linearParametersQENeqZero) : accGrav (bijection S).1.val = 0 ↔ S.v + S.w = -1 := by
  erw [linearParameters.grav]
  have hvw := S.hvw
  have hQ := S.hx
  field_simp
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · apply (mul_right_inj' hQ).mp
    linear_combination -1 * h / 6
  · rw [h]
    exact Eq.symm (mul_neg_one (6 * S.x))

lemma grav_of_cubic (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (FLTThree : FermatLastTheoremWith ℚ 3) :
    accGrav (bijection S).1.val = 0 := by
  rw [grav]
  have h' := cube_w_v S h FLTThree
  cases' h' with h h
  · rw [h.1, h.2]
    exact Rat.add_zero (-1)
  · rw [h.1, h.2]
    exact Rat.zero_add (-1)

end linearParametersQENeqZero

end One
end SMNoGrav
end SM

end

section

universe v u
namespace SM
namespace SMNoGrav
namespace One

open SMCharges
open SMACCs
open BigOperators

lemma E_zero_iff_Q_zero {S : (SMNoGrav 1).Sols} : Q S.val (0 : Fin 1) = 0 ↔
    E S.val (0 : Fin 1) = 0 := by
  let S' := linearParameters.bijection.symm S.1.1
  have hC := cubeSol S
  have hS' := congrArg (fun S => S.val) (linearParameters.bijection.right_inv S.1.1)
  change S'.asCharges = S.val at hS'
  rw [← hS'] at hC
  exact Iff.intro (fun hQ => S'.cubic_zero_Q'_zero hC hQ) (fun hE => S'.cubic_zero_E'_zero hC hE)

lemma accGrav_Q_zero {S : (SMNoGrav 1).Sols} (hQ : Q S.val (0 : Fin 1) = 0) :
    accGrav S.val = 0 := by
  rw [accGrav]
  simp only [SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk]
  erw [hQ, E_zero_iff_Q_zero.mp hQ]
  have h1 := SU2Sol S.1.1
  have h2 := SU3Sol S.1.1
  simp only [accSU2, SMSpecies_numberCharges, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, LinearMap.coe_mk, AddHom.coe_mk, accSU3] at h1 h2
  erw [hQ] at h1 h2
  simp_all
  linear_combination 3 * h2

lemma accGrav_Q_neq_zero {S : (SMNoGrav 1).Sols} (hQ : Q S.val (0 : Fin 1) ≠ 0)
    (FLTThree : FermatLastTheoremWith ℚ 3) :
    accGrav S.val = 0 := by
  have hE := E_zero_iff_Q_zero.mpr.mt hQ
  let S' := linearParametersQENeqZero.bijection.symm ⟨S.1.1, And.intro hQ hE⟩
  have hC := cubeSol S
  have hS' := congrArg (fun S => S.val.val)
    (linearParametersQENeqZero.bijection.right_inv ⟨S.1.1, And.intro hQ hE⟩)
  change _ = S.val at hS'
  rw [← hS'] at hC ⊢
  exact S'.grav_of_cubic hC FLTThree

/-- Any solution to the ACCs without gravity satisfies the gravitational ACC. -/
theorem accGravSatisfied {S : (SMNoGrav 1).Sols} (FLTThree : FermatLastTheoremWith ℚ 3) :
    accGrav S.val = 0 := by
  by_cases hQ : Q S.val (0 : Fin 1)= 0
  · exact accGrav_Q_zero hQ
  · exact accGrav_Q_neq_zero hQ FLTThree

end One
end SMNoGrav
end SM

end
