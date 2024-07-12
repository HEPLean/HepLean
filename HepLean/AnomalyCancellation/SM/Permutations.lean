/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.AnomalyCancellation.SM.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic
/-!
# Permutations of SM with no RHN.

We define the group of permutations for the SM charges with no RHN.

-/

universe v u

open Nat
open Finset

namespace SM

open SMCharges
open SMACCs
open BigOperators

/-- The group of `Sₙ` permutations for each species. -/
@[simp]
def PermGroup (n : ℕ) := ∀ (_ : Fin 5), Equiv.Perm (Fin n)

variable {n : ℕ}

@[simp]
instance : Group (PermGroup n) := Pi.group

/-- The image of an element of `permGroup n` under the representation on charges. -/
@[simps!]
def chargeMap (f : PermGroup n) : (SMCharges n).Charges →ₗ[ℚ] (SMCharges n).Charges where
  toFun S := toSpeciesEquiv.symm (fun i => toSpecies i S ∘ f i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The representation of `(permGroup n)` acting on the vector space of charges. -/
@[simp]
def repCharges {n : ℕ} : Representation ℚ (PermGroup n) (SMCharges n).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup, mul_inv_rev]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    simp only [chargeMap_apply, Pi.mul_apply, Pi.inv_apply, Equiv.Perm.coe_mul, LinearMap.mul_apply]
    repeat erw [toSMSpecies_toSpecies_inv]
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    erw [toSMSpecies_toSpecies_inv]
    rfl

lemma repCharges_toSpecies (f : PermGroup n) (S : (SMCharges n).Charges) (j : Fin 5) :
    toSpecies j (repCharges f S) = toSpecies j S ∘ f⁻¹ j := by
  erw [toSMSpecies_toSpecies_inv]

lemma toSpecies_sum_invariant (m : ℕ) (f : PermGroup n) (S : (SMCharges n).Charges) (j : Fin 5) :
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j S) i := by
  rw [repCharges_toSpecies]
  exact Fintype.sum_equiv (f⁻¹ j) (fun x => ((fun a => a ^ m) ∘ (toSpecies j) S ∘ ⇑(f⁻¹ j)) x)
   (fun x => ((fun a => a ^ m) ∘ (toSpecies j) S) x) (congrFun rfl)

lemma accGrav_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accGrav (repCharges f S) = accGrav S :=
  accGrav_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

lemma accSU2_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accSU2 (repCharges f S) = accSU2 S :=
  accSU2_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

lemma accSU3_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

lemma accYY_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accYY (repCharges f S) = accYY S :=
  accYY_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

lemma accQuad_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accQuad (repCharges f S) = accQuad S :=
  accQuad_ext
    (toSpecies_sum_invariant 2 f S)

lemma accCube_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accCube (repCharges f S) = accCube S :=
  accCube_ext (fun j => toSpecies_sum_invariant 3 f S j)

end SM
