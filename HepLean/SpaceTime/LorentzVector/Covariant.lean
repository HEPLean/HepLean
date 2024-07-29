/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Basic
import HepLean.SpaceTime.LorentzGroup.Basic
import Mathlib.RepresentationTheory.Basic
/-!

# Covariant Lorentz vectors

The type `LorentzVector` corresponds to contravariant Lorentz tensors.
In this section we define covariant Lorentz tensors.

-/
/-! TODO: Define equivariant map between contravariant and covariant lorentz tensors. -/

noncomputable section

/- The number of space dimensions . -/
variable (d : ℕ)

/-- The type of covariant Lorentz Vectors in `d`-space dimensions. -/
def CovariantLorentzVector : Type := (Fin 1 ⊕ Fin d) → ℝ

/-- An instance of an additive commutative monoid on `LorentzVector`. -/
instance : AddCommMonoid (CovariantLorentzVector d) := Pi.addCommMonoid

/-- An instance of a module on `LorentzVector`. -/
noncomputable instance : Module ℝ (CovariantLorentzVector d) := Pi.module _ _ _

instance : AddCommGroup (CovariantLorentzVector d) := Pi.addCommGroup

/-- The structure of a topological space `LorentzVector d`. -/
instance : TopologicalSpace (CovariantLorentzVector d) :=
  haveI : NormedAddCommGroup (CovariantLorentzVector d) := Pi.normedAddCommGroup
  UniformSpace.toTopologicalSpace

namespace CovariantLorentzVector

variable {d : ℕ} (v : CovariantLorentzVector d)

/-- The standard basis of `LorentzVector` indexed by `Fin 1 ⊕ Fin (d)`. -/
@[simps!]
noncomputable def stdBasis : Basis (Fin 1 ⊕ Fin (d)) ℝ (CovariantLorentzVector d) := Pi.basisFun ℝ _

lemma decomp_stdBasis (v : CovariantLorentzVector d) : ∑ i, v i • stdBasis i = v := by
  funext ν
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem ν]
  simp [HSMul.hSMul, SMul.smul, stdBasis, Pi.basisFun_apply]
  erw [Pi.basisFun_apply]
  simp only [LinearMap.stdBasis_same, mul_one]
  exact Finset.mem_univ ν
  intros b _ hbi
  simp [HSMul.hSMul, SMul.smul, stdBasis, Pi.basisFun_apply]
  erw [Pi.basisFun_apply]
  simp [LinearMap.stdBasis_apply]
  exact Or.inr hbi

@[simp]
lemma decomp_stdBasis' (v : CovariantLorentzVector d) :
    v (Sum.inl 0) • stdBasis (Sum.inl 0) + ∑ a₂ : Fin d, v (Sum.inr a₂) • stdBasis (Sum.inr a₂)  = v := by
  trans ∑ i, v i • stdBasis i
  simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton]
  exact decomp_stdBasis v

/-!

## Lorentz group action on covariant Lorentz vectors

-/

/-- The representation of the Lorentz group acting on covariant Lorentz vectors. -/
def rep : Representation ℝ (LorentzGroup d) (CovariantLorentzVector d) where
  toFun g := Matrix.toLinAlgEquiv stdBasis (LorentzGroup.transpose g⁻¹)
  map_one' := by
    simp only [inv_one, LorentzGroup.transpose_one, lorentzGroupIsGroup_one_coe, map_one]
  map_mul' x y := by
    simp only [mul_inv_rev, lorentzGroupIsGroup_inv, LorentzGroup.transpose_mul,
      lorentzGroupIsGroup_mul_coe, map_mul]

end CovariantLorentzVector

end
