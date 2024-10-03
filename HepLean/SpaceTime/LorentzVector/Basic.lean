/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!

# Lorentz vectors

(aka 4-vectors)

In this file we define a Lorentz vector (in 4d, this is more often called a 4-vector).

One of the most important example of a Lorentz vector is SpaceTime.

We will define the group action of the Lorentz group on Lorentz vectors in
`HepLean.SpaceTime.LorentzVector.LorentzAction` in such a way that `LorentzVector`
corresponds to contravariant Lorentz tensors.

-/

/- The number of space dimensions . -/
variable (d : ℕ)

/-- The type of (contravariant) Lorentz Vectors in `d`-space dimensions. -/
def LorentzVector : Type := (Fin 1 ⊕ Fin d) → ℝ

/-- An instance of an additive commutative monoid on `LorentzVector`. -/
instance : AddCommMonoid (LorentzVector d) := Pi.addCommMonoid

/-- An instance of a module on `LorentzVector`. -/
noncomputable instance : Module ℝ (LorentzVector d) := Pi.module _ _ _

instance : AddCommGroup (LorentzVector d) := Pi.addCommGroup

/-- The structure of a topological space `LorentzVector d`. -/
instance : TopologicalSpace (LorentzVector d) :=
  haveI : NormedAddCommGroup (LorentzVector d) := Pi.normedAddCommGroup
  UniformSpace.toTopologicalSpace

namespace LorentzVector

variable {d : ℕ} (v : LorentzVector d)

/-- The space components. -/
@[simp]
def space : EuclideanSpace ℝ (Fin d) := v ∘ Sum.inr

/-- The time component. -/
@[simp]
def time : ℝ := v (Sum.inl 0)

/-!

# The standard basis

-/

/-- The standard basis of `LorentzVector` indexed by `Fin 1 ⊕ Fin (d)`. -/
@[simps!]
noncomputable def stdBasis : Basis (Fin 1 ⊕ Fin (d)) ℝ (LorentzVector d) := Pi.basisFun ℝ _

/-- Notation for `stdBasis`. -/
scoped[LorentzVector] notation "e" => stdBasis

lemma stdBasis_apply (μ ν : Fin 1 ⊕ Fin d) : e μ ν = if μ = ν then 1 else 0 := by
  erw [stdBasis, Pi.basisFun_apply, Pi.single_apply]
  refine Eq.symm (ite_congr ?h₁ (congrFun rfl) (congrFun rfl))
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)

lemma decomp_stdBasis (v : LorentzVector d) : ∑ i, v i • e i = v := by
  funext ν
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem ν]
  · simp only [HSMul.hSMul, SMul.smul, stdBasis]
    erw [Pi.basisFun_apply]
    simp only [Pi.single_eq_same, mul_one]
  · exact Finset.mem_univ ν
  · intros b _ hbi
    simp only [HSMul.hSMul, SMul.smul, stdBasis, mul_eq_zero]
    erw [Pi.basisFun_apply]
    simp only [Pi.single]
    apply Or.inr $ Function.update_noteq (id (Ne.symm hbi)) 1 0

@[simp]
lemma decomp_stdBasis' (v : LorentzVector d) :
    v (Sum.inl 0) • e (Sum.inl 0) + ∑ a₂ : Fin d, v (Sum.inr a₂) • e (Sum.inr a₂) = v := by
  trans ∑ i, v i • e i
  · simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
  · exact decomp_stdBasis v

/-- The standard unit time vector. -/
noncomputable abbrev timeVec : (LorentzVector d) := e (Sum.inl 0)

lemma timeVec_space : (@timeVec d).space = 0 := by
  funext i
  simp only [space, Function.comp_apply, stdBasis_apply, Fin.isValue, reduceCtorEq, ↓reduceIte,
    PiLp.zero_apply]

lemma timeVec_time: (@timeVec d).time = 1 := by
  simp only [time, Fin.isValue, stdBasis_apply, ↓reduceIte]

/-!

# Reflection of space

-/

/-- The reflection of space as a linear map. -/
@[simps!]
def spaceReflectionLin : LorentzVector d →ₗ[ℝ] LorentzVector d where
  toFun x := Sum.elim (x ∘ Sum.inl) (- x ∘ Sum.inr)
  map_add' x y := by
    funext i
    rcases i with i | i
    · rfl
    · simp only [Sum.elim_inr, Pi.neg_apply]
      apply neg_add
  map_smul' c x := by
    funext i
    rcases i with i | i
    · rfl
    · simp [HSMul.hSMul, SMul.smul]

/-- The reflection of space. -/
@[simp]
def spaceReflection : LorentzVector d := spaceReflectionLin v

lemma spaceReflection_space : v.spaceReflection.space = - v.space := rfl

lemma spaceReflection_time : v.spaceReflection.time = v.time := rfl

end LorentzVector
