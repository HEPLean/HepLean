/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.MinkowskiMetric
import HepLean.SpaceTime.LorentzVector.NormOne
/-!
# The Lorentz Group

We define the Lorentz group.

## References

- http://home.ku.edu.tr/~amostafazadeh/phys517_518/phys517_2016f/Handouts/A_Jaffi_Lorentz_Group.pdf

-/
/-! TODO: Show that the Lorentz is a Lie group. -/

noncomputable section

open Matrix
open Complex
open ComplexConjugate

/-!
## Matrices which preserves the Minkowski metric

We start studying the properties of matrices which preserve `ηLin`.
These matrices form the Lorentz group, which we will define in the next section at `lorentzGroup`.

-/
variable {d : ℕ}

open minkowskiMetric in
/-- The Lorentz group is the subset of matrices which preserve the minkowski metric. -/
def LorentzGroup (d : ℕ) : Set (Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :=
    {Λ : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ |
     ∀ (x y : LorentzVector d), ⟪Λ *ᵥ x, Λ *ᵥ y⟫ₘ = ⟪x, y⟫ₘ}

namespace LorentzGroup
/-- Notation for the Lorentz group. -/
scoped[LorentzGroup] notation (name := lorentzGroup_notation) "𝓛" => LorentzGroup

open minkowskiMetric

variable {Λ Λ' : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}

/-!

# Membership conditions

-/

lemma mem_iff_norm : Λ ∈ LorentzGroup d ↔
    ∀ (x : LorentzVector d), ⟪Λ *ᵥ x, Λ *ᵥ x⟫ₘ = ⟪x, x⟫ₘ := by
  refine Iff.intro (fun h x => h x x) (fun h x y => ?_)
  have hp := h (x + y)
  have hn := h (x - y)
  rw [mulVec_add] at hp
  rw [mulVec_sub] at hn
  simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply] at hp hn
  rw [symm (Λ *ᵥ y) (Λ *ᵥ x), symm y x] at hp hn
  linear_combination hp / 4 + -1 * hn / 4

lemma mem_iff_on_right : Λ ∈ LorentzGroup d ↔
    ∀ (x y : LorentzVector d), ⟪x, (dual Λ * Λ) *ᵥ y⟫ₘ = ⟪x, y⟫ₘ := by
  apply Iff.intro
  intro h x y
  have h1 := h x y
  rw [← dual_mulVec_right, mulVec_mulVec] at h1
  exact h1
  intro h x y
  rw [← dual_mulVec_right, mulVec_mulVec]
  exact h x y

lemma mem_iff_dual_mul_self : Λ ∈ LorentzGroup d ↔ dual Λ * Λ = 1 := by
  rw [mem_iff_on_right, matrix_eq_id_iff]
  exact forall_comm

lemma mem_iff_self_mul_dual : Λ ∈ LorentzGroup d ↔ Λ * dual Λ = 1 := by
  rw [mem_iff_dual_mul_self]
  exact mul_eq_one_comm

lemma mem_iff_transpose : Λ ∈ LorentzGroup d ↔ Λᵀ ∈ LorentzGroup d := by
  apply Iff.intro
  · intro h
    have h1 := congrArg transpose ((mem_iff_dual_mul_self).mp h)
    rw [dual, transpose_mul, transpose_mul, transpose_mul, minkowskiMatrix.eq_transpose,
      ← mul_assoc, transpose_one] at h1
    rw [mem_iff_self_mul_dual, ← h1, dual]
    noncomm_ring
  · intro h
    have h1 := congrArg transpose ((mem_iff_dual_mul_self).mp h)
    rw [dual, transpose_mul, transpose_mul, transpose_mul, minkowskiMatrix.eq_transpose,
      ← mul_assoc, transpose_one, transpose_transpose] at h1
    rw [mem_iff_self_mul_dual, ← h1, dual]
    noncomm_ring

lemma mem_mul (hΛ : Λ ∈ LorentzGroup d) (hΛ' : Λ' ∈ LorentzGroup d) : Λ * Λ' ∈ LorentzGroup d := by
  rw [mem_iff_dual_mul_self, dual_mul]
  trans dual Λ' * (dual Λ * Λ) * Λ'
  noncomm_ring
  rw [(mem_iff_dual_mul_self).mp hΛ]
  simp [(mem_iff_dual_mul_self).mp hΛ']

lemma one_mem : 1 ∈ LorentzGroup d := by
  rw [mem_iff_dual_mul_self]
  simp

lemma dual_mem (h : Λ ∈ LorentzGroup d) : dual Λ ∈ LorentzGroup d := by
  rw [mem_iff_dual_mul_self, dual_dual]
  exact mem_iff_self_mul_dual.mp h

end LorentzGroup

/-!

# The Lorentz group as a group

-/

@[simps mul_coe one_coe inv div]
instance lorentzGroupIsGroup : Group (LorentzGroup d) where
  mul A B := ⟨A.1 * B.1, LorentzGroup.mem_mul A.2 B.2⟩
  mul_assoc A B C := by
    apply Subtype.eq
    exact Matrix.mul_assoc A.1 B.1 C.1
  one := ⟨1, LorentzGroup.one_mem⟩
  one_mul A := by
    apply Subtype.eq
    exact Matrix.one_mul A.1
  mul_one A := by
    apply Subtype.eq
    exact Matrix.mul_one A.1
  inv A := ⟨minkowskiMetric.dual A.1, LorentzGroup.dual_mem A.2⟩
  mul_left_inv A := by
    apply Subtype.eq
    exact LorentzGroup.mem_iff_dual_mul_self.mp A.2

/-- `LorentzGroup` has the subtype topology. -/
instance : TopologicalSpace (LorentzGroup d) := instTopologicalSpaceSubtype

namespace LorentzGroup

open minkowskiMetric

variable {Λ Λ' : LorentzGroup d}

lemma coe_inv : (Λ⁻¹).1 = Λ.1⁻¹:= by
  refine (inv_eq_left_inv ?h).symm
  exact mem_iff_dual_mul_self.mp Λ.2

/-- The transpose of a matrix in the Lorentz group is an element of the Lorentz group. -/
def transpose (Λ : LorentzGroup d) : LorentzGroup d :=
  ⟨Λ.1ᵀ, mem_iff_transpose.mp Λ.2⟩

/-!

## Lorentz group as a topological group

We now show that the Lorentz group is a topological group.
We do this by showing that the natrual map from the Lorentz group to `GL (Fin 4) ℝ` is an
embedding.

-/

/-- The homomorphism of the Lorentz group into `GL (Fin 4) ℝ`. -/
def toGL : LorentzGroup d →* GL (Fin 1 ⊕ Fin d) ℝ where
  toFun A := ⟨A.1, (A⁻¹).1, mul_eq_one_comm.mpr $ mem_iff_dual_mul_self.mp A.2,
    mem_iff_dual_mul_self.mp A.2⟩
  map_one' := by
    simp
    rfl
  map_mul' x y := by
    simp only [lorentzGroupIsGroup, _root_.mul_inv_rev, coe_inv]
    ext
    rfl

lemma toGL_injective : Function.Injective (@toGL d) := by
  intro A B h
  apply Subtype.eq
  rw [@Units.ext_iff] at h
  exact h

/-- The homomorphism from the Lorentz Group into the monoid of matrices times the opposite of
  the monoid of matrices. -/
@[simps!]
def toProd : LorentzGroup d →* (Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) ×
    (Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)ᵐᵒᵖ :=
  MonoidHom.comp (Units.embedProduct _) toGL

lemma toProd_eq_transpose_η : toProd Λ = (Λ.1, MulOpposite.op $ minkowskiMetric.dual Λ.1) := rfl

lemma toProd_injective : Function.Injective (@toProd d) := by
  intro A B h
  rw [toProd_eq_transpose_η, toProd_eq_transpose_η] at h
  rw [@Prod.mk.inj_iff] at h
  apply Subtype.eq
  exact h.1

lemma toProd_continuous : Continuous (@toProd d) := by
  change Continuous (fun A => (A.1, ⟨dual A.1⟩))
  refine continuous_prod_mk.mpr (And.intro ?_ ?_)
  exact continuous_iff_le_induced.mpr fun U a => a
  refine Continuous.comp' ?_ ?_
  exact MulOpposite.continuous_op
  refine Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) continuous_const
  refine Continuous.matrix_transpose ?_
  exact continuous_iff_le_induced.mpr fun U a => a

/-- The embedding from the Lorentz Group into the monoid of matrices times the opposite of
  the monoid of matrices. -/
lemma toProd_embedding : Embedding (@toProd d) where
  inj := toProd_injective
  induced := by
    refine (inducing_iff ⇑toProd).mp ?_
    refine inducing_of_inducing_compose toProd_continuous continuous_fst ?hgf
    exact (inducing_iff (Prod.fst ∘ ⇑toProd)).mpr rfl

/-- The embedding from the Lorentz Group into `GL (Fin 4) ℝ`. -/
lemma toGL_embedding : Embedding (@toGL d).toFun where
  inj := toGL_injective
  induced := by
    refine ((fun {X} {t t'} => TopologicalSpace.ext_iff.mpr) ?_).symm
    intro s
    rw [TopologicalSpace.ext_iff.mp toProd_embedding.induced s ]
    rw [isOpen_induced_iff, isOpen_induced_iff]
    exact exists_exists_and_eq_and

instance : TopologicalGroup (LorentzGroup d) :=
Inducing.topologicalGroup toGL toGL_embedding.toInducing

section
open LorentzVector
/-!

# To a norm one Lorentz vector

-/

/-- The first column of a Lorentz matrix as a `NormOneLorentzVector`. -/
@[simps!]
def toNormOneLorentzVector (Λ : LorentzGroup d) : NormOneLorentzVector d :=
  ⟨Λ.1 *ᵥ timeVec, by rw [NormOneLorentzVector.mem_iff, Λ.2, minkowskiMetric.on_timeVec]⟩

/-!

# The time like element

-/

/-- The time like element of a Lorentz matrix. -/
@[simp]
def timeComp (Λ : LorentzGroup d) : ℝ := Λ.1 (Sum.inl 0) (Sum.inl 0)

lemma timeComp_eq_toNormOneLorentzVector : timeComp Λ = (toNormOneLorentzVector Λ).1.time := by
  simp only [time, toNormOneLorentzVector, timeVec, Fin.isValue, timeComp]
  erw [Pi.basisFun_apply, mulVec_stdBasis]

lemma timeComp_mul (Λ Λ' : LorentzGroup d) : timeComp (Λ * Λ') =
    ⟪toNormOneLorentzVector (transpose Λ), (toNormOneLorentzVector Λ').1.spaceReflection⟫ₘ := by
  simp only [timeComp, Fin.isValue, lorentzGroupIsGroup_mul_coe, mul_apply, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, toNormOneLorentzVector,
    transpose, timeVec, right_spaceReflection, time, space, PiLp.inner_apply, Function.comp_apply,
    RCLike.inner_apply, conj_trivial]
  erw [Pi.basisFun_apply, mulVec_stdBasis]
  simp

end
end LorentzGroup
