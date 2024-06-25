/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.Metric
import HepLean.SpaceTime.AsSelfAdjointMatrix
/-!
# The Lorentz Group

We define the Lorentz group.

## TODO

- Show that the Lorentz is a Lie group.
- Prove that the restricted Lorentz group is equivalent to the connected component of the
identity.
- Define the continuous maps from `ℝ³` to `restrictedLorentzGroup` defining boosts.

## References

- http://home.ku.edu.tr/~amostafazadeh/phys517_518/phys517_2016f/Handouts/A_Jaffi_Lorentz_Group.pdf

-/


noncomputable section

namespace spaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-!
## Matrices which preserve `ηLin`

We start studying the properties of matrices which preserve `ηLin`.
These matrices form the Lorentz group, which we will define in the next section at `lorentzGroup`.

-/

/-- We say a matrix `Λ` preserves `ηLin` if for all `x` and `y`,
  `ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y`.  -/
def PreservesηLin (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  ∀ (x y : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ y) = ηLin x y

namespace PreservesηLin

variable  (Λ : Matrix (Fin 4) (Fin 4) ℝ)

lemma iff_norm : PreservesηLin Λ ↔
    ∀ (x : spaceTime), ηLin (Λ *ᵥ x) (Λ *ᵥ x) = ηLin x x := by
  refine Iff.intro (fun h x => h x x) (fun h x y => ?_)
  have hp := h (x + y)
  have hn := h (x - y)
  rw [mulVec_add] at hp
  rw [mulVec_sub] at hn
  simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply] at hp hn
  rw [ηLin_symm (Λ *ᵥ y) (Λ *ᵥ x), ηLin_symm y x] at hp hn
  linear_combination hp / 4 + -1 * hn / 4

lemma iff_det_selfAdjoint : PreservesηLin Λ ↔
    ∀ (x : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)),
    det ((toSelfAdjointMatrix ∘ toLin stdBasis stdBasis Λ ∘ toSelfAdjointMatrix.symm) x).1
    = det x.1 := by
  rw [iff_norm]
  apply Iff.intro
  intro h x
  have h1 := congrArg ofReal $ h (toSelfAdjointMatrix.symm x)
  simpa [← det_eq_ηLin] using h1
  intro h x
  have h1 := h (toSelfAdjointMatrix x)
  simpa [det_eq_ηLin] using h1

lemma iff_on_right : PreservesηLin Λ ↔
    ∀ (x y : spaceTime), ηLin x ((η * Λᵀ * η * Λ) *ᵥ y) = ηLin x y := by
  apply Iff.intro
  intro h x y
  have h1 := h x y
  rw [ηLin_mulVec_left, mulVec_mulVec] at h1
  exact h1
  intro h x y
  rw [ηLin_mulVec_left, mulVec_mulVec]
  exact h x y

lemma iff_matrix : PreservesηLin Λ ↔ η * Λᵀ * η * Λ = 1  := by
  rw [iff_on_right, ηLin_matrix_eq_identity_iff (η * Λᵀ * η * Λ)]
  apply Iff.intro
  · simp_all  [ηLin, implies_true, iff_true, one_mulVec]
  · exact fun a x y => Eq.symm (Real.ext_cauchy (congrArg Real.cauchy (a x y)))

lemma iff_matrix' : PreservesηLin Λ ↔ Λ * (η * Λᵀ * η) = 1  := by
  rw [iff_matrix]
  exact mul_eq_one_comm


lemma iff_transpose : PreservesηLin Λ ↔ PreservesηLin Λᵀ := by
  apply Iff.intro
  intro h
  have h1 := congrArg transpose ((iff_matrix Λ).mp h)
  rw [transpose_mul, transpose_mul, transpose_mul, η_transpose,
    ← mul_assoc, transpose_one] at h1
  rw [iff_matrix' Λ.transpose, ← h1]
  noncomm_ring
  intro h
  have h1 := congrArg transpose ((iff_matrix Λ.transpose).mp h)
  rw [transpose_mul, transpose_mul, transpose_mul, η_transpose,
    ← mul_assoc, transpose_one, transpose_transpose] at h1
  rw [iff_matrix', ← h1]
  noncomm_ring

/-- The lift of a matrix which preserves `ηLin` to an invertible matrix. -/
def liftGL {Λ : Matrix (Fin 4) (Fin 4) ℝ} (h : PreservesηLin Λ) : GL (Fin 4) ℝ :=
  ⟨Λ, η * Λᵀ * η , (iff_matrix' Λ).mp h , (iff_matrix Λ).mp h⟩

lemma mul {Λ Λ' : Matrix (Fin 4) (Fin 4) ℝ} (h : PreservesηLin Λ) (h' : PreservesηLin Λ') :
    PreservesηLin (Λ * Λ') := by
  intro x y
  rw [← mulVec_mulVec, ← mulVec_mulVec, h, h']

lemma one : PreservesηLin 1 := by
  intro x y
  simp

lemma η : PreservesηLin η := by
  simp [iff_matrix, η_transpose, η_sq]

end PreservesηLin

/-!
## The Lorentz group

We define the Lorentz group as the set of matrices which preserve `ηLin`.
We show that the Lorentz group is indeed a group.

-/

/-- The Lorentz group is the subset of matrices which preserve ηLin. -/
def lorentzGroup : Type := {Λ : Matrix (Fin 4) (Fin 4) ℝ // PreservesηLin Λ}

@[simps mul_coe one_coe inv div]
instance lorentzGroupIsGroup : Group lorentzGroup where
  mul A B := ⟨A.1 * B.1, PreservesηLin.mul A.2 B.2⟩
  mul_assoc A B C := by
    apply Subtype.eq
    exact Matrix.mul_assoc A.1 B.1 C.1
  one := ⟨1, PreservesηLin.one⟩
  one_mul A := by
    apply Subtype.eq
    exact Matrix.one_mul A.1
  mul_one A := by
    apply Subtype.eq
    exact Matrix.mul_one A.1
  inv A := ⟨η * A.1ᵀ * η , PreservesηLin.mul (PreservesηLin.mul PreservesηLin.η
    ((PreservesηLin.iff_transpose A.1).mp A.2)) PreservesηLin.η⟩
  mul_left_inv A := by
    apply Subtype.eq
    exact (PreservesηLin.iff_matrix A.1).mp A.2

/-- Notation for the Lorentz group. -/
scoped[spaceTime] notation (name := lorentzGroup_notation) "𝓛" => lorentzGroup


/-- `lorentzGroup` has the subtype topology. -/
instance : TopologicalSpace lorentzGroup := instTopologicalSpaceSubtype

namespace lorentzGroup

lemma coe_inv (A : 𝓛) : (A⁻¹).1 = A.1⁻¹:= by
  refine (inv_eq_left_inv ?h).symm
  exact (PreservesηLin.iff_matrix A.1).mp A.2

/-- The transpose of an matrix in the Lorentz group is an element of the Lorentz group. -/
def transpose (Λ : lorentzGroup) : lorentzGroup := ⟨Λ.1ᵀ, (PreservesηLin.iff_transpose Λ.1).mp Λ.2⟩

/-!

## Lorentz group as a topological group

We now show that the Lorentz group is a topological group.
We do this by showing that the natrual map from the Lorentz group to `GL (Fin 4) ℝ` is an
embedding.

-/

/-- The homomorphism of the Lorentz group into `GL (Fin 4) ℝ`. -/
def toGL : 𝓛 →* GL (Fin 4) ℝ where
  toFun A := ⟨A.1, (A⁻¹).1, mul_eq_one_comm.mpr $ (PreservesηLin.iff_matrix A.1).mp A.2,
    (PreservesηLin.iff_matrix A.1).mp A.2⟩
  map_one' := by
    simp
    rfl
  map_mul' x y  := by
    simp only [lorentzGroupIsGroup, _root_.mul_inv_rev, coe_inv]
    ext
    rfl

lemma toGL_injective : Function.Injective toGL := by
  intro A B h
  apply Subtype.eq
  rw [@Units.ext_iff] at h
  exact h

/-- The homomorphism from the Lorentz Group into the monoid of matrices times the opposite of
  the monoid of matrices. -/
@[simps!]
def toProd : 𝓛 →* (Matrix (Fin 4) (Fin 4) ℝ) × (Matrix (Fin 4) (Fin 4) ℝ)ᵐᵒᵖ :=
  MonoidHom.comp (Units.embedProduct _) toGL

lemma toProd_eq_transpose_η  : toProd A = (A.1, ⟨η * A.1ᵀ * η⟩) := rfl

lemma toProd_injective : Function.Injective toProd := by
  intro A B h
  rw [toProd_eq_transpose_η, toProd_eq_transpose_η] at h
  rw [@Prod.mk.inj_iff] at h
  apply Subtype.eq
  exact h.1

lemma toProd_continuous : Continuous toProd := by
  change Continuous (fun A => (A.1, ⟨η * A.1ᵀ * η⟩))
  refine continuous_prod_mk.mpr (And.intro ?_ ?_)
  exact continuous_iff_le_induced.mpr fun U a => a
  refine Continuous.comp' ?_ ?_
  exact MulOpposite.continuous_op
  refine Continuous.matrix_mul (Continuous.matrix_mul continuous_const ?_) continuous_const
  refine Continuous.matrix_transpose ?_
  exact continuous_iff_le_induced.mpr fun U a => a

/-- The embedding from the Lorentz Group into the monoid of matrices times the opposite of
  the monoid of matrices. -/
lemma toProd_embedding : Embedding toProd where
  inj := toProd_injective
  induced := by
    refine (inducing_iff ⇑toProd).mp ?_
    refine inducing_of_inducing_compose toProd_continuous continuous_fst ?hgf
    exact (inducing_iff (Prod.fst ∘ ⇑toProd)).mpr rfl

/-- The embedding from the Lorentz Group into `GL (Fin 4) ℝ`. -/
lemma toGL_embedding : Embedding toGL.toFun where
  inj := toGL_injective
  induced := by
    refine ((fun {X} {t t'} => TopologicalSpace.ext_iff.mpr) ?_).symm
    intro s
    rw [TopologicalSpace.ext_iff.mp toProd_embedding.induced s ]
    rw [isOpen_induced_iff, isOpen_induced_iff]
    exact exists_exists_and_eq_and


instance : TopologicalGroup 𝓛 := Inducing.topologicalGroup toGL toGL_embedding.toInducing



end lorentzGroup


end spaceTime
