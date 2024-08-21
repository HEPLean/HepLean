/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Complex.Exponential
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# The group SO(3)

-/

namespace GroupTheory
open Matrix

/-- The group of `3×3` real matrices with determinant 1 and `A * Aᵀ = 1`. -/
def SO3 : Type := {A : Matrix (Fin 3) (Fin 3) ℝ // A.det = 1 ∧ A * Aᵀ = 1}

@[simps mul_coe one_coe inv div]
instance SO3Group : Group SO3 where
  mul A B := ⟨A.1 * B.1,
    by
      simp only [det_mul, A.2.1, B.2.1, mul_one],
    by
      simp [A.2.2, B.2.2, ← Matrix.mul_assoc, Matrix.mul_assoc]⟩
  mul_assoc A B C := Subtype.eq (Matrix.mul_assoc A.1 B.1 C.1)
  one := ⟨1, det_one, by rw [transpose_one, mul_one]⟩
  one_mul A := Subtype.eq (Matrix.one_mul A.1)
  mul_one A := Subtype.eq (Matrix.mul_one A.1)
  inv A := ⟨A.1ᵀ, by simp [A.2], by simp [mul_eq_one_comm.mpr A.2.2]⟩
  mul_left_inv A := Subtype.eq (mul_eq_one_comm.mpr A.2.2)

/-- Notation for the group `SO3`. -/
scoped[GroupTheory] notation (name := SO3_notation) "SO(3)" => SO3

/-- SO3 has the subtype topology. -/
instance : TopologicalSpace SO3 := instTopologicalSpaceSubtype

namespace SO3

lemma coe_inv (A : SO3) : (A⁻¹).1 = A.1⁻¹:=
  (inv_eq_left_inv (mul_eq_one_comm.mpr A.2.2)).symm

/-- The inclusion of `SO(3)` into `GL (Fin 3) ℝ`. -/
def toGL : SO(3) →* GL (Fin 3) ℝ where
  toFun A := ⟨A.1, (A⁻¹).1, A.2.2, mul_eq_one_comm.mpr A.2.2⟩
  map_one' := by
    simp
    rfl
  map_mul' x y := by
    simp only [_root_.mul_inv_rev, coe_inv]
    ext
    rfl

lemma subtype_val_eq_toGL : (Subtype.val : SO3 → Matrix (Fin 3) (Fin 3) ℝ) =
    Units.val ∘ toGL.toFun :=
  rfl

lemma toGL_injective : Function.Injective toGL := by
  refine fun A B h ↦ Subtype.eq ?_
  rw [@Units.ext_iff] at h
  simpa using h

/-- The inclusion of `SO(3)` into the monoid of matrices times the opposite of
  the monoid of matrices. -/
@[simps!]
def toProd : SO(3) →* (Matrix (Fin 3) (Fin 3) ℝ) × (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ :=
  MonoidHom.comp (Units.embedProduct _) toGL

lemma toProd_eq_transpose : toProd A = (A.1, ⟨A.1ᵀ⟩) := by
  simp only [toProd, Units.embedProduct, coe_units_inv, MulOpposite.op_inv, toGL, coe_inv,
    MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply, Prod.mk.injEq,
    true_and]
  refine MulOpposite.unop_inj.mp ?_
  simp only [MulOpposite.unop_inv, MulOpposite.unop_op]
  rw [← coe_inv]
  rfl

lemma toProd_injective : Function.Injective toProd := by
  intro A B h
  rw [toProd_eq_transpose, toProd_eq_transpose] at h
  rw [@Prod.mk.inj_iff] at h
  exact Subtype.eq h.1

lemma toProd_continuous : Continuous toProd :=
  continuous_prod_mk.mpr ⟨continuous_iff_le_induced.mpr fun _ a ↦ a,
    Continuous.comp' (MulOpposite.continuous_op)
      (Continuous.matrix_transpose (continuous_iff_le_induced.mpr fun _ a ↦ a))⟩

/-- The embedding of `SO(3)` into the monoid of matrices times the opposite of
  the monoid of matrices. -/
lemma toProd_embedding : Embedding toProd where
  inj := toProd_injective
  induced := (inducing_iff ⇑toProd).mp (inducing_of_inducing_compose toProd_continuous
    continuous_fst ((inducing_iff (Prod.fst ∘ ⇑toProd)).mpr rfl))

/-- The embedding of `SO(3)` into `GL (Fin 3) ℝ`. -/
lemma toGL_embedding : Embedding toGL.toFun where
  inj := toGL_injective
  induced := by
    refine ((fun {X} {t t'} => TopologicalSpace.ext_iff.mpr) ?_).symm
    intro s
    rw [TopologicalSpace.ext_iff.mp toProd_embedding.induced s]
    rw [isOpen_induced_iff, isOpen_induced_iff]
    apply Iff.intro ?_ ?_
    · intro h
      obtain ⟨U, hU1, hU2⟩ := h
      rw [isOpen_induced_iff] at hU1
      obtain ⟨V, hV1, hV2⟩ := hU1
      use V
      simp [hV1]
      rw [← hU2, ← hV2]
      rfl
    · intro h
      obtain ⟨U, hU1, hU2⟩ := h
      let t := (Units.embedProduct _) ⁻¹' U
      use t
      apply And.intro (isOpen_induced hU1)
      exact hU2

instance : TopologicalGroup SO(3) :=
  Inducing.topologicalGroup toGL toGL_embedding.toInducing

lemma det_minus_id (A : SO(3)) : det (A.1 - 1) = 0 := by
  have h1 : det (A.1 - 1) = - det (A.1 - 1) :=
    calc
      det (A.1 - 1) = det (A.1 - A.1 * A.1ᵀ) := by simp [A.2.2]
      _ = det A.1 * det (1 - A.1ᵀ) := by rw [← det_mul, mul_sub, mul_one]
      _ = det (1 - A.1ᵀ) := by simp [A.2.1]
      _ = det (1 - A.1ᵀ)ᵀ := by rw [det_transpose]
      _ = det (1 - A.1) := by simp
      _ = det (- (A.1 - 1)) := by simp
      _ = (- 1) ^ 3 * det (A.1 - 1) := by simp only [det_neg, Fintype.card_fin, neg_mul, one_mul]
      _ = - det (A.1 - 1) := by simp [pow_three]
  simpa using h1

@[simp]
lemma det_id_minus (A : SO(3)) : det (1 - A.1) = 0 := by
  have h1 : det (1 - A.1) = - det (A.1 - 1) := by
    calc
      det (1 - A.1) = det (- (A.1 - 1)) := by simp
      _ = (- 1) ^ 3 * det (A.1 - 1) := by simp only [det_neg, Fintype.card_fin, neg_mul, one_mul]
      _ = - det (A.1 - 1) := by simp [pow_three]
  rw [h1, det_minus_id]
  simp only [neg_zero]

@[simp]
lemma one_in_spectrum (A : SO(3)) : 1 ∈ spectrum ℝ (A.1) := by
  rw [spectrum.mem_iff]
  simp only [_root_.map_one]
  rw [Matrix.isUnit_iff_isUnit_det]
  simp

noncomputable section action
open Module

/-- The endomorphism of `EuclideanSpace ℝ (Fin 3)` associated to a element of `SO(3)`. -/
@[simps!]
def toEnd (A : SO(3)) : End ℝ (EuclideanSpace ℝ (Fin 3)) :=
  Matrix.toLin (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis A.1

lemma one_is_eigenvalue (A : SO(3)) : A.toEnd.HasEigenvalue 1 := by
  rw [End.hasEigenvalue_iff_mem_spectrum]
  erw [AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis) A.1]
  exact one_in_spectrum A

lemma exists_stationary_vec (A : SO(3)) :
    ∃ (v : EuclideanSpace ℝ (Fin 3)),
    Orthonormal ℝ (({0} : Set (Fin 3)).restrict (fun _ => v))
    ∧ A.toEnd v = v := by
  obtain ⟨v, hv⟩ := End.HasEigenvalue.exists_hasEigenvector $ one_is_eigenvalue A
  have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv.2
  use (1/‖v‖) • v
  apply And.intro
  · rw [@orthonormal_iff_ite]
    intro v1 v2
    have hv1 := v1.2
    have hv2 := v2.2
    simp_all only [one_div, Set.mem_singleton_iff]
    have hveq : v1 = v2 := by
      rw [@Subtype.ext_iff]
      simp_all only
    subst hveq
    simp only [Set.restrict_apply, PiLp.smul_apply, smul_eq_mul,
      _root_.map_mul, map_inv₀, conj_trivial, ↓reduceIte]
    rw [inner_smul_right, inner_smul_left, real_inner_self_eq_norm_sq v]
    field_simp
    ring
  · rw [_root_.map_smul, End.mem_eigenspace_iff.mp hv.1]
    simp

lemma exists_basis_preserved (A : SO(3)) :
    ∃ (b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))), A.toEnd (b 0) = b 0 := by
  obtain ⟨v, hv⟩ := exists_stationary_vec A
  have h3 : FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = Fintype.card (Fin 3) := by
    simp_all only [toEnd_apply, finrank_euclideanSpace, Fintype.card_fin]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq h3 hv.1
  simp at hb
  use b
  rw [hb, hv.2]

end action
end SO3

end GroupTheory
