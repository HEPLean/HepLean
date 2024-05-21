/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Data.Complex.Exponential
import Mathlib.Geometry.Manifold.VectorBundle.Basic
/-!
# the 3d special orthogonal group



-/

namespace GroupTheory
open Matrix

def SO3 : Type := {A : Matrix (Fin 3) (Fin 3) ℝ // A.det = 1 ∧ A * Aᵀ = 1}

instance SO3Group : Group SO3 where
  mul A B := ⟨A.1 * B.1,
    by
      simp only [det_mul, A.2.1, B.2.1, mul_one],
    by
      simp [A.2.2, B.2.2, ← Matrix.mul_assoc, Matrix.mul_assoc]⟩
  mul_assoc A B C := by
    apply Subtype.eq
    exact Matrix.mul_assoc A.1 B.1 C.1
  one := ⟨1, by simp, by simp⟩
  one_mul A := by
    apply Subtype.eq
    exact Matrix.one_mul A.1
  mul_one A := by
    apply Subtype.eq
    exact Matrix.mul_one A.1
  inv A := ⟨A.1ᵀ, by simp [A.2], by simp [mul_eq_one_comm.mpr A.2.2]⟩
  mul_left_inv A := by
    apply Subtype.eq
    exact mul_eq_one_comm.mpr A.2.2

scoped[GroupTheory] notation (name := SO3_notation) "SO(3)" => SO3

/-- SO3 has the subtype topology. -/
instance : TopologicalSpace SO3 := instTopologicalSpaceSubtype

namespace SO3

@[simp]
lemma coe_inv (A : SO3) : (A⁻¹).1 = A.1⁻¹:= by
  refine (inv_eq_left_inv ?h).symm
  exact mul_eq_one_comm.mpr A.2.2

@[simps!]
def toGL : SO3 →* GL (Fin 3) ℝ where
  toFun A := ⟨A.1, (A⁻¹).1, A.2.2, mul_eq_one_comm.mpr A.2.2⟩
  map_one' := by
    simp
    rfl
  map_mul' x y  := by
    simp
    ext
    rfl

lemma subtype_val_eq_toGL : (Subtype.val : SO3 → Matrix (Fin 3) (Fin 3) ℝ) =
    Units.val ∘ toGL.toFun := by
  ext A
  rfl

lemma toGL_injective : Function.Injective toGL := by
  intro A B h
  apply Subtype.eq
  rw [@Units.ext_iff] at h
  simpa using h

example : TopologicalSpace (GL (Fin 3) ℝ) := by
  exact Units.instTopologicalSpaceUnits

@[simps!]
def toProd : SO(3) →* (Matrix (Fin 3) (Fin 3) ℝ) × (Matrix (Fin 3) (Fin 3) ℝ)ᵐᵒᵖ :=
  MonoidHom.comp (Units.embedProduct _) toGL

lemma toProd_eq_transpose  : toProd A = (A.1, ⟨A.1ᵀ⟩) := by
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
  apply Subtype.eq
  exact h.1

lemma toProd_continuous : Continuous toProd := by
  change Continuous (fun A => (A.1, ⟨A.1ᵀ⟩))
  refine continuous_prod_mk.mpr (And.intro ?_ ?_)
  exact continuous_iff_le_induced.mpr fun U a => a
  refine Continuous.comp' ?_ ?_
  exact MulOpposite.continuous_op
  refine Continuous.matrix_transpose ?_
  exact continuous_iff_le_induced.mpr fun U a => a


def embeddingProd : Embedding toProd where
  inj := toProd_injective
  induced := by
    refine (inducing_iff ⇑toProd).mp ?_
    refine inducing_of_inducing_compose toProd_continuous continuous_fst ?hgf
    exact (inducing_iff (Prod.fst ∘ ⇑toProd)).mpr rfl


def embeddingGL : Embedding toGL.toFun where
  inj := toGL_injective
  induced := by
    refine ((fun {X} {t t'} => TopologicalSpace.ext_iff.mpr) ?_).symm
    intro s
    rw [TopologicalSpace.ext_iff.mp embeddingProd.induced s ]
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
  Inducing.topologicalGroup toGL embeddingGL.toInducing

lemma det_minus_id (A : SO(3)) : det (A.1 - 1) = 0 := by
  have h1 : det (A.1 - 1) = - det (A.1 - 1)  :=
    calc
      det (A.1 - 1) = det (A.1 - A.1 *  A.1ᵀ)  := by simp [A.2.2]
      _ = det A.1 * det (1 -  A.1ᵀ) :=  by rw [← det_mul, mul_sub, mul_one]
      _ = det (1 - A.1ᵀ):= by simp [A.2.1]
      _ = det (1 - A.1ᵀ)ᵀ := by rw [det_transpose]
      _ = det (1 - A.1) := by simp
      _ = det (- (A.1 - 1)) := by simp
      _ = (- 1) ^ 3  * det (A.1 - 1) := by simp only [det_neg, Fintype.card_fin, neg_mul, one_mul]
      _ = -  det (A.1 - 1)  := by simp [pow_three]
  simpa using h1



end SO3


end GroupTheory
