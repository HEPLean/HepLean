/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.MinkowskiMatrix
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

open minkowskiMatrix in
/-- The Lorentz group is the subset of matrices for which
  `Λ * dual Λ = 1`. -/
def LorentzGroup (d : ℕ) : Set (Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :=
    {Λ : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ | Λ * dual Λ = 1}

namespace LorentzGroup
/-- Notation for the Lorentz group. -/
scoped[LorentzGroup] notation (name := lorentzGroup_notation) "𝓛" => LorentzGroup

open minkowskiMatrix
variable {Λ Λ' : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}

/-!

# Membership conditions

-/

lemma mem_iff_self_mul_dual : Λ ∈ LorentzGroup d ↔ Λ * dual Λ = 1 := by
  rfl

lemma mem_iff_dual_mul_self : Λ ∈ LorentzGroup d ↔ dual Λ * Λ = 1 := by
  rw [mem_iff_self_mul_dual]
  exact mul_eq_one_comm

lemma mem_iff_transpose : Λ ∈ LorentzGroup d ↔ Λᵀ ∈ LorentzGroup d := by
  refine Iff.intro (fun h ↦ ?_) (fun h ↦ ?_)
  · have h1 := congrArg transpose ((mem_iff_dual_mul_self).mp h)
    rw [dual, transpose_mul, transpose_mul, transpose_mul, minkowskiMatrix.eq_transpose,
      ← mul_assoc, transpose_one] at h1
    rw [mem_iff_self_mul_dual, ← h1, dual]
    noncomm_ring
  · have h1 := congrArg transpose ((mem_iff_dual_mul_self).mp h)
    rw [dual, transpose_mul, transpose_mul, transpose_mul, minkowskiMatrix.eq_transpose,
      ← mul_assoc, transpose_one, transpose_transpose] at h1
    rw [mem_iff_self_mul_dual, ← h1, dual]
    noncomm_ring

lemma mem_mul (hΛ : Λ ∈ LorentzGroup d) (hΛ' : Λ' ∈ LorentzGroup d) : Λ * Λ' ∈ LorentzGroup d := by
  rw [mem_iff_dual_mul_self, dual_mul]
  trans dual Λ' * (dual Λ * Λ) * Λ'
  · noncomm_ring
  · rw [(mem_iff_dual_mul_self).mp hΛ]
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

/-- The instance of a group on `LorentzGroup d`. -/
@[simps! mul_coe one_coe inv div]
instance lorentzGroupIsGroup : Group (LorentzGroup d) where
  mul A B := ⟨A.1 * B.1, LorentzGroup.mem_mul A.2 B.2⟩
  mul_assoc A B C := Subtype.eq (Matrix.mul_assoc A.1 B.1 C.1)
  one := ⟨1, LorentzGroup.one_mem⟩
  one_mul A := Subtype.eq (Matrix.one_mul A.1)
  mul_one A := Subtype.eq (Matrix.mul_one A.1)
  inv A := ⟨minkowskiMatrix.dual A.1, LorentzGroup.dual_mem A.2⟩
  inv_mul_cancel A := Subtype.eq (LorentzGroup.mem_iff_dual_mul_self.mp A.2)

/-- `LorentzGroup` has the subtype topology. -/
instance : TopologicalSpace (LorentzGroup d) := instTopologicalSpaceSubtype

namespace LorentzGroup

open minkowskiMatrix

variable {Λ Λ' : LorentzGroup d}

lemma coe_inv : (Λ⁻¹).1 = Λ.1⁻¹:= (inv_eq_left_inv (mem_iff_dual_mul_self.mp Λ.2)).symm

/-- The underlying matrix of a Lorentz transformation is invertible. -/
instance (M : LorentzGroup d) : Invertible M.1 where
  invOf := M⁻¹
  invOf_mul_self := by
    rw [← coe_inv]
    exact (mem_iff_dual_mul_self.mp M.2)
  mul_invOf_self := by
    rw [← coe_inv]
    exact (mem_iff_self_mul_dual.mp M.2)

lemma subtype_inv_mul : (Subtype.val Λ)⁻¹ * (Subtype.val Λ) = 1 := by
  trans Subtype.val (Λ⁻¹ * Λ)
  · rw [← coe_inv]
    rfl
  · rw [inv_mul_cancel Λ]
    rfl

lemma subtype_mul_inv : (Subtype.val Λ) * (Subtype.val Λ)⁻¹ = 1 := by
  trans Subtype.val (Λ * Λ⁻¹)
  · rw [← coe_inv]
    rfl
  · rw [mul_inv_cancel Λ]
    rfl

@[simp]
lemma mul_minkowskiMatrix_mul_transpose :
    (Subtype.val Λ) * minkowskiMatrix * (Subtype.val Λ).transpose = minkowskiMatrix := by
  have h2 := Λ.prop
  rw [LorentzGroup.mem_iff_self_mul_dual] at h2
  simp only [dual] at h2
  refine (right_inv_eq_left_inv minkowskiMatrix.sq ?_).symm
  rw [← h2]
  noncomm_ring

@[simp]
lemma transpose_mul_minkowskiMatrix_mul_self :
    (Subtype.val Λ).transpose * minkowskiMatrix * (Subtype.val Λ) = minkowskiMatrix := by
  have h2 := Λ.prop
  rw [LorentzGroup.mem_iff_dual_mul_self] at h2
  simp only [dual] at h2
  refine right_inv_eq_left_inv ?_ minkowskiMatrix.sq
  rw [← h2]
  noncomm_ring

/-- The transpose of a matrix in the Lorentz group is an element of the Lorentz group. -/
def transpose (Λ : LorentzGroup d) : LorentzGroup d :=
  ⟨Λ.1ᵀ, mem_iff_transpose.mp Λ.2⟩

@[simp]
lemma transpose_one : @transpose d 1 = 1 := Subtype.eq Matrix.transpose_one

@[simp]
lemma transpose_mul : transpose (Λ * Λ') = transpose Λ' * transpose Λ :=
  Subtype.eq (Matrix.transpose_mul Λ.1 Λ'.1)

lemma transpose_val : (transpose Λ).1 = Λ.1ᵀ := rfl

lemma transpose_inv : (transpose Λ)⁻¹ = transpose Λ⁻¹ := by
  refine Subtype.eq ?_
  rw [transpose_val, coe_inv, transpose_val, coe_inv, Matrix.transpose_nonsing_inv]

lemma comm_minkowskiMatrix : Λ.1 * minkowskiMatrix = minkowskiMatrix * (transpose Λ⁻¹).1 := by
  conv_rhs => rw [← @mul_minkowskiMatrix_mul_transpose d Λ]
  rw [← transpose_inv, coe_inv, transpose_val]
  rw [mul_assoc]
  have h1 : ((Λ.1)ᵀ * (Λ.1)ᵀ⁻¹) = 1 := by
    rw [← transpose_val]
    simp only [subtype_mul_inv]
  rw [h1]
  simp

lemma minkowskiMatrix_comm : minkowskiMatrix * Λ.1 = (transpose Λ⁻¹).1 * minkowskiMatrix := by
  conv_rhs => rw [← @transpose_mul_minkowskiMatrix_mul_self d Λ]
  rw [← transpose_inv, coe_inv, transpose_val]
  rw [← mul_assoc, ← mul_assoc]
  have h1 : ((Λ.1)ᵀ⁻¹ * (Λ.1)ᵀ) = 1 := by
    rw [← transpose_val]
    simp only [subtype_inv_mul]
  rw [h1]
  simp

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
  map_one' :=
    (GeneralLinearGroup.ext_iff _ 1).mpr fun _ => congrFun rfl
  map_mul' _ _ :=
    (GeneralLinearGroup.ext_iff _ _).mpr fun _ => congrFun rfl

lemma toGL_injective : Function.Injective (@toGL d) := by
  refine fun A B h => Subtype.eq ?_
  rw [@Units.ext_iff] at h
  exact h

/-- The homomorphism from the Lorentz Group into the monoid of matrices times the opposite of
  the monoid of matrices. -/
@[simps!]
def toProd : LorentzGroup d →* (Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) ×
    (Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)ᵐᵒᵖ :=
  MonoidHom.comp (Units.embedProduct _) toGL

lemma toProd_eq_transpose_η : toProd Λ = (Λ.1, MulOpposite.op $ minkowskiMatrix.dual Λ.1) := rfl

lemma toProd_injective : Function.Injective (@toProd d) := by
  intro A B h
  rw [toProd_eq_transpose_η, toProd_eq_transpose_η] at h
  rw [@Prod.mk.inj_iff] at h
  exact Subtype.eq h.1

lemma toProd_continuous : Continuous (@toProd d) := by
  refine continuous_prod_mk.mpr ⟨continuous_iff_le_induced.mpr fun U a ↦ a,
    MulOpposite.continuous_op.comp' ((continuous_const.matrix_mul (continuous_iff_le_induced.mpr
      fun U a => a).matrix_transpose).matrix_mul continuous_const)⟩

open Topology

/-- The embedding from the Lorentz Group into the monoid of matrices times the opposite of
  the monoid of matrices. -/
lemma toProd_embedding : IsEmbedding (@toProd d) where
  injective := toProd_injective
  eq_induced :=
    (isInducing_iff ⇑toProd).mp (IsInducing.of_comp toProd_continuous continuous_fst
      ((isInducing_iff (Prod.fst ∘ ⇑toProd)).mpr rfl))

/-- The embedding from the Lorentz Group into `GL (Fin 4) ℝ`. -/
lemma toGL_embedding : IsEmbedding (@toGL d).toFun where
  injective := toGL_injective
  eq_induced := by
    refine ((fun {X} {t t'} => TopologicalSpace.ext_iff.mpr) fun _ ↦ ?_).symm
    rw [TopologicalSpace.ext_iff.mp toProd_embedding.eq_induced _, isOpen_induced_iff,
      isOpen_induced_iff]
    exact exists_exists_and_eq_and

/-- The embedding of the Lorentz group into `GL(n, ℝ)` gives `LorentzGroup d` an instance
  of a topological group. -/
instance : TopologicalGroup (LorentzGroup d) :=
  IsInducing.topologicalGroup toGL toGL_embedding.toIsInducing

/-!

## To Complex matrices

-/

/-- The monoid homomorphisms taking the lorentz group to complex matrices. -/
def toComplex : LorentzGroup d →* Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℂ where
  toFun Λ := Λ.1.map ofRealHom
  map_one' := by
    ext i j
    simp only [lorentzGroupIsGroup_one_coe, map_apply, ofRealHom_eq_coe]
    simp only [Matrix.one_apply, ofReal_one, ofReal_zero]
    split_ifs
    · rfl
    · rfl
  map_mul' Λ Λ' := by
    ext i j
    simp only [lorentzGroupIsGroup_mul_coe, map_apply, ofRealHom_eq_coe]
    simp only [← Matrix.map_mul, RingHom.map_matrix_mul]
    rfl

/-- The image of a Lorentz transformation under `toComplex` is invertible. -/
instance (M : LorentzGroup d) : Invertible (toComplex M) where
  invOf := toComplex M⁻¹
  invOf_mul_self := by
    rw [← toComplex.map_mul, Group.inv_mul_cancel]
    simp
  mul_invOf_self := by
    rw [← toComplex.map_mul]
    rw [@mul_inv_cancel]
    simp

lemma toComplex_inv (Λ : LorentzGroup d) : (toComplex Λ)⁻¹ = toComplex Λ⁻¹ := by
  refine inv_eq_right_inv ?h
  rw [← toComplex.map_mul, mul_inv_cancel]
  simp

@[simp]
lemma toComplex_mul_minkowskiMatrix_mul_transpose (Λ : LorentzGroup d) :
    toComplex Λ * minkowskiMatrix.map ofRealHom * (toComplex Λ)ᵀ =
    minkowskiMatrix.map ofRealHom := by
  simp only [toComplex, MonoidHom.coe_mk, OneHom.coe_mk]
  have h1 : ((Λ.1).map ⇑ofRealHom)ᵀ = (Λ.1ᵀ).map ofRealHom := rfl
  rw [h1]
  trans (Λ.1 * minkowskiMatrix * Λ.1ᵀ).map ofRealHom
  · simp only [Matrix.map_mul]
  simp only [mul_minkowskiMatrix_mul_transpose]

@[simp]
lemma toComplex_transpose_mul_minkowskiMatrix_mul_self (Λ : LorentzGroup d) :
    (toComplex Λ)ᵀ * minkowskiMatrix.map ofRealHom * toComplex Λ =
    minkowskiMatrix.map ofRealHom := by
  simp only [toComplex, MonoidHom.coe_mk, OneHom.coe_mk]
  have h1 : ((Λ.1).map ofRealHom)ᵀ = (Λ.1ᵀ).map ofRealHom := rfl
  rw [h1]
  trans (Λ.1ᵀ * minkowskiMatrix * Λ.1).map ofRealHom
  · simp only [Matrix.map_mul]
  simp only [transpose_mul_minkowskiMatrix_mul_self]

lemma toComplex_mulVec_ofReal (v : Fin 1 ⊕ Fin d → ℝ) (Λ : LorentzGroup d) :
    toComplex Λ *ᵥ (ofRealHom ∘ v) = ofRealHom ∘ (Λ *ᵥ v) := by
  simp only [toComplex, MonoidHom.coe_mk, OneHom.coe_mk]
  funext i
  rw [← RingHom.map_mulVec]
  rfl

/-- The parity transformation. -/
def parity : LorentzGroup d := ⟨minkowskiMatrix, by
  rw [mem_iff_dual_mul_self]
  simp only [dual_eta, minkowskiMatrix.sq]⟩

end LorentzGroup
