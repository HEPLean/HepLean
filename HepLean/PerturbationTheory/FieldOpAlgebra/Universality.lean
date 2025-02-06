/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldOpAlgebra.Basic
/-!

# Universality properties of FieldOpAlgebra

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-- For a field specification, `𝓕`, given an algebra `A` and a function `f : 𝓕.CrAnFieldOp → A`
  such that the lift of `f` to `FreeAlgebra.lift ℂ f : FreeAlgebra ℂ 𝓕.CrAnFieldOp → A` is
  zero on the ideal defining `𝓕.FieldOpAlgebra`, the corresponding map `𝓕.FieldOpAlgebra → A`.
-/
def universalLiftMap {A : Type} [Semiring A] [Algebra ℂ A] (f : 𝓕.CrAnFieldOp → A)
    (h1 : ∀ a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet, FreeAlgebra.lift ℂ f a = 0) :
    FieldOpAlgebra 𝓕 → A :=
  Quotient.lift (FreeAlgebra.lift ℂ f) (by
    intro a b h
    rw [equiv_iff_exists_add] at h
    obtain ⟨a, rfl, ha⟩ := h
    simp only [map_add]
    rw [h1 a ha]
    simp)

@[simp]
lemma universalLiftMap_ι {A : Type} [Semiring A] [Algebra ℂ A] (f : 𝓕.CrAnFieldOp → A)
    (h1 : ∀ a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet, FreeAlgebra.lift ℂ f a = 0) :
    universalLiftMap f h1 (ι a) = FreeAlgebra.lift ℂ f a := by rfl

/-- For a field specification, `𝓕`, given an algebra `A` and a function `f : 𝓕.CrAnFieldOp → A`
  such that the lift of `f` to `FreeAlgebra.lift ℂ f : FreeAlgebra ℂ 𝓕.CrAnFieldOp → A` is
  zero on the ideal defining `𝓕.FieldOpAlgebra`, the corresponding algebra map
  `𝓕.FieldOpAlgebra → A`.
-/
def universalLift {A : Type} [Semiring A] [Algebra ℂ A] (f : 𝓕.CrAnFieldOp → A)
    (h1 : ∀ a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet, FreeAlgebra.lift ℂ f a = 0) :
    FieldOpAlgebra 𝓕 →ₐ[ℂ] A where
  toFun := universalLiftMap f h1
  map_one' := by
    rw [show 1 = ι (𝓕 := 𝓕) 1 from rfl, universalLiftMap_ι]
    simp
  map_mul' x y := by
    obtain ⟨x, rfl⟩ := ι_surjective x
    obtain ⟨y, rfl⟩ := ι_surjective y
    simp [← map_mul]
  map_zero' := by
    simp only
    rw [show 0 = ι (𝓕 := 𝓕) 0 from rfl, universalLiftMap_ι]
    simp
  map_add' x y := by
    obtain ⟨x, rfl⟩ := ι_surjective x
    obtain ⟨y, rfl⟩ := ι_surjective y
    simp [← map_add]
  commutes' r := by
    simp only
    rw [Algebra.algebraMap_eq_smul_one r]
    rw [show r • 1 = ι (𝓕 := 𝓕) (r • 1) from rfl, universalLiftMap_ι]
    simp only [map_smul, map_one]
    exact Eq.symm (Algebra.algebraMap_eq_smul_one r)

@[simp]
lemma universalLift_ι {A : Type} [Semiring A] [Algebra ℂ A] (f : 𝓕.CrAnFieldOp → A)
    (h1 : ∀ a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet, FreeAlgebra.lift ℂ f a = 0) :
    universalLift f h1 (ι a) = FreeAlgebra.lift ℂ f a := by rfl

/--
For a field specification, `𝓕`, the algebra `𝓕.FieldOpAlgebra` satifies the following universal
property. Let `f : 𝓕.CrAnFieldOp → A` be a function and `g : 𝓕.FieldOpFreeAlgebra →ₐ[ℂ] A`
the universal lift of that function associated with the free algebra `𝓕.FieldOpFreeAlgebra`.
If `g` is zero on the ideal defining `𝓕.FieldOpAlgebra`, then there is a unique
algebra map `g' : FieldOpAlgebra 𝓕 →ₐ[ℂ] A` such that `g' ∘ ι = g`.
-/
lemma universality {A : Type} [Semiring A] [Algebra ℂ A] (f : 𝓕.CrAnFieldOp → A)
    (h1 : ∀ a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet, FreeAlgebra.lift ℂ f a = 0) :
    ∃! g : FieldOpAlgebra 𝓕 →ₐ[ℂ] A, g ∘ ι = FreeAlgebra.lift ℂ f := by
  use universalLift f h1
  simp only
  apply And.intro
  · ext a
    simp
  · intro g hg
    ext a
    obtain ⟨a, rfl⟩ := ι_surjective a
    simpa using congrFun hg a

end FieldOpAlgebra
end FieldSpecification
