/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.SuperCommute
/-!

# The operator algebras

-/

namespace FieldSpecification
variable (𝓕 : FieldSpecification)
open CrAnAlgebra

/--
A proto-operator algebra for a field specification `𝓕`
is a generalization of the operator algebra of a field theory with field specification `𝓕`.
It is an algebra `A` with a map `crAnF` from the creation and annihilation free algebra
satisfying a number of conditions with respect to super commutators.
The true operator algebra of a field theory with field specification `𝓕`is an
example of a proto-operator algebra. -/
structure ProtoOperatorAlgebra where
  /-- The algebra representing the operator algebra. -/
  A : Type
  /-- The instance of the type `A` as a semi-ring. -/
  [A_semiRing : Semiring A]
  /-- The instance of the type `A` as an algebra. -/
  [A_algebra : Algebra ℂ A]
  /-- An algebra map from the creation and annihilation free algebra to the
    algebra A. -/
  crAnF : 𝓕.CrAnAlgebra →ₐ[ℂ] A
  superCommuteF_crAn_center : ∀ (φ ψ : 𝓕.CrAnStates),
    crAnF [ofCrAnState φ, ofCrAnState ψ]ₛca ∈ Subalgebra.center ℂ A
  superCommuteF_create_create : ∀ (φc φc' : 𝓕.CrAnStates)
    (_ : 𝓕 |>ᶜ φc = .create) (_ : 𝓕 |>ᶜ φc' = .create),
    crAnF [ofCrAnState φc, ofCrAnState φc']ₛca = 0
  superCommuteF_annihilate_annihilate : ∀ (φa φa' : 𝓕.CrAnStates)
    (_ : 𝓕 |>ᶜ φa = .annihilate) (_ : 𝓕 |>ᶜ φa' = .annihilate),
    crAnF [ofCrAnState φa, ofCrAnState φa']ₛca = 0
  superCommuteF_different_statistics : ∀ (φ φ' : 𝓕.CrAnStates) (_ : ¬ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φ')),
    crAnF [ofCrAnState φ, ofCrAnState φ']ₛca = 0

namespace ProtoOperatorAlgebra
open FieldStatistic
variable {𝓕 : FieldSpecification} (𝓞 : 𝓕.ProtoOperatorAlgebra)

/-- The algebra `𝓞.A` carries the instance of a semi-ring induced via `A_seimRing`. -/
instance : Semiring 𝓞.A := 𝓞.A_semiRing

/-- The algebra `𝓞.A` carries the instance of aan algebra over `ℂ` induced via `A_algebra`. -/
instance : Algebra ℂ 𝓞.A := 𝓞.A_algebra

lemma crAnF_superCommuteF_ofCrAnState_ofState_mem_center (φ : 𝓕.CrAnStates) (ψ : 𝓕.States) :
    𝓞.crAnF [ofCrAnState φ, ofState ψ]ₛca ∈ Subalgebra.center ℂ 𝓞.A := by
  rw [ofState, map_sum, map_sum]
  refine Subalgebra.sum_mem (Subalgebra.center ℂ 𝓞.A) ?h
  intro x _
  exact 𝓞.superCommuteF_crAn_center φ ⟨ψ, x⟩

lemma crAnF_superCommuteF_anPart_ofState_mem_center (φ ψ : 𝓕.States) :
    𝓞.crAnF [anPart φ, ofState ψ]ₛca ∈ Subalgebra.center ℂ 𝓞.A := by
  match φ with
  | States.inAsymp _ =>
    simp only [anPart_negAsymp, map_zero, LinearMap.zero_apply]
    exact Subalgebra.zero_mem (Subalgebra.center ℂ 𝓞.A)
  | States.position φ =>
    simp only [anPart_position]
    exact 𝓞.crAnF_superCommuteF_ofCrAnState_ofState_mem_center _ _
  | States.outAsymp _ =>
    simp only [anPart_posAsymp]
    exact 𝓞.crAnF_superCommuteF_ofCrAnState_ofState_mem_center _ _

lemma crAnF_superCommuteF_ofCrAnState_ofState_diff_grade_zero (φ : 𝓕.CrAnStates) (ψ : 𝓕.States)
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) :
    𝓞.crAnF [ofCrAnState φ, ofState ψ]ₛca = 0 := by
  rw [ofState, map_sum, map_sum]
  rw [Finset.sum_eq_zero]
  intro x hx
  apply 𝓞.superCommuteF_different_statistics
  simpa [crAnStatistics] using h

lemma crAnF_superCommuteF_anPart_ofState_diff_grade_zero (φ ψ : 𝓕.States)
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) :
    𝓞.crAnF [anPart φ, ofState ψ]ₛca = 0 := by
  match φ with
  | States.inAsymp _ =>
    simp
  | States.position φ =>
    simp only [anPart_position]
    apply 𝓞.crAnF_superCommuteF_ofCrAnState_ofState_diff_grade_zero _ _ _
    simpa [crAnStatistics] using h
  | States.outAsymp _ =>
    simp only [anPart_posAsymp]
    apply 𝓞.crAnF_superCommuteF_ofCrAnState_ofState_diff_grade_zero _ _
    simpa [crAnStatistics] using h

lemma crAnF_superCommuteF_ofState_ofState_mem_center (φ ψ : 𝓕.States) :
    𝓞.crAnF [ofState φ, ofState ψ]ₛca ∈ Subalgebra.center ℂ 𝓞.A := by
  rw [ofState, map_sum]
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, map_sum]
  refine Subalgebra.sum_mem (Subalgebra.center ℂ 𝓞.A) ?h
  intro x _
  exact crAnF_superCommuteF_ofCrAnState_ofState_mem_center 𝓞 ⟨φ, x⟩ ψ

lemma crAnF_superCommuteF_anPart_anPart (φ ψ : 𝓕.States) :
    𝓞.crAnF [anPart φ, anPart ψ]ₛca = 0 := by
  match φ, ψ with
  | _, States.inAsymp _ =>
    simp
  | States.inAsymp _, _ =>
    simp
  | States.position φ, States.position ψ =>
    simp only [anPart_position]
    rw [𝓞.superCommuteF_annihilate_annihilate]
    rfl
    rfl
  | States.position φ, States.outAsymp _ =>
    simp only [anPart_position, anPart_posAsymp]
    rw [𝓞.superCommuteF_annihilate_annihilate]
    rfl
    rfl
  | States.outAsymp _, States.outAsymp _ =>
    simp only [anPart_posAsymp]
    rw [𝓞.superCommuteF_annihilate_annihilate]
    rfl
    rfl
  | States.outAsymp _, States.position _ =>
    simp only [anPart_posAsymp, anPart_position]
    rw [𝓞.superCommuteF_annihilate_annihilate]
    rfl
    rfl

lemma crAnF_superCommuteF_crPart_crPart (φ ψ : 𝓕.States) :
    𝓞.crAnF [crPart φ, crPart ψ]ₛca = 0 := by
  match φ, ψ with
  | _, States.outAsymp _ =>
    simp
  | States.outAsymp _, _ =>
    simp
  | States.position φ, States.position ψ =>
    simp only [crPart_position]
    rw [𝓞.superCommuteF_create_create]
    rfl
    rfl
  | States.position φ, States.inAsymp _ =>
    simp only [crPart_position, crPart_negAsymp]
    rw [𝓞.superCommuteF_create_create]
    rfl
    rfl
  | States.inAsymp _, States.inAsymp _ =>
    simp only [crPart_negAsymp]
    rw [𝓞.superCommuteF_create_create]
    rfl
    rfl
  | States.inAsymp _, States.position _ =>
    simp only [crPart_negAsymp, crPart_position]
    rw [𝓞.superCommuteF_create_create]
    rfl
    rfl

lemma crAnF_superCommuteF_ofCrAnState_ofCrAnList_eq_sum (φ : 𝓕.CrAnStates) (φs : List 𝓕.CrAnStates) :
    𝓞.crAnF [ofCrAnState φ, ofCrAnList φs]ₛca
    = 𝓞.crAnF (∑ (n : Fin φs.length), 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (List.take n φs)) •
    [ofCrAnState φ, ofCrAnState (φs.get n)]ₛca * ofCrAnList (φs.eraseIdx n)) := by
  conv_lhs =>
    rw [← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofCrAnList_eq_sum]
  rw [map_sum, map_sum]
  congr
  funext x
  repeat rw [map_mul]
  rw [map_smul, map_smul, ofCrAnList_singleton]
  have h := Subalgebra.mem_center_iff.mp (𝓞.superCommuteF_crAn_center φ (φs.get x))
  rw [h, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_assoc]
  congr 1
  · simp
  · congr
    rw [← map_mul, ← ofCrAnList_append, ← List.eraseIdx_eq_take_drop_succ]

lemma crAnF_superCommuteF_ofCrAnState_ofStateList_eq_sum (φ : 𝓕.CrAnStates) (φs : List 𝓕.States) :
    𝓞.crAnF [ofCrAnState φ, ofStateList φs]ₛca
    = 𝓞.crAnF (∑ (n : Fin φs.length), 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ (List.take n φs)) •
    [ofCrAnState φ, ofState (φs.get n)]ₛca * ofStateList (φs.eraseIdx n)) := by
  conv_lhs =>
    rw [← ofCrAnList_singleton, superCommuteF_ofCrAnList_ofStateList_eq_sum]
  rw [map_sum, map_sum]
  congr
  funext x
  repeat rw [map_mul]
  rw [map_smul, map_smul, ofCrAnList_singleton]
  have h := Subalgebra.mem_center_iff.mp
    (crAnF_superCommuteF_ofCrAnState_ofState_mem_center 𝓞 φ (φs.get x))
  rw [h, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_assoc]
  congr 1
  · simp
  · congr
    rw [← map_mul, ← ofStateList_append, ← List.eraseIdx_eq_take_drop_succ]

end ProtoOperatorAlgebra
end FieldSpecification
