/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.SuperCommute
/-!

# The operator algebras

-/

namespace FieldStruct
variable (𝓕 : FieldStruct)
open CrAnAlgebra

structure OperatorAlgebra where
  A : Type
  [A_semiRing : Semiring A] [A_algebra : Algebra ℂ A]
  crAnF : 𝓕.CrAnAlgebra →ₐ[ℂ] A
  superCommute_crAn_center : ∀ (φ ψ : 𝓕.CrAnStates),
    crAnF (superCommute (ofCrAnState φ) (ofCrAnState ψ))
    ∈ Subalgebra.center ℂ A
  superCommute_create_create : ∀ (φc φc' : 𝓕.CrAnStates)
    (_ : 𝓕.crAnStatesToCreateAnnihilate φc = CreateAnnihilate.create)
    (_ : 𝓕.crAnStatesToCreateAnnihilate φc' = CreateAnnihilate.create),
    crAnF (superCommute (ofCrAnState φc) (ofCrAnState φc')) = 0
  superCommute_annihilate_annihilate : ∀ (φa φa' : 𝓕.CrAnStates)
    (_ : 𝓕.crAnStatesToCreateAnnihilate φa = CreateAnnihilate.annihilate)
    (_ : 𝓕.crAnStatesToCreateAnnihilate φa' = CreateAnnihilate.annihilate),
    crAnF (superCommute (ofCrAnState φa) (ofCrAnState φa')) = 0
  superCommute_different_statistics : ∀ (φ φ' : 𝓕.CrAnStates)
    (_ : ¬ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φ')),
    crAnF (superCommute (ofCrAnState φ) (ofCrAnState φ')) = 0

namespace OperatorAlgebra
open FieldStatistic
variable {𝓕 : FieldStruct} (𝓞 : 𝓕.OperatorAlgebra)

instance : Semiring 𝓞.A := 𝓞.A_semiRing

instance : Algebra ℂ 𝓞.A := 𝓞.A_algebra

lemma crAnF_superCommute_ofCrAnState_ofState_mem_center (φ : 𝓕.CrAnStates) (ψ : 𝓕.States) :
    𝓞.crAnF (superCommute (ofCrAnState φ) (ofState ψ)) ∈ Subalgebra.center ℂ 𝓞.A := by
  rw [ofState, map_sum, map_sum]
  refine Subalgebra.sum_mem (Subalgebra.center ℂ 𝓞.A) ?h
  intro x _
  exact 𝓞.superCommute_crAn_center φ ⟨ψ, x⟩

lemma crAnF_superCommute_anPart_ofState_mem_center (φ ψ : 𝓕.States) :
    𝓞.crAnF ⟨anPart (StateAlgebra.ofState φ), ofState ψ⟩ₛca ∈ Subalgebra.center ℂ 𝓞.A := by
  match φ with
  | States.negAsymp _ =>
    simp
    exact Subalgebra.zero_mem (Subalgebra.center ℂ 𝓞.A)
  | States.position φ =>
    simp
    exact 𝓞.crAnF_superCommute_ofCrAnState_ofState_mem_center _ _
  | States.posAsymp _ =>
    simp
    exact 𝓞.crAnF_superCommute_ofCrAnState_ofState_mem_center _ _

lemma crAnF_superCommute_ofCrAnState_ofState_diff_grade_zero (φ : 𝓕.CrAnStates) (ψ : 𝓕.States)
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)):
    𝓞.crAnF (superCommute (ofCrAnState φ) (ofState ψ)) = 0 := by
  rw [ofState, map_sum, map_sum]
  rw [Finset.sum_eq_zero]
  intro x hx
  apply 𝓞.superCommute_different_statistics
  simpa [crAnStatistics] using h

lemma crAnF_superCommute_anPart_ofState_diff_grade_zero  (φ ψ : 𝓕.States)
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)):
    𝓞.crAnF (superCommute (anPart (StateAlgebra.ofState φ)) (ofState ψ)) = 0 := by
  match φ with
  | States.negAsymp _ =>
    simp
  | States.position φ =>
    simp
    apply 𝓞.crAnF_superCommute_ofCrAnState_ofState_diff_grade_zero _ _ _
    simpa [crAnStatistics] using h
  | States.posAsymp _ =>
    simp
    apply 𝓞.crAnF_superCommute_ofCrAnState_ofState_diff_grade_zero _ _
    simpa [crAnStatistics] using h

lemma crAnF_superCommute_ofState_ofState_mem_center (φ ψ : 𝓕.States) :
    𝓞.crAnF (superCommute (ofState φ) (ofState ψ)) ∈ Subalgebra.center ℂ 𝓞.A := by
  rw [ofState,  map_sum]
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, map_sum]
  refine Subalgebra.sum_mem (Subalgebra.center ℂ 𝓞.A) ?h
  intro x _
  exact crAnF_superCommute_ofCrAnState_ofState_mem_center 𝓞 ⟨φ, x⟩ ψ

lemma crAnF_superCommute_anPart_anPart (φ ψ : 𝓕.States) :
    𝓞.crAnF ⟨anPart (StateAlgebra.ofState φ), anPart (StateAlgebra.ofState ψ)⟩ₛca = 0 := by
  match φ, ψ with
  | _, States.negAsymp _ =>
    simp
  | States.negAsymp _, _ =>
    simp
  | States.position φ, States.position ψ =>
    simp
    rw [𝓞.superCommute_annihilate_annihilate]
    rfl
    rfl
  | States.position φ, States.posAsymp _ =>
    simp
    rw [𝓞.superCommute_annihilate_annihilate]
    rfl
    rfl
  | States.posAsymp _, States.posAsymp _ =>
    simp
    rw [𝓞.superCommute_annihilate_annihilate]
    rfl
    rfl
  | States.posAsymp _, States.position _ =>
    simp
    rw [𝓞.superCommute_annihilate_annihilate]
    rfl
    rfl

lemma crAnF_superCommute_crPart_crPart (φ ψ : 𝓕.States) :
    𝓞.crAnF ⟨crPart (StateAlgebra.ofState φ), crPart (StateAlgebra.ofState ψ)⟩ₛca = 0 := by
  match φ, ψ with
  | _, States.posAsymp _ =>
    simp
  | States.posAsymp _, _ =>
    simp
  | States.position φ, States.position ψ =>
    simp
    rw [𝓞.superCommute_create_create]
    rfl
    rfl
  | States.position φ, States.negAsymp _ =>
    simp
    rw [𝓞.superCommute_create_create]
    rfl
    rfl
  | States.negAsymp _, States.negAsymp _ =>
    simp
    rw [𝓞.superCommute_create_create]
    rfl
    rfl
  | States.negAsymp _, States.position _ =>
    simp
    rw [𝓞.superCommute_create_create]
    rfl
    rfl

lemma crAnF_superCommute_ofCrAnState_ofCrAnList_eq_sum (φ : 𝓕.CrAnStates) (φs : List 𝓕.CrAnStates) :
    𝓞.crAnF ⟨ofCrAnState φ, ofCrAnList φs⟩ₛca
    = 𝓞.crAnF (∑ (n : Fin φs.length), pairedSign (𝓕.crAnStatistics φ)
    (𝓕 |>ₛ (List.take n φs)) •
    ⟨ofCrAnState φ, ofCrAnState (φs.get n)⟩ₛca * ofCrAnList (φs.eraseIdx n)) := by
  conv_lhs =>
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList_eq_sum]
  rw [map_sum, map_sum]
  congr
  funext x
  repeat rw [map_mul]
  rw [map_smul, map_smul, ofCrAnList_singleton]
  have h := Subalgebra.mem_center_iff.mp (𝓞.superCommute_crAn_center φ (φs.get x))
  rw [h, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_assoc]
  congr 1
  · simp
  · congr
    rw [← map_mul, ← ofCrAnList_append, ← List.eraseIdx_eq_take_drop_succ]

lemma crAnF_superCommute_ofCrAnState_ofStateList_eq_sum (φ : 𝓕.CrAnStates) (φs : List 𝓕.States) :
    𝓞.crAnF ⟨ofCrAnState φ, ofStateList φs⟩ₛca
    = 𝓞.crAnF (∑ (n : Fin φs.length), pairedSign (𝓕.crAnStatistics φ)
    (FieldStatistic.ofList 𝓕.statesStatistic (List.take n φs)) •
    ⟨ofCrAnState φ, ofState (φs.get n)⟩ₛca * ofStateList (φs.eraseIdx n)) := by
  conv_lhs =>
    rw [← ofCrAnList_singleton, superCommute_ofCrAnList_ofStateList_eq_sum]
  rw [map_sum, map_sum]
  congr
  funext x
  repeat rw [map_mul]
  rw [map_smul, map_smul, ofCrAnList_singleton]
  have h := Subalgebra.mem_center_iff.mp
    (crAnF_superCommute_ofCrAnState_ofState_mem_center 𝓞 φ (φs.get x))
  rw [h, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_assoc]
  congr 1
  · simp
  · congr
    rw [← map_mul, ← ofStateList_append, ← List.eraseIdx_eq_take_drop_succ]

end OperatorAlgebra
end FieldStruct
