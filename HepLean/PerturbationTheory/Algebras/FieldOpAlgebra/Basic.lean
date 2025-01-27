/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.Meta.Remark.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Algebra.RingQuot
/-!

# Field operator algebra

-/

namespace FieldSpecification
open CrAnAlgebra
open ProtoOperatorAlgebra
open HepLean.List
open WickContraction
open FieldStatistic

variable (𝓕 : FieldSpecification)

/-- The set contains the super-commutors equal to zero in the operator algebra.
  This contains e.g. the super-commutor of two creation operators. -/
def fieldOpIdealSet : Set (CrAnAlgebra 𝓕) :=
  { x |
    (∃ (φ ψ : 𝓕.CrAnStates) (a : CrAnAlgebra 𝓕),
        x = a * [ofCrAnState φ, ofCrAnState ψ]ₛca - [ofCrAnState φ, ofCrAnState ψ]ₛca * a)
    ∨ (∃ (φc φc' : 𝓕.CrAnStates) (_ : 𝓕 |>ᶜ φc = .create) (_ : 𝓕 |>ᶜ φc' = .create),
      x = [ofCrAnState φc, ofCrAnState φc']ₛca)
    ∨ (∃ (φa φa' : 𝓕.CrAnStates) (_ : 𝓕 |>ᶜ φa = .annihilate) (_ : 𝓕 |>ᶜ φa' = .annihilate),
      x = [ofCrAnState φa, ofCrAnState φa']ₛca)
    ∨ (∃ (φ φ' : 𝓕.CrAnStates) (_ : ¬ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φ')),
      x = [ofCrAnState φ, ofCrAnState φ']ₛca)}

/-- The algebra spanned by cr and an parts of fields, with appropriate super-commutors
  set to zero. -/
abbrev FieldOpAlgebra : Type := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.Quotient

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-- The instance of a setoid on `CrAnAlgebra` from the ideal `TwoSidedIdeal`. -/
instance : Setoid (CrAnAlgebra 𝓕) := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.toSetoid

lemma equiv_iff_sub_mem_ideal (x y : CrAnAlgebra 𝓕) :
    x ≈ y ↔ x - y ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [← TwoSidedIdeal.rel_iff]
  rfl

/-- The projection of `CrAnAlgebra` down to `FieldOpAlgebra` as an algebra map. -/
def ι : CrAnAlgebra 𝓕 →ₐ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.mk'
  map_one' := by rfl
  map_mul' x y := by rfl
  map_zero' := by rfl
  map_add' x y := by rfl
  commutes' x := by rfl

lemma ι_surjective : Function.Surjective (@ι 𝓕) := by
  intro x
  obtain ⟨x⟩ := x
  use x
  rfl

lemma ι_apply (x : CrAnAlgebra 𝓕) : ι x = Quotient.mk _ x := rfl

lemma ι_of_mem_fieldOpIdealSet (x : CrAnAlgebra 𝓕) (hx : x ∈ 𝓕.fieldOpIdealSet) :
    ι x = 0 := by
  rw [ι_apply]
  change ⟦x⟧ = ⟦0⟧
  simp only [ringConGen, Quotient.eq]
  refine RingConGen.Rel.of x 0 ?_
  simpa using hx

lemma ι_superCommute_ofCrAnState_ofCrAnState_mem_center (φ ψ : 𝓕.CrAnStates) :
    ι [ofCrAnState φ, ofCrAnState ψ]ₛca ∈ Subalgebra.center ℂ 𝓕.FieldOpAlgebra := by
  rw [Subalgebra.mem_center_iff]
  intro b
  obtain ⟨b, rfl⟩ := ι_surjective b
  rw [← map_mul, ← map_mul]
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker]
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq]
  left
  use φ, ψ, b

lemma ι_superCommute_of_create_create (φc φc' : 𝓕.CrAnStates) (hφc : 𝓕 |>ᶜ φc = .create)
    (hφc' : 𝓕 |>ᶜ φc' = .create) : ι [ofCrAnState φc, ofCrAnState φc']ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_and_left, Set.mem_setOf_eq]
  simp only [exists_prop]
  right
  left
  use φc, φc', hφc, hφc'

lemma ι_superCommute_of_annihilate_annihilate (φa φa' : 𝓕.CrAnStates)
    (hφa : 𝓕 |>ᶜ φa = .annihilate) (hφa' : 𝓕 |>ᶜ φa' = .annihilate) :
    ι [ofCrAnState φa, ofCrAnState φa']ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_and_left, Set.mem_setOf_eq]
  simp only [exists_prop]
  right
  right
  left
  use φa, φa', hφa, hφa'

lemma ι_superCommute_of_diff_statistic (φ ψ : 𝓕.CrAnStates)
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) : ι [ofCrAnState φ, ofCrAnState ψ]ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq]
  right
  right
  right
  use φ, ψ

end FieldOpAlgebra
end FieldSpecification
