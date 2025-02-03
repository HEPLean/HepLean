/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.FieldOpFreeAlgebra.SuperCommute
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.TwoSidedIdeal.Operations
/-!

# Field operator algebra

-/

namespace FieldSpecification
open FieldOpFreeAlgebra
open HepLean.List
open FieldStatistic

variable (𝓕 : FieldSpecification)

/-- The set contains the super-commutors equal to zero in the operator algebra.
  This contains e.g. the super-commutor of two creation operators. -/
def fieldOpIdealSet : Set (FieldOpFreeAlgebra 𝓕) :=
  { x |
    (∃ (φ1 φ2 φ3 : 𝓕.CrAnFieldOp),
        x = [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca)
    ∨ (∃ (φc φc' : 𝓕.CrAnFieldOp) (_ : 𝓕 |>ᶜ φc = .create) (_ : 𝓕 |>ᶜ φc' = .create),
      x = [ofCrAnOpF φc, ofCrAnOpF φc']ₛca)
    ∨ (∃ (φa φa' : 𝓕.CrAnFieldOp) (_ : 𝓕 |>ᶜ φa = .annihilate) (_ : 𝓕 |>ᶜ φa' = .annihilate),
      x = [ofCrAnOpF φa, ofCrAnOpF φa']ₛca)
    ∨ (∃ (φ φ' : 𝓕.CrAnFieldOp) (_ : ¬ (𝓕 |>ₛ φ) = (𝓕 |>ₛ φ')),
      x = [ofCrAnOpF φ, ofCrAnOpF φ']ₛca)}

/-- The algebra spanned by cr and an parts of fields, with appropriate super-commutors
  set to zero. -/
abbrev FieldOpAlgebra : Type := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.Quotient

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

/-- The instance of a setoid on `FieldOpFreeAlgebra` from the ideal `TwoSidedIdeal`. -/
instance : Setoid (FieldOpFreeAlgebra 𝓕) := (TwoSidedIdeal.span 𝓕.fieldOpIdealSet).ringCon.toSetoid

lemma equiv_iff_sub_mem_ideal (x y : FieldOpFreeAlgebra 𝓕) :
    x ≈ y ↔ x - y ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [← TwoSidedIdeal.rel_iff]
  rfl

/-- The projection of `FieldOpFreeAlgebra` down to `FieldOpAlgebra` as an algebra map. -/
def ι : FieldOpFreeAlgebra 𝓕 →ₐ[ℂ] FieldOpAlgebra 𝓕 where
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

lemma ι_apply (x : FieldOpFreeAlgebra 𝓕) : ι x = Quotient.mk _ x := rfl

lemma ι_of_mem_fieldOpIdealSet (x : FieldOpFreeAlgebra 𝓕) (hx : x ∈ 𝓕.fieldOpIdealSet) :
    ι x = 0 := by
  rw [ι_apply]
  change ⟦x⟧ = ⟦0⟧
  simp only [ringConGen, Quotient.eq]
  refine RingConGen.Rel.of x 0 ?_
  simpa using hx

lemma ι_superCommuteF_of_create_create (φc φc' : 𝓕.CrAnFieldOp) (hφc : 𝓕 |>ᶜ φc = .create)
    (hφc' : 𝓕 |>ᶜ φc' = .create) : ι [ofCrAnOpF φc, ofCrAnOpF φc']ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_and_left, Set.mem_setOf_eq]
  simp only [exists_prop]
  right
  left
  use φc, φc', hφc, hφc'

lemma ι_superCommuteF_of_annihilate_annihilate (φa φa' : 𝓕.CrAnFieldOp)
    (hφa : 𝓕 |>ᶜ φa = .annihilate) (hφa' : 𝓕 |>ᶜ φa' = .annihilate) :
    ι [ofCrAnOpF φa, ofCrAnOpF φa']ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_and_left, Set.mem_setOf_eq]
  simp only [exists_prop]
  right
  right
  left
  use φa, φa', hφa, hφa'

lemma ι_superCommuteF_of_diff_statistic {φ ψ : 𝓕.CrAnFieldOp}
    (h : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)) : ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq]
  right
  right
  right
  use φ, ψ

lemma ι_superCommuteF_zero_of_fermionic (φ ψ : 𝓕.CrAnFieldOp)
    (h : [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca ∈ statisticSubmodule fermionic) :
    ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca = 0 := by
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton] at h ⊢
  rcases statistic_neq_of_superCommuteF_fermionic h with h | h
  · simp only [ofCrAnListF_singleton]
    apply ι_superCommuteF_of_diff_statistic
    simpa using h
  · simp [h]

lemma ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_zero (φ ψ : 𝓕.CrAnFieldOp) :
    [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca ∈ statisticSubmodule bosonic ∨
    ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca = 0 := by
  rcases superCommuteF_ofCrAnListF_ofCrAnListF_bosonic_or_fermionic [φ] [ψ] with h | h
  · simp_all [ofCrAnListF_singleton]
  · simp_all only [ofCrAnListF_singleton]
    right
    exact ι_superCommuteF_zero_of_fermionic _ _ h

/-!

## Super-commutes are in the center

-/

@[simp]
lemma ι_superCommuteF_ofCrAnOpF_superCommuteF_ofCrAnOpF_ofCrAnOpF (φ1 φ2 φ3 : 𝓕.CrAnFieldOp) :
    ι [ofCrAnOpF φ1, [ofCrAnOpF φ2, ofCrAnOpF φ3]ₛca]ₛca = 0 := by
  apply ι_of_mem_fieldOpIdealSet
  simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq]
  left
  use φ1, φ2, φ3

lemma ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnOpF (φ1 φ2 φ3 : 𝓕.CrAnFieldOp) :
    ι [[ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca, ofCrAnOpF φ3]ₛca = 0 := by
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton, ← ofCrAnListF_singleton]
  rcases superCommuteF_ofCrAnListF_ofCrAnListF_bosonic_or_fermionic [φ1] [φ2] with h | h
  · rw [bonsonic_superCommuteF_symm h]
    simp [ofCrAnListF_singleton]
  · rcases ofCrAnListF_bosonic_or_fermionic [φ3] with h' | h'
    · rw [superCommuteF_bonsonic_symm h']
      simp [ofCrAnListF_singleton]
    · rw [superCommuteF_fermionic_fermionic_symm h h']
      simp [ofCrAnListF_singleton]

lemma ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnListF (φ1 φ2 : 𝓕.CrAnFieldOp)
    (φs : List 𝓕.CrAnFieldOp) :
    ι [[ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca, ofCrAnListF φs]ₛca = 0 := by
  rw [← ofCrAnListF_singleton, ← ofCrAnListF_singleton]
  rcases superCommuteF_ofCrAnListF_ofCrAnListF_bosonic_or_fermionic [φ1] [φ2] with h | h
  · rw [superCommuteF_bosonic_ofCrAnListF_eq_sum _ _ h]
    simp [ofCrAnListF_singleton, ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnOpF]
  · rw [superCommuteF_fermionic_ofCrAnListF_eq_sum _ _ h]
    simp [ofCrAnListF_singleton, ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnOpF]

@[simp]
lemma ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_fieldOpFreeAlgebra (φ1 φ2 : 𝓕.CrAnFieldOp)
    (a : 𝓕.FieldOpFreeAlgebra) : ι [[ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca, a]ₛca = 0 := by
  change (ι.toLinearMap ∘ₗ superCommuteF [ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca) a = _
  have h1 : (ι.toLinearMap ∘ₗ superCommuteF [ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca) = 0 := by
    apply (ofCrAnListFBasis.ext fun l ↦ ?_)
    simp [ι_superCommuteF_superCommuteF_ofCrAnOpF_ofCrAnOpF_ofCrAnListF]
  rw [h1]
  simp

lemma ι_commute_fieldOpFreeAlgebra_superCommuteF_ofCrAnOpF_ofCrAnOpF (φ1 φ2 : 𝓕.CrAnFieldOp)
    (a : 𝓕.FieldOpFreeAlgebra) : ι a * ι [ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca -
    ι [ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca * ι a = 0 := by
  rcases ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_zero φ1 φ2 with h | h
  swap
  · simp [h]
  trans - ι [[ofCrAnOpF φ1, ofCrAnOpF φ2]ₛca, a]ₛca
  · rw [bosonic_superCommuteF h]
    simp
  · simp

lemma ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_mem_center (φ ψ : 𝓕.CrAnFieldOp) :
    ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛca ∈ Subalgebra.center ℂ 𝓕.FieldOpAlgebra := by
  rw [Subalgebra.mem_center_iff]
  intro a
  obtain ⟨a, rfl⟩ := ι_surjective a
  have h0 := ι_commute_fieldOpFreeAlgebra_superCommuteF_ofCrAnOpF_ofCrAnOpF φ ψ a
  trans ι ((superCommuteF (ofCrAnOpF φ)) (ofCrAnOpF ψ)) * ι a + 0
  swap
  simp only [add_zero]
  rw [← h0]
  abel

/-!

## The kernal of ι
-/

lemma ι_eq_zero_iff_mem_ideal (x : FieldOpFreeAlgebra 𝓕) :
    ι x = 0 ↔ x ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [ι_apply]
  change ⟦x⟧ = ⟦0⟧ ↔ _
  simp only [ringConGen, Quotient.eq]
  rw [TwoSidedIdeal.mem_iff]
  simp only
  rfl

lemma bosonicProj_mem_fieldOpIdealSet_or_zero (x : FieldOpFreeAlgebra 𝓕) (hx : x ∈ 𝓕.fieldOpIdealSet) :
    x.bosonicProj.1 ∈ 𝓕.fieldOpIdealSet ∨ x.bosonicProj = 0 := by
  have hx' := hx
  simp only [fieldOpIdealSet, exists_prop, Set.mem_setOf_eq] at hx
  rcases hx with ⟨φ1, φ2, φ3, rfl⟩ | ⟨φc, φc', hφc, hφc', rfl⟩ | ⟨φa, φa', hφa, hφa', rfl⟩ |
    ⟨φ, φ', hdiff, rfl⟩
  · rcases superCommuteF_superCommuteF_ofCrAnOpF_bosonic_or_fermionic φ1 φ2 φ3 with h | h
    · left
      rw [bosonicProj_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProj_of_mem_fermionic _ h]
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φc φc' with h | h
    · left
      rw [bosonicProj_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProj_of_mem_fermionic _ h]
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φa φa' with h | h
    · left
      rw [bosonicProj_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProj_of_mem_fermionic _ h]
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φ φ' with h | h
    · left
      rw [bosonicProj_of_mem_bosonic _ h]
      simpa using hx'
    · right
      rw [bosonicProj_of_mem_fermionic _ h]

lemma fermionicProj_mem_fieldOpIdealSet_or_zero (x : FieldOpFreeAlgebra 𝓕) (hx : x ∈ 𝓕.fieldOpIdealSet) :
    x.fermionicProj.1 ∈ 𝓕.fieldOpIdealSet ∨ x.fermionicProj = 0 := by
  have hx' := hx
  simp only [fieldOpIdealSet, exists_prop, Set.mem_setOf_eq] at hx
  rcases hx with ⟨φ1, φ2, φ3, rfl⟩ | ⟨φc, φc', hφc, hφc', rfl⟩ | ⟨φa, φa', hφa, hφa', rfl⟩ |
    ⟨φ, φ', hdiff, rfl⟩
  · rcases superCommuteF_superCommuteF_ofCrAnOpF_bosonic_or_fermionic φ1 φ2 φ3 with h | h
    · right
      rw [fermionicProj_of_mem_bosonic _ h]
    · left
      rw [fermionicProj_of_mem_fermionic _ h]
      simpa using hx'
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φc φc' with h | h
    · right
      rw [fermionicProj_of_mem_bosonic _ h]
    · left
      rw [fermionicProj_of_mem_fermionic _ h]
      simpa using hx'
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φa φa' with h | h
    · right
      rw [fermionicProj_of_mem_bosonic _ h]
    · left
      rw [fermionicProj_of_mem_fermionic _ h]
      simpa using hx'
  · rcases superCommuteF_ofCrAnOpF_ofCrAnOpF_bosonic_or_fermionic φ φ' with h | h
    · right
      rw [fermionicProj_of_mem_bosonic _ h]
    · left
      rw [fermionicProj_of_mem_fermionic _ h]
      simpa using hx'

lemma bosonicProj_mem_ideal (x : FieldOpFreeAlgebra 𝓕) (hx : x ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) :
    x.bosonicProj.1 ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at hx
  let p {k : Set 𝓕.FieldOpFreeAlgebra} (a : FieldOpFreeAlgebra 𝓕) (h : a ∈ AddSubgroup.closure k) : Prop :=
    a.bosonicProj.1 ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet
  change p x hx
  apply AddSubgroup.closure_induction
  · intro x hx
    simp only [p]
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨d, hd, y, hy, rfl⟩ := Set.mem_mul.mp ha
    rw [bosonicProj_mul, bosonicProj_mul, fermionicProj_mul]
    simp only [add_mul]
    rcases fermionicProj_mem_fieldOpIdealSet_or_zero y hy with hfy | hfy
      <;> rcases bosonicProj_mem_fieldOpIdealSet_or_zero y hy with hby | hby
    · apply TwoSidedIdeal.add_mem
      apply TwoSidedIdeal.add_mem
      · /- boson, boson, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProj d) * ↑(bosonicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProj d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (bosonicProj y).1
          simp [hby]
        · use ↑(bosonicProj b)
          simp
      · /- fermion, fermion, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProj d) * ↑(fermionicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProj d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (fermionicProj y).1
          simp [hby, hfy]
        · use ↑(bosonicProj b)
          simp
      apply TwoSidedIdeal.add_mem
      · /- boson, fermion, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProj d) * ↑(fermionicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProj d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (fermionicProj y).1
          simp [hby, hfy]
        · use ↑(fermionicProj b)
          simp
      · /- fermion, boson, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProj d) * ↑(bosonicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProj d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (bosonicProj y).1
          simp [hby, hfy]
        · use ↑(fermionicProj b)
          simp
    · simp only [hby, ZeroMemClass.coe_zero, mul_zero, zero_mul, zero_add, add_zero]
      apply TwoSidedIdeal.add_mem
      · /- fermion, fermion, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProj d) * ↑(fermionicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProj d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (fermionicProj y).1
          simp [hby, hfy]
        · use ↑(bosonicProj b)
          simp
      · /- boson, fermion, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProj d) * ↑(fermionicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProj d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (fermionicProj y).1
          simp [hby, hfy]
        · use ↑(fermionicProj b)
          simp
    · simp only [hfy, ZeroMemClass.coe_zero, mul_zero, zero_mul, add_zero, zero_add]
      apply TwoSidedIdeal.add_mem
      · /- boson, boson, boson mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(bosonicProj d) * ↑(bosonicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use bosonicProj d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (bosonicProj y).1
          simp [hby]
        · use ↑(bosonicProj b)
          simp
      · /- fermion, boson, fermion mem-/
        rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure]
        refine Set.mem_of_mem_of_subset ?_ AddSubgroup.subset_closure
        apply Set.mem_mul.mpr
        use ↑(fermionicProj d) * ↑(bosonicProj y)
        apply And.intro
        · apply Set.mem_mul.mpr
          use fermionicProj d
          simp only [Set.mem_univ, mul_eq_mul_left_iff, ZeroMemClass.coe_eq_zero, true_and]
          use (bosonicProj y).1
          simp [hby, hfy]
        · use ↑(fermionicProj b)
          simp
    · simp [hfy, hby]
  · simp [p]
  · intro x y hx hy hpx hpy
    simp_all only [map_add, Submodule.coe_add, p]
    apply TwoSidedIdeal.add_mem
    · exact hpx
    · exact hpy
  · intro x hx
    simp [p]

lemma fermionicProj_mem_ideal (x : FieldOpFreeAlgebra 𝓕) (hx : x ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) :
    x.fermionicProj.1 ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet := by
  have hb := bosonicProj_mem_ideal x hx
  rw [← ι_eq_zero_iff_mem_ideal] at hx hb ⊢
  rw [← bosonicProj_add_fermionicProj x] at hx
  simp only [map_add] at hx
  simp_all

lemma ι_eq_zero_iff_ι_bosonicProj_fermonicProj_zero (x : FieldOpFreeAlgebra 𝓕) :
    ι x = 0 ↔ ι x.bosonicProj.1 = 0 ∧ ι x.fermionicProj.1 = 0 := by
  apply Iff.intro
  · intro h
    rw [ι_eq_zero_iff_mem_ideal] at h ⊢
    rw [ι_eq_zero_iff_mem_ideal]
    apply And.intro
    · exact bosonicProj_mem_ideal x h
    · exact fermionicProj_mem_ideal x h
  · intro h
    rw [← bosonicProj_add_fermionicProj x]
    simp_all

/-!

## Constructors

-/

/-- An element of `FieldOpAlgebra` from a `FieldOp`. -/
def ofFieldOp (φ : 𝓕.FieldOp) : 𝓕.FieldOpAlgebra := ι (ofFieldOpF φ)

lemma ofFieldOp_eq_ι_ofFieldOpF (φ : 𝓕.FieldOp) : ofFieldOp φ = ι (ofFieldOpF φ) := rfl

/-- An element of `FieldOpAlgebra` from a list of `FieldOp`. -/
def ofFieldOpList (φs : List 𝓕.FieldOp) : 𝓕.FieldOpAlgebra := ι (ofFieldOpListF φs)

lemma ofFieldOpList_eq_ι_ofFieldOpListF (φs : List 𝓕.FieldOp) :
    ofFieldOpList φs = ι (ofFieldOpListF φs) := rfl

lemma ofFieldOpList_append (φs ψs : List 𝓕.FieldOp) :
    ofFieldOpList (φs ++ ψs) = ofFieldOpList φs * ofFieldOpList ψs := by
  simp only [ofFieldOpList]
  rw [ofFieldOpListF_append]
  simp

lemma ofFieldOpList_cons (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    ofFieldOpList (φ :: φs) = ofFieldOp φ * ofFieldOpList φs := by
  simp only [ofFieldOpList]
  rw [ofFieldOpListF_cons]
  simp only [map_mul]
  rfl

lemma ofFieldOpList_singleton (φ : 𝓕.FieldOp) :
    ofFieldOpList [φ] = ofFieldOp φ := by
  simp only [ofFieldOpList, ofFieldOp, ofFieldOpListF_singleton]

/-- An element of `FieldOpAlgebra` from a `CrAnFieldOp`. -/
def ofCrAnFieldOp (φ : 𝓕.CrAnFieldOp) : 𝓕.FieldOpAlgebra := ι (ofCrAnOpF φ)

lemma ofCrAnFieldOp_eq_ι_ofCrAnOpF (φ : 𝓕.CrAnFieldOp) :
    ofCrAnFieldOp φ = ι (ofCrAnOpF φ) := rfl

lemma ofFieldOp_eq_sum (φ : 𝓕.FieldOp) :
    ofFieldOp φ = (∑ i : 𝓕.fieldOpToCrAnType φ, ofCrAnFieldOp ⟨φ, i⟩) := by
  rw [ofFieldOp, ofFieldOpF]
  simp only [map_sum]
  rfl

/-- An element of `FieldOpAlgebra` from a list of `CrAnFieldOp`. -/
def ofCrAnFieldOpList (φs : List 𝓕.CrAnFieldOp) : 𝓕.FieldOpAlgebra := ι (ofCrAnListF φs)

lemma ofCrAnFieldOpList_eq_ι_ofCrAnListF (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnFieldOpList φs = ι (ofCrAnListF φs) := rfl

lemma ofCrAnFieldOpList_append (φs ψs : List 𝓕.CrAnFieldOp) :
    ofCrAnFieldOpList (φs ++ ψs) = ofCrAnFieldOpList φs * ofCrAnFieldOpList ψs := by
  simp only [ofCrAnFieldOpList]
  rw [ofCrAnListF_append]
  simp

lemma ofCrAnFieldOpList_singleton (φ : 𝓕.CrAnFieldOp) :
    ofCrAnFieldOpList [φ] = ofCrAnFieldOp φ := by
  simp only [ofCrAnFieldOpList, ofCrAnFieldOp, ofCrAnListF_singleton]

lemma ofFieldOpList_eq_sum (φs : List 𝓕.FieldOp) :
    ofFieldOpList φs = ∑ s : CrAnSection φs, ofCrAnFieldOpList s.1 := by
  rw [ofFieldOpList, ofFieldOpListF_sum]
  simp only [map_sum]
  rfl

/-- The annihilation part of a state. -/
def anPart (φ : 𝓕.FieldOp) : 𝓕.FieldOpAlgebra := ι (anPartF φ)

lemma anPart_eq_ι_anPartF (φ : 𝓕.FieldOp) : anPart φ = ι (anPartF φ) := rfl

@[simp]
lemma anPart_negAsymp (φ : 𝓕.IncomingAsymptotic) :
    anPart (FieldOp.inAsymp φ) = 0 := by
  simp [anPart, anPartF]

@[simp]
lemma anPart_position (φ : 𝓕.PositionFieldOp) :
    anPart (FieldOp.position φ) =
    ofCrAnFieldOp ⟨FieldOp.position φ, CreateAnnihilate.annihilate⟩ := by
  simp [anPart, ofCrAnFieldOp]

@[simp]
lemma anPart_posAsymp (φ : 𝓕.OutgoingAsymptotic) :
    anPart (FieldOp.outAsymp φ) = ofCrAnFieldOp ⟨FieldOp.outAsymp φ, ()⟩ := by
  simp [anPart, ofCrAnFieldOp]

/-- The creation part of a state. -/
def crPart (φ : 𝓕.FieldOp) : 𝓕.FieldOpAlgebra := ι (crPartF φ)

lemma crPart_eq_ι_crPartF (φ : 𝓕.FieldOp) : crPart φ = ι (crPartF φ) := rfl

@[simp]
lemma crPart_negAsymp (φ : 𝓕.IncomingAsymptotic) :
    crPart (FieldOp.inAsymp φ) = ofCrAnFieldOp ⟨FieldOp.inAsymp φ, ()⟩ := by
  simp [crPart, ofCrAnFieldOp]

@[simp]
lemma crPart_position (φ : 𝓕.PositionFieldOp) :
    crPart (FieldOp.position φ) =
    ofCrAnFieldOp ⟨FieldOp.position φ, CreateAnnihilate.create⟩ := by
  simp [crPart, ofCrAnFieldOp]

@[simp]
lemma crPart_posAsymp (φ : 𝓕.OutgoingAsymptotic) :
    crPart (FieldOp.outAsymp φ) = 0 := by
  simp [crPart]

lemma ofFieldOp_eq_crPart_add_anPart (φ : 𝓕.FieldOp) :
    ofFieldOp φ = crPart φ + anPart φ := by
  rw [ofFieldOp, crPart, anPart, ofFieldOpF_eq_crPartF_add_anPartF]
  simp only [map_add]

end FieldOpAlgebra
end FieldSpecification
