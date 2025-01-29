/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.TimeOrder
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.Basic
/-!

# Time Ordering on Field operator algebra

-/

namespace FieldSpecification
open CrAnAlgebra
open HepLean.List
open FieldStatistic

namespace FieldOpAlgebra
variable {𝓕 : FieldSpecification}

lemma ι_timeOrder_superCommute_time {φ ψ : 𝓕.CrAnStates}
    (hφψ : crAnTimeOrderRel φ ψ) (hψφ : crAnTimeOrderRel ψ φ) (a b : 𝓕.CrAnAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnState φ, ofCrAnState ψ]ₛca * b) =
    ι ([ofCrAnState φ, ofCrAnState ψ]ₛca * 𝓣ᶠ(a * b)) := by
  let pb (b : 𝓕.CrAnAlgebra) (hc : b ∈ Submodule.span ℂ (Set.range ofCrAnListBasis)) :
    Prop :=  ι 𝓣ᶠ(a * [ofCrAnState φ, ofCrAnState ψ]ₛca * b) =
    ι ([ofCrAnState φ, ofCrAnState ψ]ₛca * 𝓣ᶠ(a * b))
  change pb b (Basis.mem_span _ b)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl⟩ := hx
    simp [pb]
    let pa (a : 𝓕.CrAnAlgebra) (hc : a ∈ Submodule.span ℂ (Set.range ofCrAnListBasis)) :
      Prop := ι 𝓣ᶠ(a * [ofCrAnState φ, ofCrAnState ψ]ₛca * ofCrAnList φs) =
      ι ([ofCrAnState φ, ofCrAnState ψ]ₛca * 𝓣ᶠ(a* ofCrAnList φs))
    change pa a (Basis.mem_span _ a)
    apply Submodule.span_induction
    · intro x hx
      obtain ⟨φs', rfl⟩ := hx
      simp [pa]
      conv_lhs =>
        rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, superCommute_ofCrAnList_ofCrAnList]
        simp [mul_sub, sub_mul, ← ofCrAnList_append]
        rw [timeOrder_ofCrAnList, timeOrder_ofCrAnList]
      have h1 : crAnTimeOrderSign (φs' ++ φ :: ψ :: φs) = crAnTimeOrderSign (φs' ++ ψ :: φ :: φs) := by
        trans crAnTimeOrderSign (φs' ++ [φ, ψ] ++  φs)
        simp
        rw [crAnTimeOrderSign]
        have hp : List.Perm [φ,ψ] [ψ,φ] := by exact List.Perm.swap ψ φ []
        rw [Wick.koszulSign_perm_eq _ _ φ _ _ _ _ _ hp]
        simp
        rfl
        simp_all
      rw [h1]
      simp
      have h1 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ φs' [φ, ψ] φs
       (by simp_all)
      rw [crAnTimeOrderList, show φs' ++ φ :: ψ :: φs = φs' ++ [φ, ψ] ++ φs by simp, h1]
      have h2 := insertionSort_of_eq_list 𝓕.crAnTimeOrderRel φ φs' [ψ, φ] φs
       (by simp_all)
      rw [crAnTimeOrderList, show φs' ++ ψ :: φ :: φs = φs' ++ [ψ, φ] ++ φs by simp, h2]
      repeat rw [ofCrAnList_append]
      rw [smul_smul, mul_comm, ← smul_smul, ← smul_sub]
      rw [map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
      rw [← mul_smul_comm]
      rw [mul_assoc, mul_assoc, mul_assoc ,mul_assoc ,mul_assoc ,mul_assoc]
      rw [← mul_sub, ← mul_sub, mul_smul_comm, mul_smul_comm, ← smul_mul_assoc,
        ← smul_mul_assoc]
      rw [← sub_mul]
      have h1 : (ι (ofCrAnList [φ, ψ]) - (exchangeSign (𝓕.crAnStatistics φ)) (𝓕.crAnStatistics ψ) • ι (ofCrAnList [ψ, φ])) =
        ι [ofCrAnState φ, ofCrAnState ψ]ₛca := by
        rw [superCommute_ofCrAnState_ofCrAnState]
        rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_append]
        simp only [instCommGroup.eq_1, List.singleton_append, Algebra.smul_mul_assoc, map_sub,
          map_smul]
        rw [← ofCrAnList_append]
        simp
      rw [h1]
      have hc : ι ((superCommute (ofCrAnState φ)) (ofCrAnState ψ)) ∈ Subalgebra.center ℂ 𝓕.FieldOpAlgebra := by
        apply ι_superCommute_ofCrAnState_ofCrAnState_mem_center
      rw [Subalgebra.mem_center_iff] at hc
      repeat rw [← mul_assoc]
      rw [hc]
      repeat rw [mul_assoc]
      rw [smul_mul_assoc]
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
      rw [← ofCrAnList_append, ← ofCrAnList_append, ← ofCrAnList_append, ← ofCrAnList_append]
      have h1 := insertionSort_of_takeWhile_filter 𝓕.crAnTimeOrderRel φ φs' φs
      simp at  h1 ⊢
      rw [← h1]
      rw [← crAnTimeOrderList]
      by_cases hq : (𝓕 |>ₛ φ) ≠ (𝓕 |>ₛ ψ)
      · rw [ι_superCommute_of_diff_statistic hq]
        simp
      · rw [crAnTimeOrderSign, Wick.koszulSign_eq_rel_eq_stat _ _, ← crAnTimeOrderSign]
        rw [timeOrder_ofCrAnList]
        simp
        exact hψφ
        exact hφψ
        simpa using hq
    · simp [pa]
    · intro x y hx hy hpx hpy
      simp_all [pa,mul_add, add_mul]
    · intro x hx hpx
      simp_all [pa, hpx]
  · simp [pb]
  · intro x y hx hy hpx hpy
    simp_all [pb,mul_add, add_mul]
  · intro x hx hpx
    simp_all [pb, hpx]

/-!

## Defining normal order for `FiedOpAlgebra`.

-/

lemma ι_timeOrder_zero_of_mem_ideal (a : 𝓕.CrAnAlgebra)
    (h : a ∈ TwoSidedIdeal.span 𝓕.fieldOpIdealSet) : ι 𝓣ᶠ(a) = 0 := by
  rw [TwoSidedIdeal.mem_span_iff_mem_addSubgroup_closure] at h
  let p {k : Set 𝓕.CrAnAlgebra} (a : CrAnAlgebra 𝓕) (h : a ∈ AddSubgroup.closure k) := ι 𝓣ᶠ(a) = 0
  change p a h
  apply AddSubgroup.closure_induction
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨a, ha, c, hc, rfl⟩ := ha
    simp only [p]
    simp only [fieldOpIdealSet, exists_prop, exists_and_left, Set.mem_setOf_eq] at hc
    match hc with
    | Or.inl hc =>
      obtain ⟨φa, φa', hφa, hφa', rfl⟩ := hc
      sorry
    | Or.inr (Or.inl hc) =>
      obtain ⟨φa, φa', hφa, hφa', rfl⟩ := hc
      sorry
    | Or.inr (Or.inr (Or.inl hc)) =>
      obtain ⟨φa, φa', hφa, hφa', rfl⟩ := hc
      sorry
    | Or.inr (Or.inr (Or.inr hc)) =>
      obtain ⟨φa, φa', hφa, hφa', rfl⟩ := hc
      sorry
  · simp [p]
  · intro x y hx hy
    simp only [map_add, p]
    intro h1 h2
    simp [h1, h2]
  · intro x hx
    simp [p]

lemma ι_timeOrder_eq_of_equiv (a b : 𝓕.CrAnAlgebra) (h : a ≈ b) :
    ι 𝓣ᶠ(a) = ι 𝓣ᶠ(b) := by
  rw [equiv_iff_sub_mem_ideal] at h
  rw [LinearMap.sub_mem_ker_iff.mp]
  simp only [LinearMap.mem_ker, ← map_sub]
  exact ι_timeOrder_zero_of_mem_ideal (a - b) h

/-- Normal ordering on `FieldOpAlgebra`. -/
noncomputable def timeOrder : FieldOpAlgebra 𝓕 →ₗ[ℂ] FieldOpAlgebra 𝓕 where
  toFun := Quotient.lift (ι.toLinearMap ∘ₗ CrAnAlgebra.timeOrder) ι_timeOrder_eq_of_equiv
  map_add' x y := by
    obtain ⟨x, hx⟩ := ι_surjective x
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hx hy
    rw [← map_add, ι_apply, ι_apply, ι_apply]
    rw [Quotient.lift_mk, Quotient.lift_mk, Quotient.lift_mk]
    simp
  map_smul' c y := by
    obtain ⟨y, hy⟩ := ι_surjective y
    subst hy
    rw [← map_smul, ι_apply, ι_apply]
    simp

end FieldOpAlgebra
end FieldSpecification
