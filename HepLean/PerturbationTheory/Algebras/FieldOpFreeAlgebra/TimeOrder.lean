/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.TimeOrder
import HepLean.PerturbationTheory.Algebras.FieldOpFreeAlgebra.SuperCommute
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Time Ordering in the FieldOpFreeAlgebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace FieldOpFreeAlgebra

noncomputable section
open HepLean.List
/-!

## Time order

-/

/-- Time ordering for the `FieldOpFreeAlgebra`. -/
def timeOrderF : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕 :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  crAnTimeOrderSign φs • ofCrAnList (crAnTimeOrderList φs)

@[inherit_doc timeOrderF]
scoped[FieldSpecification.FieldOpFreeAlgebra] notation "𝓣ᶠ(" a ")" => timeOrderF a

lemma timeOrderF_ofCrAnList (φs : List 𝓕.CrAnStates) :
    𝓣ᶠ(ofCrAnList φs) = crAnTimeOrderSign φs • ofCrAnList (crAnTimeOrderList φs) := by
  rw [← ofListBasis_eq_ofList]
  simp only [timeOrderF, Basis.constr_basis]

lemma timeOrderF_timeOrderF_mid (a b c : 𝓕.FieldOpFreeAlgebra) : 𝓣ᶠ(a * b * c) = 𝓣ᶠ(a * 𝓣ᶠ(b) * c) := by
  let pc (c : 𝓕.FieldOpFreeAlgebra) (hc : c ∈ Submodule.span ℂ (Set.range ofCrAnListBasis)) :
    Prop := 𝓣ᶠ(a * b * c) = 𝓣ᶠ(a * 𝓣ᶠ(b) * c)
  change pc c (Basis.mem_span _ c)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl⟩ := hx
    simp only [ofListBasis_eq_ofList, pc]
    let pb (b : 𝓕.FieldOpFreeAlgebra) (hb : b ∈ Submodule.span ℂ (Set.range ofCrAnListBasis)) :
      Prop := 𝓣ᶠ(a * b * ofCrAnList φs) = 𝓣ᶠ(a * 𝓣ᶠ(b) * ofCrAnList φs)
    change pb b (Basis.mem_span _ b)
    apply Submodule.span_induction
    · intro x hx
      obtain ⟨φs', rfl⟩ := hx
      simp only [ofListBasis_eq_ofList, pb]
      let pa (a : 𝓕.FieldOpFreeAlgebra) (ha : a ∈ Submodule.span ℂ (Set.range ofCrAnListBasis)) :
        Prop := 𝓣ᶠ(a * ofCrAnList φs' * ofCrAnList φs) = 𝓣ᶠ(a * 𝓣ᶠ(ofCrAnList φs') * ofCrAnList φs)
      change pa a (Basis.mem_span _ a)
      apply Submodule.span_induction
      · intro x hx
        obtain ⟨φs'', rfl⟩ := hx
        simp only [ofListBasis_eq_ofList, pa]
        rw [timeOrderF_ofCrAnList]
        simp only [← ofCrAnList_append, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, map_smul]
        rw [timeOrderF_ofCrAnList, timeOrderF_ofCrAnList, smul_smul]
        congr 1
        · simp only [crAnTimeOrderSign, crAnTimeOrderList]
          rw [Wick.koszulSign_of_append_eq_insertionSort, mul_comm]
        · congr 1
          simp only [crAnTimeOrderList]
          rw [insertionSort_append_insertionSort_append]
      · simp [pa]
      · intro x y hx hy h1 h2
        simp_all [pa, add_mul]
      · intro x hx h
        simp_all [pa]
    · simp [pb]
    · intro x y hx hy h1 h2
      simp_all [pb, mul_add, add_mul]
    · intro x hx h
      simp_all [pb]
  · simp [pc]
  · intro x y hx hy h1 h2
    simp_all [pc, mul_add]
  · intro x hx h hp
    simp_all [pc]

lemma timeOrderF_timeOrderF_right (a b : 𝓕.FieldOpFreeAlgebra) : 𝓣ᶠ(a * b) = 𝓣ᶠ(a * 𝓣ᶠ(b)) := by
  trans 𝓣ᶠ(a * b * 1)
  · simp
  · rw [timeOrderF_timeOrderF_mid]
    simp

lemma timeOrderF_timeOrderF_left (a b : 𝓕.FieldOpFreeAlgebra) : 𝓣ᶠ(a * b) = 𝓣ᶠ(𝓣ᶠ(a) * b) := by
  trans 𝓣ᶠ(1 * a * b)
  · simp
  · rw [timeOrderF_timeOrderF_mid]
    simp

lemma timeOrderF_ofStateList (φs : List 𝓕.States) :
    𝓣ᶠ(ofStateList φs) = timeOrderSign φs • ofStateList (timeOrderList φs) := by
  conv_lhs =>
    rw [ofStateList_sum, map_sum]
    enter [2, x]
    rw [timeOrderF_ofCrAnList]
  simp only [crAnTimeOrderSign_crAnSection]
  rw [← Finset.smul_sum]
  congr
  rw [ofStateList_sum, sum_crAnSections_timeOrder]
  rfl

lemma timeOrderF_ofStateList_nil : timeOrderF (𝓕 := 𝓕) (ofStateList []) = 1 := by
  rw [timeOrderF_ofStateList]
  simp [timeOrderSign, Wick.koszulSign, timeOrderList]

@[simp]
lemma timeOrderF_ofStateList_singleton (φ : 𝓕.States) : 𝓣ᶠ(ofStateList [φ]) = ofStateList [φ] := by
  simp [timeOrderF_ofStateList, timeOrderSign, timeOrderList]

lemma timeOrderF_ofState_ofState_ordered {φ ψ : 𝓕.States} (h : timeOrderRel φ ψ) :
    𝓣ᶠ(ofState φ * ofState ψ) = ofState φ * ofState ψ := by
  rw [← ofStateList_singleton, ← ofStateList_singleton, ← ofStateList_append,
    timeOrderF_ofStateList]
  simp only [List.singleton_append]
  rw [timeOrderSign_pair_ordered h, timeOrderList_pair_ordered h]
  simp

lemma timeOrderF_ofState_ofState_not_ordered {φ ψ : 𝓕.States} (h : ¬ timeOrderRel φ ψ) :
    𝓣ᶠ(ofState φ * ofState ψ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • ofState ψ * ofState φ := by
  rw [← ofStateList_singleton, ← ofStateList_singleton,
    ← ofStateList_append, timeOrderF_ofStateList]
  simp only [List.singleton_append, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [timeOrderSign_pair_not_ordered h, timeOrderList_pair_not_ordered h]
  simp [← ofStateList_append]

lemma timeOrderF_ofState_ofState_not_ordered_eq_timeOrderF {φ ψ : 𝓕.States}
    (h : ¬ timeOrderRel φ ψ) :
    𝓣ᶠ(ofState φ * ofState ψ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • 𝓣ᶠ(ofState ψ * ofState φ) := by
  rw [timeOrderF_ofState_ofState_not_ordered h]
  rw [timeOrderF_ofState_ofState_ordered]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc]
  have hx := IsTotal.total (r := timeOrderRel) ψ φ
  simp_all

lemma timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel
    {φ ψ : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ ψ) :
    𝓣ᶠ([ofCrAnState φ, ofCrAnState ψ]ₛca) = 0 := by
  rw [superCommuteF_ofCrAnState_ofCrAnState]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc, map_sub, map_smul]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton,
    ← ofCrAnList_append, ← ofCrAnList_append, timeOrderF_ofCrAnList, timeOrderF_ofCrAnList]
  simp only [List.singleton_append]
  rw [crAnTimeOrderSign_pair_not_ordered h, crAnTimeOrderList_pair_not_ordered h]
  rw [sub_eq_zero, smul_smul]
  have h1 := IsTotal.total (r := crAnTimeOrderRel) φ ψ
  congr
  · rw [crAnTimeOrderSign_pair_ordered, exchangeSign_symm]
    simp only [instCommGroup.eq_1, mul_one]
    simp_all
  · rw [crAnTimeOrderList_pair_ordered]
    simp_all

lemma timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_right
    {φ ψ : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ ψ) (a : 𝓕.FieldOpFreeAlgebra) :
    𝓣ᶠ(a * [ofCrAnState φ, ofCrAnState ψ]ₛca) = 0 := by
  rw [timeOrderF_timeOrderF_right,
    timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel h]
  simp

lemma timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_left
    {φ ψ : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ ψ) (a : 𝓕.FieldOpFreeAlgebra) :
    𝓣ᶠ([ofCrAnState φ, ofCrAnState ψ]ₛca * a) = 0 := by
  rw [timeOrderF_timeOrderF_left,
    timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel h]
  simp

lemma timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_mid
    {φ ψ : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ ψ) (a b : 𝓕.FieldOpFreeAlgebra) :
    𝓣ᶠ(a * [ofCrAnState φ, ofCrAnState ψ]ₛca * b) = 0 := by
  rw [timeOrderF_timeOrderF_mid,
    timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel h]
  simp

lemma timeOrderF_superCommuteF_superCommuteF_ofCrAnState_not_crAnTimeOrderRel
    {φ1 φ2 : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ1 φ2) (a : 𝓕.FieldOpFreeAlgebra) :
    𝓣ᶠ([a, [ofCrAnState φ1, ofCrAnState φ2]ₛca]ₛca) = 0 := by
  rw [← bosonicProj_add_fermionicProj a]
  simp only [map_add, LinearMap.add_apply]
  rw [bosonic_superCommuteF (Submodule.coe_mem (bosonicProj a))]
  simp only [map_sub]
  rw [timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_left h]
  rw [timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_right h]
  simp only [sub_self, zero_add]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rcases superCommuteF_ofCrAnList_ofCrAnList_bosonic_or_fermionic [φ1] [φ2] with h' | h'
  · rw [superCommuteF_bonsonic h']
    simp only [ofCrAnList_singleton, map_sub]
    rw [timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_left h]
    rw [timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_right h]
    simp
  · rw [superCommuteF_fermionic_fermionic (Submodule.coe_mem (fermionicProj a)) h']
    simp only [ofCrAnList_singleton, map_add]
    rw [timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_left h]
    rw [timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_right h]
    simp

lemma timeOrderF_superCommuteF_ofCrAnState_superCommuteF_not_crAnTimeOrderRel
    {φ1 φ2 φ3 : 𝓕.CrAnStates} (h12 : ¬ crAnTimeOrderRel φ1 φ2)
    (h13 : ¬ crAnTimeOrderRel φ1 φ3) :
    𝓣ᶠ([ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca) = 0 := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rw [summerCommute_jacobi_ofCrAnList]
  simp only [instCommGroup.eq_1, ofList_singleton, ofCrAnList_singleton, neg_smul, map_smul,
    map_sub, map_neg, smul_eq_zero]
  right
  rw [timeOrderF_superCommuteF_superCommuteF_ofCrAnState_not_crAnTimeOrderRel h12]
  rw [superCommuteF_ofCrAnState_ofCrAnState_symm φ3]
  simp only [smul_zero, neg_zero, instCommGroup.eq_1, neg_smul, map_neg, map_smul, smul_neg,
    sub_neg_eq_add, zero_add, smul_eq_zero]
  rw [timeOrderF_superCommuteF_superCommuteF_ofCrAnState_not_crAnTimeOrderRel h13]
  simp

lemma timeOrderF_superCommuteF_ofCrAnState_superCommuteF_not_crAnTimeOrderRel'
    {φ1 φ2 φ3 : 𝓕.CrAnStates} (h12 : ¬ crAnTimeOrderRel φ2 φ1)
    (h13 : ¬ crAnTimeOrderRel φ3 φ1) :
    𝓣ᶠ([ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca) = 0 := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rw [summerCommute_jacobi_ofCrAnList]
  simp only [instCommGroup.eq_1, ofList_singleton, ofCrAnList_singleton, neg_smul, map_smul,
    map_sub, map_neg, smul_eq_zero]
  right
  rw [superCommuteF_ofCrAnState_ofCrAnState_symm φ1]
  simp only [instCommGroup.eq_1, neg_smul, map_neg, map_smul, smul_neg, neg_neg]
  rw [timeOrderF_superCommuteF_superCommuteF_ofCrAnState_not_crAnTimeOrderRel h12]
  simp only [smul_zero, zero_sub, neg_eq_zero, smul_eq_zero]
  rw [timeOrderF_superCommuteF_superCommuteF_ofCrAnState_not_crAnTimeOrderRel h13]
  simp

lemma timeOrderF_superCommuteF_ofCrAnState_superCommuteF_all_not_crAnTimeOrderRel
    (φ1 φ2 φ3 : 𝓕.CrAnStates) (h : ¬
      (crAnTimeOrderRel φ1 φ2 ∧ crAnTimeOrderRel φ1 φ3 ∧
      crAnTimeOrderRel φ2 φ1 ∧ crAnTimeOrderRel φ2 φ3 ∧
      crAnTimeOrderRel φ3 φ1 ∧ crAnTimeOrderRel φ3 φ2)) :
    𝓣ᶠ([ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca) = 0 := by
  simp only [not_and] at h
  by_cases h23 : ¬ crAnTimeOrderRel φ2 φ3
  · simp_all only [IsEmpty.forall_iff, implies_true]
    rw [timeOrderF_superCommuteF_superCommuteF_ofCrAnState_not_crAnTimeOrderRel h23]
  simp_all only [Decidable.not_not, forall_const]
  by_cases h32 : ¬ crAnTimeOrderRel φ3 φ2
  · simp_all only [not_false_eq_true, implies_true]
    rw [superCommuteF_ofCrAnState_ofCrAnState_symm]
    simp only [instCommGroup.eq_1, neg_smul, map_neg, map_smul, neg_eq_zero, smul_eq_zero]
    rw [timeOrderF_superCommuteF_superCommuteF_ofCrAnState_not_crAnTimeOrderRel h32]
    simp
  simp_all only [imp_false, Decidable.not_not]
  by_cases h12 : ¬ crAnTimeOrderRel φ1 φ2
  · have h13 : ¬ crAnTimeOrderRel φ1 φ3 := by
      intro h13
      apply h12
      exact IsTrans.trans φ1 φ3 φ2 h13 h32
    rw [timeOrderF_superCommuteF_ofCrAnState_superCommuteF_not_crAnTimeOrderRel h12 h13]
  simp_all only [Decidable.not_not, forall_const]
  have h13 : crAnTimeOrderRel φ1 φ3 := IsTrans.trans φ1 φ2 φ3 h12 h23
  simp_all only [forall_const]
  by_cases h21 : ¬ crAnTimeOrderRel φ2 φ1
  · simp_all only [IsEmpty.forall_iff]
    have h31 : ¬ crAnTimeOrderRel φ3 φ1 := by
      intro h31
      apply h21
      exact IsTrans.trans φ2 φ3 φ1 h23 h31
    rw [timeOrderF_superCommuteF_ofCrAnState_superCommuteF_not_crAnTimeOrderRel' h21 h31]
  simp_all only [Decidable.not_not, forall_const]
  refine False.elim (h ?_)
  exact IsTrans.trans φ3 φ2 φ1 h32 h21

lemma timeOrderF_superCommuteF_ofCrAnState_ofCrAnState_eq_time
    {φ ψ : 𝓕.CrAnStates} (h1 : crAnTimeOrderRel φ ψ) (h2 : crAnTimeOrderRel ψ φ) :
    𝓣ᶠ([ofCrAnState φ, ofCrAnState ψ]ₛca) = [ofCrAnState φ, ofCrAnState ψ]ₛca := by
  rw [superCommuteF_ofCrAnState_ofCrAnState]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc, map_sub, map_smul]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton,
    ← ofCrAnList_append, ← ofCrAnList_append, timeOrderF_ofCrAnList, timeOrderF_ofCrAnList]
  simp only [List.singleton_append]
  rw [crAnTimeOrderSign_pair_ordered h1, crAnTimeOrderList_pair_ordered h1,
    crAnTimeOrderSign_pair_ordered h2, crAnTimeOrderList_pair_ordered h2]
  simp

/-!

## Interaction with maxTimeField

-/

/-- In the state algebra time, ordering obeys `T(φ₀φ₁…φₙ) = s * φᵢ * T(φ₀φ₁…φᵢ₋₁φᵢ₊₁…φₙ)`
  where `φᵢ` is the state
  which has maximum time and `s` is the exchange sign of `φᵢ` and `φ₀φ₁…φᵢ₋₁`. -/
lemma timeOrderF_eq_maxTimeField_mul (φ : 𝓕.States) (φs : List 𝓕.States) :
    𝓣ᶠ(ofStateList (φ :: φs)) =
    𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ (φ :: φs).take (maxTimeFieldPos φ φs)) •
    ofState (maxTimeField φ φs) * 𝓣ᶠ(ofStateList (eraseMaxTimeField φ φs)) := by
  rw [timeOrderF_ofStateList, timeOrderList_eq_maxTimeField_timeOrderList]
  rw [ofStateList_cons, timeOrderF_ofStateList]
  simp only [instCommGroup.eq_1, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  congr
  rw [timerOrderSign_of_eraseMaxTimeField, mul_assoc]
  simp

/-- In the state algebra time, ordering obeys `T(φ₀φ₁…φₙ) = s * φᵢ * T(φ₀φ₁…φᵢ₋₁φᵢ₊₁…φₙ)`
  where `φᵢ` is the state
  which has maximum time and `s` is the exchange sign of `φᵢ` and `φ₀φ₁…φᵢ₋₁`.
  Here `s` is written using finite sets. -/
lemma timeOrderF_eq_maxTimeField_mul_finset (φ : 𝓕.States) (φs : List 𝓕.States) :
    𝓣ᶠ(ofStateList (φ :: φs)) = 𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ ⟨(eraseMaxTimeField φ φs).get,
      (Finset.filter (fun x =>
        (maxTimeFieldPosFin φ φs).succAbove x < maxTimeFieldPosFin φ φs) Finset.univ)⟩) •
      ofState (maxTimeField φ φs) * 𝓣ᶠ(ofStateList (eraseMaxTimeField φ φs)) := by
  rw [timeOrderF_eq_maxTimeField_mul]
  congr 3
  apply FieldStatistic.ofList_perm
  nth_rewrite 1 [← List.finRange_map_get (φ :: φs)]
  simp only [List.length_cons, eraseMaxTimeField, insertionSortDropMinPos]
  rw [eraseIdx_get, ← List.map_take, ← List.map_map]
  refine List.Perm.map (φ :: φs).get ?_
  apply (List.perm_ext_iff_of_nodup _ _).mpr
  · intro i
    simp only [List.length_cons, maxTimeFieldPos, mem_take_finrange, Fin.val_fin_lt, List.mem_map,
      Finset.mem_sort, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    refine Iff.intro (fun hi => ?_) (fun h => ?_)
    · have h2 := (maxTimeFieldPosFin φ φs).2
      simp only [eraseMaxTimeField, insertionSortDropMinPos, List.length_cons, Nat.succ_eq_add_one,
        maxTimeFieldPosFin, insertionSortMinPosFin] at h2
      use ⟨i, by omega⟩
      apply And.intro
      · simp only [Fin.succAbove, List.length_cons, Fin.castSucc_mk, maxTimeFieldPosFin,
        insertionSortMinPosFin, Nat.succ_eq_add_one, Fin.mk_lt_mk, Fin.val_fin_lt, Fin.succ_mk]
        rw [Fin.lt_def]
        split
        · simp only [Fin.val_fin_lt]
          omega
        · omega
      · simp only [Fin.succAbove, List.length_cons, Fin.castSucc_mk, Fin.succ_mk, Fin.ext_iff,
        Fin.coe_cast]
        split
        · simp
        · simp_all [Fin.lt_def]
    · obtain ⟨j, h1, h2⟩ := h
      subst h2
      simp only [Fin.lt_def, Fin.coe_cast]
      exact h1
  · exact List.Sublist.nodup (List.take_sublist _ _) <|
      List.nodup_finRange (φs.length + 1)
  · refine List.Nodup.map ?_ ?_
    · refine Function.Injective.comp ?hf.hg Fin.succAbove_right_injective
      exact Fin.cast_injective (eraseIdx_length (φ :: φs) (insertionSortMinPos timeOrderRel φ φs))
    · exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2)
        (Finset.filter (fun x => (maxTimeFieldPosFin φ φs).succAbove x < maxTimeFieldPosFin φ φs)
          Finset.univ)

end

end FieldOpFreeAlgebra

end FieldSpecification
