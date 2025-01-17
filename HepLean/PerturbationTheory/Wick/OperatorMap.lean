/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.SuperCommute
/-!

# Operator map

-/
namespace Wick

noncomputable section

open FieldStatistic

variable {𝓕 : Type}

/-- A map from the free algebra of fields `FreeAlgebra ℂ 𝓕` to an algebra `A`, to be
  thought of as the operator algebra is said to be an operator map if
  all super commutors of fields land in the center of `A`,
  if two fields are of a different grade then their super commutor lands on zero,
  and the `koszulOrder` (normal order) of any term with a super commutor of two fields present
  is zero.
  This can be thought as as a condition on the operator algebra `A` as much as it can
  on `F`. -/
class OperatorMap {A : Type} [Semiring A] [Algebra ℂ A]
    (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop)
    [DecidableRel le] (F : FreeAlgebra ℂ 𝓕 →ₐ[ℂ] A) : Prop where
  superCommute_mem_center : ∀ i j, F (superCommute q (FreeAlgebra.ι ℂ i) (FreeAlgebra.ι ℂ j)) ∈
    Subalgebra.center ℂ A
  superCommute_diff_grade_zero : ∀ i j, q i ≠ q j →
    F (superCommute q (FreeAlgebra.ι ℂ i) (FreeAlgebra.ι ℂ j)) = 0
  superCommute_ordered_zero : ∀ i j, ∀ a b,
    F (koszulOrder q le (a * superCommute q (FreeAlgebra.ι ℂ i) (FreeAlgebra.ι ℂ j) * b)) = 0

namespace OperatorMap

variable {A : Type} [Semiring A] [Algebra ℂ A]
  {q : 𝓕 → FieldStatistic} {le : 𝓕 → 𝓕 → Prop}
  [DecidableRel le] (F : FreeAlgebra ℂ 𝓕 →ₐ[ℂ] A)

lemma superCommute_ofList_singleton_ι_center [OperatorMap q le F] (i j : 𝓕) :
    F (superCommute q (ofList [i] xa) (FreeAlgebra.ι ℂ j)) ∈ Subalgebra.center ℂ A := by
  have h1 : F (superCommute q (ofList [i] xa) (FreeAlgebra.ι ℂ j)) =
      xa • F (superCommute q (FreeAlgebra.ι ℂ i) (FreeAlgebra.ι ℂ j)) := by
    rw [← map_smul]
    congr
    rw [ofList_eq_smul_one, ofList_singleton]
    rw [map_smul]
    rfl
  rw [h1]
  refine Subalgebra.smul_mem (Subalgebra.center ℂ A) ?_ xa
  exact superCommute_mem_center (le := le) i j

end OperatorMap

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

lemma superCommuteSplit_operatorMap (lb : List 𝓕) (xa xb : ℂ) (n : ℕ)
    (hn : n < lb.length) {A : Type} [Semiring A] [Algebra ℂ A] (f : FreeAlgebra ℂ 𝓕 →ₐ[ℂ] A)
    [OperatorMap q le f] (i : 𝓕) :
    f (superCommuteSplit q [i] lb xa xb n hn) =
    f (superCommute q (ofList [i] xa) (FreeAlgebra.ι ℂ (lb.get ⟨n, hn⟩)))
    * (superCommuteCoef q [i] (List.take n lb) •
    f (ofList (List.eraseIdx lb n) xb)) := by
  have hn : f ((superCommute q) (ofList [i] xa) (FreeAlgebra.ι ℂ (lb.get ⟨n, hn⟩))) ∈
      Subalgebra.center ℂ A :=
    OperatorMap.superCommute_ofList_singleton_ι_center (le := le) f i (lb.get ⟨n, hn⟩)
  rw [Subalgebra.mem_center_iff] at hn
  rw [superCommuteSplit, map_mul, map_mul, map_smul, hn, mul_assoc, smul_mul_assoc,
    ← map_mul, ← ofList_pair]
  congr
  · exact Eq.symm (List.eraseIdx_eq_take_drop_succ lb n)
  · exact one_mul xb

lemma superCommuteLiftSplit_operatorMap {f : 𝓕 → Type} [∀ i, Fintype (f i)]
    (c : (Σ i, f i)) (r : List 𝓕) (x y : ℂ) (n : ℕ)
    (hn : n < r.length)
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le]
    {A : Type} [Semiring A] [Algebra ℂ A] (F : FreeAlgebra ℂ (Σ i, f i) →ₐ[ℂ] A)
    [OperatorMap (fun i => q i.1) le F] :
    F (superCommuteLiftSplit q [c] r x y n hn) = superCommuteLiftCoef q [c] (List.take n r) •
    (F (superCommute (fun i => q i.1) (ofList [c] x)
    (sumFiber f (FreeAlgebra.ι ℂ (r.get ⟨n, hn⟩))))
    * F (ofListLift f (List.eraseIdx r n) y)) := by
  rw [superCommuteLiftSplit]
  rw [map_smul]
  congr
  rw [map_mul, map_mul]
  have h1 : F ((superCommute fun i => q i.fst) (ofList [c] x) ((sumFiber f)
    (FreeAlgebra.ι ℂ (r.get ⟨n, hn⟩)))) ∈ Subalgebra.center ℂ A := by
      rw [sumFiber_ι]
      rw [map_sum, map_sum]
      refine Subalgebra.sum_mem _ ?_
      intro n
      exact fun a => OperatorMap.superCommute_ofList_singleton_ι_center (le := le) F c _
  rw [Subalgebra.mem_center_iff] at h1
  rw [h1, mul_assoc, ← map_mul]
  congr
  rw [ofListLift, ofListLift, ofListLift, ← map_mul]
  congr
  rw [← ofList_pair, one_mul]
  congr
  exact Eq.symm (List.eraseIdx_eq_take_drop_succ r n)

lemma superCommute_koszulOrder_le_ofList [IsTotal 𝓕 le] [IsTrans 𝓕 le] (r : List 𝓕) (x : ℂ)
    (i : 𝓕) {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ 𝓕 →ₐ A) [OperatorMap q le F] :
    F ((superCommute q (FreeAlgebra.ι ℂ i) (koszulOrder q le (ofList r x)))) =
    ∑ n : Fin r.length, (superCommuteCoef q [r.get n] (r.take n)) •
    (F (((superCommute q) (ofList [i] 1)) (FreeAlgebra.ι ℂ (r.get n))) *
    F ((koszulOrder q le) (ofList (r.eraseIdx ↑n) x))) := by
  rw [koszulOrder_ofList, map_smul, map_smul, ← ofList_singleton, superCommute_ofList_sum]
  rw [map_sum, ← (HepLean.List.insertionSortEquiv le r).sum_comp]
  conv_lhs =>
    enter [2, 2]
    intro n
    rw [superCommuteSplit_operatorMap (le := le)]
    enter [1, 2, 2, 2]
    change ((List.insertionSort le r).get ∘ (HepLean.List.insertionSortEquiv le r)) n
    rw [HepLean.List.insertionSort_get_comp_insertionSortEquiv]
  conv_lhs =>
    enter [2, 2]
    intro n
    rw [HepLean.List.eraseIdx_insertionSort_fin le r n]
    rw [ofList_insertionSort_eq_koszulOrder q le]
  rw [Finset.smul_sum]
  conv_lhs =>
    rhs
    intro n
    rw [map_smul, smul_smul, Algebra.mul_smul_comm, smul_smul]
  congr
  funext n
  by_cases hq : q i ≠ q (r.get n)
  · have hn := OperatorMap.superCommute_diff_grade_zero (q := q) (F := F) le i (r.get n) hq
    conv_lhs =>
      enter [2, 1]
      rw [ofList_singleton, hn]
    conv_rhs =>
      enter [2, 1]
      rw [ofList_singleton, hn]
    simp
  · congr 1
    trans staticWickCoef q le r i n
    · rw [staticWickCoef, mul_assoc]
    refine staticWickCoef_eq_get q le r i n ?_
    simpa using hq

lemma koszulOrder_of_le_all_ofList (r : List 𝓕) (x : ℂ) (i : 𝓕)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ 𝓕 →ₐ A) [OperatorMap q le F] :
    F (koszulOrder q le (ofList r x * FreeAlgebra.ι ℂ i))
    = superCommuteCoef q [i] r • F (koszulOrder q le (FreeAlgebra.ι ℂ i * ofList r x)) := by
  conv_lhs =>
    enter [2, 2]
    rw [← ofList_singleton]
    rw [ofListLift_ofList_superCommute' q]
  rw [map_sub]
  rw [sub_eq_add_neg]
  rw [map_add]
  conv_lhs =>
    enter [2, 2]
    rw [map_smul]
    rw [← neg_smul]
  rw [map_smul, map_smul, map_smul]
  conv_lhs =>
    rhs
    rhs
    rw [superCommute_ofList_sum]
    rw [map_sum, map_sum]
    dsimp [superCommuteSplit]
    rw [ofList_singleton]
    rhs
    intro n
    rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc]
    rw [map_smul, map_smul]
    rw [OperatorMap.superCommute_ordered_zero]
  simp only [smul_zero, Finset.sum_const_zero, add_zero]
  rw [ofList_singleton]

lemma le_all_mul_koszulOrder_ofList (r : List 𝓕) (x : ℂ)
    (i : 𝓕) (hi : ∀ (j : 𝓕), le j i)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ 𝓕 →ₐ A) [OperatorMap q le F] :
    F (FreeAlgebra.ι ℂ i * koszulOrder q le (ofList r x)) =
    F ((koszulOrder q le) (FreeAlgebra.ι ℂ i * ofList r x)) +
    F (((superCommute q) (ofList [i] 1)) ((koszulOrder q le) (ofList r x))) := by
  rw [koszulOrder_ofList, Algebra.mul_smul_comm, map_smul, ← ofList_singleton,
    ofList_ofList_superCommute q, map_add, smul_add, ← map_smul]
  conv_lhs =>
    enter [1, 2]
    rw [← Algebra.smul_mul_assoc, smul_smul, mul_comm, ← smul_smul, ← koszulOrder_ofList,
      Algebra.smul_mul_assoc, ofList_singleton]
  rw [koszulOrder_mul_ge, map_smul]
  congr
  · rw [koszulOrder_of_le_all_ofList]
    rw [superCommuteCoef_perm_snd q [i] (List.insertionSort le r) r
      (List.perm_insertionSort le r)]
    rw [smul_smul]
    rw [superCommuteCoef_mul_self]
    simp [ofList_singleton]
  · rw [map_smul, map_smul]
  · exact fun j => hi j

/-- In the expansions of `F (FreeAlgebra.ι ℂ i * koszulOrder q le (ofList r x))`
  the ter multiplying `F ((koszulOrder q le) (ofList (optionEraseZ r i n) x))`. -/
def superCommuteCenterOrder (r : List 𝓕) (i : 𝓕)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ 𝓕 →ₐ[ℂ] A)
    (n : Option (Fin r.length)) : A :=
  match n with
  | none => 1
  | some n => superCommuteCoef q [r.get n] (r.take n) • F (((superCommute q) (ofList [i] 1))
    (FreeAlgebra.ι ℂ (r.get n)))

@[simp]
lemma superCommuteCenterOrder_none (r : List 𝓕) (i : 𝓕)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ 𝓕 →ₐ[ℂ] A) :
    superCommuteCenterOrder q r i F none = 1 := by
  simp [superCommuteCenterOrder]

open HepLean.List

lemma le_all_mul_koszulOrder_ofList_expand [IsTotal 𝓕 le] [IsTrans 𝓕 le] (r : List 𝓕) (x : ℂ)
    (i : 𝓕) (hi : ∀ (j : 𝓕), le j i)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ 𝓕 →ₐ[ℂ] A) [OperatorMap q le F] :
    F (FreeAlgebra.ι ℂ i * koszulOrder q le (ofList r x)) =
    ∑ n, superCommuteCenterOrder q r i F n *
    F ((koszulOrder q le) (ofList (optionEraseZ r i n) x)) := by
  rw [le_all_mul_koszulOrder_ofList]
  conv_lhs =>
    rhs
    rw [ofList_singleton]
  rw [superCommute_koszulOrder_le_ofList]
  simp only [List.get_eq_getElem, Fintype.sum_option, superCommuteCenterOrder_none, one_mul]
  congr
  · rw [← ofList_singleton, ← ofList_pair]
    simp only [List.singleton_append, one_mul]
    rfl
  · funext n
    simp only [superCommuteCenterOrder, List.get_eq_getElem, Algebra.smul_mul_assoc]
    rfl
  exact fun j => hi j

lemma le_all_mul_koszulOrder_ofListLift_expand {f : 𝓕 → Type} [∀ i, Fintype (f i)]
    (r : List 𝓕) (x : ℂ)
    (le : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le]
    [IsTotal (Σ i, f i) le] [IsTrans (Σ i, f i) le]
    (i : (Σ i, f i)) (hi : ∀ (j : (Σ i, f i)), le j i)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [OperatorMap (fun i => q i.1) le F] :
    F (ofList [i] 1 * koszulOrder (fun i => q i.1) le (ofListLift f r x)) =
    F ((koszulOrder (fun i => q i.fst) le) (ofList [i] 1 * ofListLift f r x)) +
    ∑ n : (Fin r.length), superCommuteCoef q [r.get n] (List.take (↑n) r) •
      F (((superCommute fun i => q i.fst) (ofList [i] 1)) (ofListLift f [r.get n] 1)) *
    F ((koszulOrder (fun i => q i.fst) le) (ofListLift f (r.eraseIdx ↑n) x)) := by
  match r with
  | [] =>
    simp only [map_mul, List.length_nil, Finset.univ_eq_empty, List.get_eq_getElem, List.take_nil,
      List.eraseIdx_nil, Algebra.smul_mul_assoc, Finset.sum_empty, add_zero]
    rw [ofListLift_empty_smul]
    simp only [map_smul, koszulOrder_one, map_one, Algebra.mul_smul_comm, mul_one]
    rw [ofList_singleton, koszulOrder_ι]
  | r0 :: r =>
  rw [ofListLift_expand, map_sum, Finset.mul_sum, map_sum]
  let e1 (a : CreateAnnihilateSect f (r0 :: r)) :
        Option (Fin a.toList.length) ≃ Option (Fin (r0 :: r).length) :=
      Equiv.optionCongr (Fin.castOrderIso (CreateAnnihilateSect.toList_length a)).toEquiv
  conv_lhs =>
    rhs
    intro a
    rw [ofList_singleton, le_all_mul_koszulOrder_ofList_expand _ _ _ _ _ hi]
    rw [← (e1 a).symm.sum_comp]
    rhs
    intro n
  rw [Finset.sum_comm]
  simp only [Fintype.sum_option]
  congr 1
  · simp only [List.length_cons, List.get_eq_getElem, superCommuteCenterOrder,
    Equiv.optionCongr_symm, OrderIso.toEquiv_symm, Fin.symm_castOrderIso, Equiv.optionCongr_apply,
    RelIso.coe_fn_toEquiv, Option.map_none', optionEraseZ, one_mul, e1]
    rw [← map_sum, Finset.mul_sum, ← map_sum]
    apply congrArg
    apply congrArg
    congr
    funext x
    rw [ofList_cons_eq_ofList]
  · congr
    funext n
    rw [← (CreateAnnihilateSect.extractEquiv n).symm.sum_comp]
    simp only [List.get_eq_getElem, List.length_cons, Equiv.optionCongr_symm, OrderIso.toEquiv_symm,
      Fin.symm_castOrderIso, Equiv.optionCongr_apply, RelIso.coe_fn_toEquiv, Option.map_some',
      Fin.castOrderIso_apply, Algebra.smul_mul_assoc, e1]
    erw [Finset.sum_product]
    have h1 (a0 : f (r0 :: r)[↑n]) (a : CreateAnnihilateSect f ((r0 :: r).eraseIdx ↑n)) :
      superCommuteCenterOrder (fun i => q i.fst)
        ((CreateAnnihilateSect.extractEquiv n).symm (a0, a)).toList i F
      (some (Fin.cast (by simp) n)) =
      superCommuteCoef q [(r0 :: r).get n] (List.take (↑n) (r0 :: r)) •
      F (((superCommute fun i => q i.fst) (ofList [i] 1))
      (FreeAlgebra.ι ℂ ⟨(r0 :: r).get n, a0⟩)) := by
      simp only [superCommuteCenterOrder, List.get_eq_getElem, List.length_cons, Fin.coe_cast]
      erw [CreateAnnihilateSect.extractEquiv_symm_toList_get_same]
      have hsc : superCommuteCoef (fun i => q i.fst) [⟨(r0 :: r).get n, a0⟩]
        (List.take (↑n) ((CreateAnnihilateSect.extractEquiv n).symm (a0, a)).toList) =
        superCommuteCoef q [(r0 :: r).get n] (List.take (↑n) ((r0 :: r))) := by
        simp only [superCommuteCoef, List.get_eq_getElem, List.length_cons, Fin.isValue,
          CreateAnnihilateSect.toList_grade_take]
        rfl
      erw [hsc]
      rfl
    conv_lhs =>
      rhs
      intro a0
      rhs
      intro a
      erw [h1]
    conv_lhs =>
      rhs
      intro a0
      rw [← Finset.mul_sum]
    conv_lhs =>
      rhs
      intro a0
      enter [2, 2]
      intro a
      simp [optionEraseZ]
      enter [2, 2, 1]
      rw [← CreateAnnihilateSect.eraseIdx_toList]
      erw [CreateAnnihilateSect.extractEquiv_symm_eraseIdx]
    rw [← Finset.sum_mul]
    conv_lhs =>
      lhs
      rw [← Finset.smul_sum]
      erw [← map_sum, ← map_sum, ← ofListLift_singleton_one]
    conv_lhs =>
      rhs
      rw [← map_sum, ← map_sum]
      simp only [List.get_eq_getElem, List.length_cons, Equiv.symm_apply_apply,
        Algebra.smul_mul_assoc]
      erw [← ofListLift_expand]
    simp only [List.get_eq_getElem, List.length_cons, Algebra.smul_mul_assoc]

end
end Wick
