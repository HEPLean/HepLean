/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Koszul.OfList
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

noncomputable section

def superCommuteMonoidAlgebra {I : Type} (q : I → Fin 2) (l : List I) :
    MonoidAlgebra ℂ (FreeMonoid I) →ₗ[ℂ] MonoidAlgebra ℂ (FreeMonoid I) :=
  Finsupp.lift (MonoidAlgebra ℂ (FreeMonoid I)) ℂ (List I)
    (fun r =>
      Finsupp.lsingle (R := ℂ) (l ++ r) 1 +
      if grade q l = 1 ∧ grade q r = 1 then
        Finsupp.lsingle (R := ℂ) (r ++ l) 1
      else
        - Finsupp.lsingle (R := ℂ) (r ++ l) 1)

def superCommuteAlgebra {I : Type} (q : I → Fin 2) :
    MonoidAlgebra ℂ (FreeMonoid I) →ₗ[ℂ] FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I :=
  Finsupp.lift (FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I) ℂ (List I) fun l =>
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toAlgHom.toLinearMap
    ∘ₗ superCommuteMonoidAlgebra q l
    ∘ₗ FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom.toLinearMap)

def superCommute {I : Type} (q : I → Fin 2) :
    FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I :=
  superCommuteAlgebra q
  ∘ₗ FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom.toLinearMap

lemma equivMonoidAlgebraFreeMonoid_freeAlgebra {I : Type} (i : I) :
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (FreeAlgebra.ι ℂ i)) =
    Finsupp.single (FreeMonoid.of i) 1 := by
  simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.single]

@[simp]
lemma superCommute_ι {I : Type} (q : I → Fin 2) (i j : I) :
    superCommute q (FreeAlgebra.ι ℂ i) (FreeAlgebra.ι ℂ j) =
    FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j +
    if q i = 1 ∧ q j = 1 then
      FreeAlgebra.ι ℂ j * FreeAlgebra.ι ℂ i
    else
      - FreeAlgebra.ι ℂ j * FreeAlgebra.ι ℂ i := by
  simp only [superCommute, superCommuteAlgebra, AlgEquiv.toAlgHom_eq_coe,
    AlgEquiv.toAlgHom_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, equivMonoidAlgebraFreeMonoid_freeAlgebra, Fin.isValue, neg_mul]
  erw [Finsupp.lift_apply]
  simp only [superCommuteMonoidAlgebra, Finsupp.lsingle_apply, Fin.isValue, grade_freeMonoid,
    zero_smul, Finsupp.sum_single_index, one_smul, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, equivMonoidAlgebraFreeMonoid_freeAlgebra]
  conv_lhs =>
    rhs
    erw [Finsupp.lift_apply]
  simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply, Fin.isValue,
    smul_add, MonoidAlgebra.smul_single', mul_one, smul_ite, smul_neg, Finsupp.sum_add,
    Finsupp.single_zero, Finsupp.sum_single_index, grade_freeMonoid, neg_zero, ite_self,
    AlgEquiv.ofAlgHom_symm_apply, map_add, MonoidAlgebra.lift_single, one_smul]
  congr
  by_cases hq : q i = 1 ∧ q j = 1
  · rw [if_pos hq, if_pos hq]
    simp only [MonoidAlgebra.lift_single, one_smul]
    obtain ⟨left, right⟩ := hq
    rfl
  · rw [if_neg hq, if_neg hq]
    simp only [map_neg, MonoidAlgebra.lift_single, one_smul, neg_inj]
    rfl

lemma superCommute_ofList_ofList {I : Type} (q : I → Fin 2) (l r : List I) (x y : ℂ) :
    superCommute q (ofList l x) (ofList r y) =
    ofList (l ++ r) (x * y) + (if grade q l = 1 ∧ grade q r = 1 then
    ofList (r ++ l) (y * x) else - ofList (r ++ l) (y * x)) := by
  simp only [superCommute, superCommuteAlgebra, AlgEquiv.toAlgHom_eq_coe,
    AlgEquiv.toAlgHom_toLinearMap, ofList, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply, Fin.isValue]
  erw [Finsupp.lift_apply]
  simp only [superCommuteMonoidAlgebra, Finsupp.lsingle_apply, Fin.isValue, zero_smul,
    Finsupp.sum_single_index, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply]
  conv_lhs =>
    rhs
    rhs
    erw [Finsupp.lift_apply]
  simp only [Fin.isValue, smul_add, MonoidAlgebra.smul_single', mul_one, smul_ite, smul_neg,
    Finsupp.sum_add, Finsupp.single_zero, Finsupp.sum_single_index, neg_zero, ite_self, map_add]
  by_cases hg : grade q l = 1 ∧ grade q r = 1
  · simp only [hg, Fin.isValue, and_self, ↓reduceIte]
    congr
    · rw [← map_smul]
      congr
      exact MonoidAlgebra.smul_single' x (l ++ r) y
    · rw [← map_smul]
      congr
      rw [mul_comm]
      exact MonoidAlgebra.smul_single' x (r ++ l) y
  · simp only [Fin.isValue, hg, ↓reduceIte, map_neg, smul_neg]
    congr
    · rw [← map_smul]
      congr
      exact MonoidAlgebra.smul_single' x (l ++ r) y
    · rw [← map_smul]
      congr
      rw [mul_comm]
      exact MonoidAlgebra.smul_single' x (r ++ l) y

@[simp]
lemma superCommute_zero {I : Type} (q : I → Fin 2) (a : FreeAlgebra ℂ I) :
    superCommute q a 0 = 0 := by
  simp [superCommute]

@[simp]
lemma superCommute_one {I : Type} (q : I → Fin 2) (a : FreeAlgebra ℂ I) :
    superCommute q a 1 = 0 := by
  let f : FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I := (LinearMap.flip (superCommute q)) 1
  have h1 : FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single [] 1) =
      (1 : FreeAlgebra ℂ I) := by
    simp_all only [EmbeddingLike.map_eq_one_iff]
    rfl
  have f_single (l : FreeMonoid I) (x : ℂ) :
      f ((FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x)))
      = 0 := by
    simp only [superCommute, superCommuteAlgebra, AlgEquiv.toAlgHom_eq_coe,
      AlgEquiv.toAlgHom_toLinearMap, LinearMap.flip_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply, f]
    rw [← h1]
    erw [Finsupp.lift_apply]
    simp only [superCommuteMonoidAlgebra, Finsupp.lsingle_apply, Fin.isValue, zero_smul,
      Finsupp.sum_single_index, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply, smul_eq_zero,
      EmbeddingLike.map_eq_zero_iff]
    apply Or.inr
    conv_lhs =>
      erw [Finsupp.lift_apply]
    simp
  have hf : f = 0 := by
    let e : FreeAlgebra ℂ I ≃ₗ[ℂ] MonoidAlgebra ℂ (FreeMonoid I) :=
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv
    apply (LinearEquiv.eq_comp_toLinearMap_iff (e₁₂ := e.symm) _ _).mp
    apply MonoidAlgebra.lhom_ext'
    intro l
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      MonoidAlgebra.lsingle_apply, LinearMap.zero_comp, LinearMap.zero_apply]
    erw [f_single]
  change f a = _
  rw [hf]
  simp

lemma superCommute_ofList_mul {I : Type} (q : I → Fin 2) (la lb lc : List I) (xa xb xc : ℂ) :
    superCommute q (ofList la xa) (ofList lb xb * ofList lc xc) =
    (superCommute q (ofList la xa) (ofList lb xb) * ofList lc xc +
    superCommuteCoef q la lb • ofList lb xb * superCommute q (ofList la xa) (ofList lc xc)) := by
  simp only [Algebra.smul_mul_assoc]
  conv_lhs => rw [← ofList_pair]
  simp only [superCommute_ofList_ofList, Fin.isValue, grade_append, ite_eq_right_iff, zero_ne_one,
    imp_false]
  simp only [superCommute_ofList_ofList, Fin.isValue, grade_append, ite_eq_right_iff, zero_ne_one,
    imp_false, ofList_triple_assoc, ofList_triple, ofList_pair, superCommuteCoef]
  by_cases hla : grade q la = 1
  · simp only [hla, Fin.isValue, true_and, ite_not, ite_smul, neg_smul, one_smul]
    by_cases hlb : grade q lb = 1
    · simp only [hlb, Fin.isValue, ↓reduceIte]
      by_cases hlc : grade q lc = 1
      · simp only [Fin.isValue, hlc, ↓reduceIte]
        simp only [mul_assoc, add_mul, mul_add]
        abel
      · have hc : grade q lc = 0 := by
          omega
        simp only [Fin.isValue, hc, one_ne_zero, ↓reduceIte, zero_ne_one]
        simp only [mul_assoc, add_mul, mul_add, mul_neg, neg_add_rev, neg_neg]
        abel
    · have hb : grade q lb = 0 := by
        omega
      simp only [hb, Fin.isValue, zero_ne_one, ↓reduceIte]
      by_cases hlc : grade q lc = 1
      · simp only [Fin.isValue, hlc, zero_ne_one, ↓reduceIte]
        simp only [mul_assoc, add_mul, neg_mul, mul_add]
        abel
      · have hc : grade q lc = 0 := by
          omega
        simp only [Fin.isValue, hc, ↓reduceIte, zero_ne_one]
        simp only [mul_assoc, add_mul, neg_mul, mul_add, mul_neg]
        abel
  · simp only [Fin.isValue, hla, false_and, ↓reduceIte, mul_assoc, add_mul, neg_mul, mul_add,
    mul_neg, smul_add, one_smul, smul_neg]
    abel

def superCommuteTake {I : Type} (q : I → Fin 2) (la lb : List I) (xa xb : ℂ) (n : ℕ)
  (hn : n < lb.length) : FreeAlgebra ℂ I :=
  superCommuteCoef q la (List.take n lb) •
  ofList (List.take n lb) 1 *
  superCommute q (ofList la xa) (FreeAlgebra.ι ℂ (lb.get ⟨n, hn⟩))
  * ofList (List.drop (n + 1) lb) xb

lemma superCommute_ofList_cons {I : Type} (q : I → Fin 2) (la lb : List I) (xa xb : ℂ) (b1 : I) :
    superCommute q (ofList la xa) (ofList (b1 :: lb) xb) =
    superCommute q (ofList la xa) (FreeAlgebra.ι ℂ b1) * ofList lb xb +
    superCommuteCoef q la [b1] •
    (ofList [b1] 1) * superCommute q (ofList la xa) (ofList lb xb) := by
  rw [ofList_cons_eq_ofList]
  rw [superCommute_ofList_mul]
  congr
  · exact ofList_singleton b1

lemma superCommute_ofList_sum {I : Type} (q : I → Fin 2) (la lb : List I) (xa xb : ℂ) :
    superCommute q (ofList la xa) (ofList lb xb) =
    ∑ (n : Fin lb.length), superCommuteTake q la lb xa xb n n.prop := by
  induction lb with
  | nil =>
    simp only [superCommute_ofList_ofList, List.append_nil, Fin.isValue, grade_empty, zero_ne_one,
      and_false, ↓reduceIte, List.nil_append, List.length_nil, Finset.univ_eq_empty,
      Finset.sum_empty]
    ring_nf
    abel
  | cons b lb ih =>
    rw [superCommute_ofList_cons, ih]
    have h0 : ((superCommute q) (ofList la xa)) (FreeAlgebra.ι ℂ b) * ofList lb xb =
        superCommuteTake q la (b :: lb) xa xb 0 (Nat.zero_lt_succ lb.length) := by
      simp [superCommuteTake, superCommuteCoef_empty, ofList_empty]
    rw [h0]
    have hf (f : Fin (b :: lb).length → FreeAlgebra ℂ I) : ∑ n, f n = f ⟨0,
        Nat.zero_lt_succ lb.length⟩ + ∑ n, f (Fin.succ n) := by
      exact Fin.sum_univ_succAbove f ⟨0, Nat.zero_lt_succ lb.length⟩
    rw [hf]
    congr
    rw [Finset.mul_sum]
    congr
    funext n
    simp only [superCommuteTake, Fin.eta, List.get_eq_getElem, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, smul_smul, List.length_cons, Fin.val_succ, List.take_succ_cons,
      List.getElem_cons_succ, List.drop_succ_cons]
    congr 1
    · rw [mul_comm, ← superCommuteCoef_append]
      rfl
    · simp only [← mul_assoc, mul_eq_mul_right_iff]
      exact Or.inl (Or.inl (ofList_cons_eq_ofList (List.take (↑n) lb) b 1).symm)

lemma superCommute_ofList_ofList_superCommuteCoef {I : Type} (q : I → Fin 2) (la lb : List I)
    (xa xb : ℂ) : superCommute q (ofList la xa) (ofList lb xb) =
    ofList la xa * ofList lb xb - superCommuteCoef q la lb • ofList lb xb * ofList la xa := by
  rw [superCommute_ofList_ofList, superCommuteCoef]
  by_cases hq : grade q la = 1 ∧ grade q lb = 1
  · simp [hq, ofList_pair]
  · simp only [ofList_pair, Fin.isValue, hq, ↓reduceIte, one_smul]
    abel

lemma ofList_ofList_superCommute {I : Type} (q : I → Fin 2) (la lb : List I) (xa xb : ℂ) :
    ofList la xa * ofList lb xb = superCommuteCoef q la lb • ofList lb xb * ofList la xa
    + superCommute q (ofList la xa) (ofList lb xb) := by
  rw [superCommute_ofList_ofList_superCommuteCoef]
  abel

lemma ofListM_ofList_superCommute' {I : Type}
    (q : I → Fin 2) (l : List I) (r : List I) (x y : ℂ) :
  ofList r y * ofList l x = superCommuteCoef q l r • (ofList l x * ofList r y)
    - superCommuteCoef q l r • superCommute q (ofList l x) (ofList r y) := by
  nth_rewrite 2 [ofList_ofList_superCommute q]
  rw [superCommuteCoef]
  by_cases hq : grade q l = 1 ∧ grade q r = 1
  · simp [hq, superCommuteCoef]
  · simp [hq]

end
end Wick
