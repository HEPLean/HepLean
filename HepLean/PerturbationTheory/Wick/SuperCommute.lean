/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.OfList
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

noncomputable section

/-- Given a grading `q : I → Fin 2` and a list `l : List I` the super-commutor on the free algebra
  `FreeAlgebra ℂ I` corresponding to commuting with `l`
  as a linear map from `MonoidAlgebra ℂ (FreeMonoid I)` (the module of lists in `I`)
  to itself. -/
def superCommuteMonoidAlgebra {I : Type} (q : I → Fin 2) (l : List I) :
    MonoidAlgebra ℂ (FreeMonoid I) →ₗ[ℂ] MonoidAlgebra ℂ (FreeMonoid I) :=
  Finsupp.lift (MonoidAlgebra ℂ (FreeMonoid I)) ℂ (List I)
    (fun r =>
      Finsupp.lsingle (R := ℂ) (l ++ r) 1 +
      if grade q l = 1 ∧ grade q r = 1 then
        Finsupp.lsingle (R := ℂ) (r ++ l) 1
      else
        - Finsupp.lsingle (R := ℂ) (r ++ l) 1)

/-- Given a grading `q : I → Fin 2` the super-commutor on the free algebra `FreeAlgebra ℂ I`
  as a linear map from `MonoidAlgebra ℂ (FreeMonoid I)` (the module of lists in `I`)
  to `FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I`. -/
def superCommuteAlgebra {I : Type} (q : I → Fin 2) :
    MonoidAlgebra ℂ (FreeMonoid I) →ₗ[ℂ] FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I :=
  Finsupp.lift (FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I) ℂ (List I) fun l =>
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toAlgHom.toLinearMap
    ∘ₗ superCommuteMonoidAlgebra q l
    ∘ₗ FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom.toLinearMap)

/-- Given a grading `q : I → Fin 2` the super-commutor on the free algebra `FreeAlgebra ℂ I`
  as a bi-linear map. -/
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

/-- Given two lists `la lb : List I`, in the expansion of the supercommutor of `la` and `lb`
  via elements of `lb`the term associated with the `n`th element.
  E.g. in the commutator
  `[a, bc] = [a, b] c + b [a, c] ` the `superCommuteSplit` for `n=0` is `[a, b] c`
  and for `n=1` is `b [a, c]`. -/
def superCommuteSplit {I : Type} (q : I → Fin 2) (la lb : List I) (xa xb : ℂ) (n : ℕ)
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
    ∑ (n : Fin lb.length), superCommuteSplit q la lb xa xb n n.prop := by
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
        superCommuteSplit q la (b :: lb) xa xb 0 (Nat.zero_lt_succ lb.length) := by
      simp [superCommuteSplit, superCommuteCoef_empty, ofList_empty]
    rw [h0]
    have hf (f : Fin (b :: lb).length → FreeAlgebra ℂ I) : ∑ n, f n = f ⟨0,
        Nat.zero_lt_succ lb.length⟩ + ∑ n, f (Fin.succ n) := by
      exact Fin.sum_univ_succAbove f ⟨0, Nat.zero_lt_succ lb.length⟩
    rw [hf]
    congr
    rw [Finset.mul_sum]
    congr
    funext n
    simp only [superCommuteSplit, Fin.eta, List.get_eq_getElem, Algebra.smul_mul_assoc,
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

lemma ofListLift_ofList_superCommute' {I : Type}
    (q : I → Fin 2) (l : List I) (r : List I) (x y : ℂ) :
  ofList r y * ofList l x = superCommuteCoef q l r • (ofList l x * ofList r y)
    - superCommuteCoef q l r • superCommute q (ofList l x) (ofList r y) := by
  nth_rewrite 2 [ofList_ofList_superCommute q]
  rw [superCommuteCoef]
  by_cases hq : grade q l = 1 ∧ grade q r = 1
  · simp [hq, superCommuteCoef]
  · simp [hq]

lemma superCommute_ofList_ofListLift {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    superCommute (fun i => q i.1) (ofList l x) (ofListLift f r y) =
    ofList l x * ofListLift f r y +
    (if grade (fun i => q i.1) l = 1 ∧ grade q r = 1 then
    ofListLift f r y * ofList l x else - ofListLift f r y * ofList l x) := by
  conv_lhs => rw [ofListLift_expand]
  rw [map_sum]
  conv_rhs =>
    lhs
    rw [ofListLift_expand, Finset.mul_sum]
  conv_rhs =>
    rhs
    rhs
    rw [ofListLift_expand, ← Finset.sum_neg_distrib, Finset.sum_mul]
  conv_rhs =>
    rhs
    lhs
    rw [ofListLift_expand, Finset.sum_mul]
  rw [← Finset.sum_ite_irrel]
  rw [← Finset.sum_add_distrib]
  congr
  funext a
  rw [superCommute_ofList_ofList]
  congr 1
  · exact ofList_pair l a.toList x y
  congr 1
  · simp
  · exact ofList_pair a.toList l y x
  · rw [ofList_pair]
    simp only [neg_mul]

lemma superCommute_ofList_ofListLift_superCommuteLiftCoef {I : Type} {f : I → Type}
    [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    superCommute (fun i => q i.1) (ofList l x) (ofListLift f r y) =
    ofList l x * ofListLift f r y - superCommuteLiftCoef q l r • ofListLift f r y * ofList l x := by
  rw [superCommute_ofList_ofListLift, superCommuteLiftCoef]
  by_cases hq : grade (fun i => q i.fst) l = 1 ∧ grade q r = 1
  · simp [hq]
  · simp only [Fin.isValue, hq, ↓reduceIte, neg_mul, one_smul]
    abel

lemma ofList_ofListLift_superCommute {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    ofList l x * ofListLift f r y = superCommuteLiftCoef q l r • ofListLift f r y * ofList l x
    + superCommute (fun i => q i.1) (ofList l x) (ofListLift f r y) := by
  rw [superCommute_ofList_ofListLift_superCommuteLiftCoef]
  abel

lemma ofListLift_ofList_superCommute {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
  ofListLift f r y * ofList l x = superCommuteLiftCoef q l r • (ofList l x * ofListLift f r y)
    - superCommuteLiftCoef q l r •
    superCommute (fun i => q i.1) (ofList l x) (ofListLift f r y) := by
  rw [ofList_ofListLift_superCommute, superCommuteLiftCoef]
  by_cases hq : grade (fun i => q i.fst) l = 1 ∧ grade q r = 1
  · simp [hq]
  · simp [hq]

lemma superCommuteLiftCoef_append {I : Type} {f : I → Type}
    (q : I → Fin 2) (l : List (Σ i, f i)) (r1 r2 : List I) :
    superCommuteLiftCoef q l (r1 ++ r2) =
    superCommuteLiftCoef q l r1 * superCommuteLiftCoef q l r2 := by
  simp only [superCommuteLiftCoef, Fin.isValue, grade_append, ite_eq_right_iff, zero_ne_one,
    imp_false, mul_ite, mul_neg, mul_one]
  by_cases hla : grade (fun i => q i.1) l = 1
  · by_cases hlb : grade q r1 = 1
    · by_cases hlc : grade q r2 = 1
      · simp [hlc, hlb, hla]
      · have hc : grade q r2 = 0 := by
          omega
        simp [hc, hlb, hla]
    · have hb : grade q r1 = 0 := by
        omega
      by_cases hlc : grade q r2 = 1
      · simp [hlc, hb]
      · have hc : grade q r2 = 0 := by
          omega
        simp [hc, hb]
  · have ha : grade (fun i => q i.1) l = 0 := by
      omega
    simp [ha]

/-- Given two lists `l : List (Σ i, f i)` and `r : List I`, on
  in the expansion of the supercommutor of `l` and the lift of `r`
  via elements of `r`the term associated with the `n`th element.
  E.g. in the commutator
  `[a, bc] = [a, b] c + b [a, c] ` the `superCommuteSplit` for `n=0` is `[a, b] c`
  and for `n=1` is `b [a, c]`. -/
def superCommuteLiftSplit {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) (n : ℕ)
    (hn : n < r.length) : FreeAlgebra ℂ (Σ i, f i) :=
  superCommuteLiftCoef q l (List.take n r) •
  (ofListLift f (List.take n r) 1 *
  superCommute (fun i => q i.1) (ofList l x) (sumFiber f (FreeAlgebra.ι ℂ (r.get ⟨n, hn⟩)))
  * ofListLift f (List.drop (n + 1) r) y)

lemma superCommute_ofList_ofListLift_cons {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) (b1 : I) :
    superCommute (fun i => q i.1) (ofList l x) (ofListLift f (b1 :: r) y) =
    superCommute (fun i => q i.1) (ofList l x) (sumFiber f (FreeAlgebra.ι ℂ b1))
    * ofListLift f r y + superCommuteLiftCoef q l [b1] •
    (ofListLift f [b1] 1) * superCommute (fun i => q i.1) (ofList l x) (ofListLift f r y) := by
  rw [ofListLift_cons]
  conv_lhs =>
    rhs
    rw [ofListLift_expand]
    rw [Finset.mul_sum]
  rw [map_sum]
  trans ∑ (n : CreateAnnilateSect f r), ∑ j : f b1, ((superCommute fun i => q i.fst) (ofList l x))
    ((FreeAlgebra.ι ℂ ⟨b1, j⟩) * ofList n.toList y)
  · apply congrArg
    funext n
    rw [← map_sum]
    congr
    rw [Finset.sum_mul]
  conv_rhs =>
    lhs
    rw [ofListLift_expand, Finset.mul_sum]
  conv_rhs =>
    rhs
    rhs
    rw [ofListLift_expand]
    rw [map_sum]
  conv_rhs =>
    rhs
    rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  congr
  funext n
  rw [sumFiber_ι, map_sum, Finset.sum_mul]
  conv_rhs =>
    rhs
    rw [ofListLift_singleton]
    rw [Finset.smul_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  congr
  funext b
  trans ((superCommute fun i => q i.fst) (ofList l x)) (ofList (⟨b1, b⟩ :: n.toList) y)
  · congr
    rw [ofList_cons_eq_ofList]
    rw [ofList_singleton]
  rw [superCommute_ofList_cons]
  congr
  rw [ofList_singleton]
  simp

lemma superCommute_ofList_ofListLift_sum {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    superCommute (fun i => q i.1) (ofList l x) (ofListLift f r y) =
    ∑ (n : Fin r.length), superCommuteLiftSplit q l r x y n n.prop := by
  induction r with
  | nil =>
    simp only [superCommute_ofList_ofListLift, Fin.isValue, grade_empty, zero_ne_one, and_false,
      ↓reduceIte, neg_mul, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
    rw [ofListLift, ofList_empty']
    simp
  | cons b r ih =>
    rw [superCommute_ofList_ofListLift_cons]
    have h0 : ((superCommute fun i => q i.fst) (ofList l x))
        ((sumFiber f) (FreeAlgebra.ι ℂ b)) * ofListLift f r y =
        superCommuteLiftSplit q l (b :: r) x y 0 (Nat.zero_lt_succ r.length) := by
      simp [superCommuteLiftSplit, superCommuteLiftCoef_empty, ofListLift_empty]
    rw [h0]
    have hf (g : Fin (b :: r).length → FreeAlgebra ℂ ((i : I) × f i)) : ∑ n, g n = g ⟨0,
        Nat.zero_lt_succ r.length⟩ + ∑ n, g (Fin.succ n) := by
      exact Fin.sum_univ_succAbove g ⟨0, Nat.zero_lt_succ r.length⟩
    rw [hf]
    congr
    rw [ih]
    rw [Finset.mul_sum]
    congr
    funext n
    simp only [superCommuteLiftSplit, Fin.eta, List.get_eq_getElem, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_smul, List.length_cons, Fin.val_succ, List.take_succ_cons,
      List.getElem_cons_succ, List.drop_succ_cons]
    congr 1
    · rw [mul_comm, ← superCommuteLiftCoef_append]
      rfl
    · simp only [← mul_assoc, mul_eq_mul_right_iff]
      apply Or.inl
      apply Or.inl
      rw [ofListLift, ofListLift, ofListLift]
      rw [← map_mul]
      congr
      rw [← ofList_pair, one_mul]
      rfl
end
end Wick
