/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Koszul.SuperCommute
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

noncomputable section

lemma superCommute_ofList_ofListM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    superCommute (fun i => q i.1) (ofList l x) (ofListM f r y) =
    ofList l x * ofListM f r y +
    (if grade (fun i => q i.1) l = 1 ∧ grade q r = 1 then
    ofListM f r y * ofList l x else - ofListM f r y * ofList l x) := by
  conv_lhs => rw [ofListM_expand]
  rw [map_sum]
  conv_rhs =>
    lhs
    rw [ofListM_expand, Finset.mul_sum]
  conv_rhs =>
    rhs
    rhs
    rw [ofListM_expand, ← Finset.sum_neg_distrib, Finset.sum_mul]
  conv_rhs =>
    rhs
    lhs
    rw [ofListM_expand, Finset.sum_mul]
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

lemma superCommute_ofList_ofListM_superCommuteCoefM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    superCommute (fun i => q i.1) (ofList l x) (ofListM f r y) =
    ofList l x * ofListM f r y - superCommuteCoefM q l r • ofListM f r y * ofList l x := by
  rw [superCommute_ofList_ofListM, superCommuteCoefM]
  by_cases hq : grade (fun i => q i.fst) l = 1 ∧ grade q r = 1
  · simp [hq]
  · simp only [Fin.isValue, hq, ↓reduceIte, neg_mul, one_smul]
    abel

lemma ofList_ofListM_superCommute {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    ofList l x * ofListM f r y = superCommuteCoefM q l r • ofListM f r y * ofList l x
    + superCommute (fun i => q i.1) (ofList l x) (ofListM f r y) := by
  rw [superCommute_ofList_ofListM_superCommuteCoefM]
  abel

lemma ofListM_ofList_superCommute {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
  ofListM f r y * ofList l x = superCommuteCoefM q l r • (ofList l x * ofListM f r y)
    - superCommuteCoefM q l r • superCommute (fun i => q i.1) (ofList l x) (ofListM f r y) := by
  rw [ofList_ofListM_superCommute, superCommuteCoefM]
  by_cases hq : grade (fun i => q i.fst) l = 1 ∧ grade q r = 1
  · simp [hq]
  · simp [hq]

lemma superCommuteCoefM_append {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r1 r2 : List I) :
    superCommuteCoefM q l (r1 ++ r2) = superCommuteCoefM q l r1 * superCommuteCoefM q l r2 := by
  simp only [superCommuteCoefM, Fin.isValue, grade_append, ite_eq_right_iff, zero_ne_one, imp_false,
    mul_ite, mul_neg, mul_one]
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

def superCommuteTakeM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) (n : ℕ)
    (hn : n < r.length) : FreeAlgebra ℂ (Σ i, f i) :=
  superCommuteCoefM q l (List.take n r) •
  (ofListM f (List.take n r) 1 *
  superCommute (fun i => q i.1) (ofList l x) (freeAlgebraMap f (FreeAlgebra.ι ℂ (r.get ⟨n, hn⟩)))
  * ofListM f (List.drop (n + 1) r) y)

lemma superCommuteM_ofList_cons {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) (b1 : I) :
    superCommute (fun i => q i.1) (ofList l x) (ofListM f (b1 :: r) y) =
    superCommute (fun i => q i.1) (ofList l x) (freeAlgebraMap f (FreeAlgebra.ι ℂ b1))
    * ofListM f r y + superCommuteCoefM q l [b1] •
    (ofListM f [b1] 1) * superCommute (fun i => q i.1) (ofList l x) (ofListM f r y) := by
  rw [ofListM_cons]
  conv_lhs =>
    rhs
    rw [ofListM_expand]
    rw [Finset.mul_sum]
  rw [map_sum]
  trans ∑ (n : CreatAnnilateSect f r), ∑ j : f b1, ((superCommute fun i => q i.fst) (ofList l x))
    ((FreeAlgebra.ι ℂ ⟨b1, j⟩) * ofList n.toList y)
  · apply congrArg
    funext n
    rw [← map_sum]
    congr
    rw [Finset.sum_mul]
  conv_rhs =>
    lhs
    rw [ofListM_expand, Finset.mul_sum]
  conv_rhs =>
    rhs
    rhs
    rw [ofListM_expand]
    rw [map_sum]
  conv_rhs =>
    rhs
    rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  congr
  funext n
  rw [freeAlgebraMap_ι, map_sum, Finset.sum_mul]
  conv_rhs =>
    rhs
    rw [ofListM_singleton]
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

lemma superCommute_ofList_ofListM_sum {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    superCommute (fun i => q i.1) (ofList l x) (ofListM f r y) =
    ∑ (n : Fin r.length), superCommuteTakeM q l r x y n n.prop := by
  induction r with
  | nil =>
    simp only [superCommute_ofList_ofListM, Fin.isValue, grade_empty, zero_ne_one, and_false,
      ↓reduceIte, neg_mul, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
    rw [ofListM, ofList_empty']
    simp
  | cons b r ih =>
    rw [superCommuteM_ofList_cons]
    have h0 : ((superCommute fun i => q i.fst) (ofList l x))
        ((freeAlgebraMap f) (FreeAlgebra.ι ℂ b)) * ofListM f r y =
        superCommuteTakeM q l (b :: r) x y 0 (Nat.zero_lt_succ r.length) := by
      simp [superCommuteTakeM, superCommuteCoefM_empty, ofListM_empty]
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
    simp only [superCommuteTakeM, Fin.eta, List.get_eq_getElem, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_smul, List.length_cons, Fin.val_succ, List.take_succ_cons,
      List.getElem_cons_succ, List.drop_succ_cons]
    congr 1
    · rw [mul_comm, ← superCommuteCoefM_append]
      rfl
    · simp only [← mul_assoc, mul_eq_mul_right_iff]
      apply Or.inl
      apply Or.inl
      rw [ofListM, ofListM, ofListM]
      rw [← map_mul]
      congr
      rw [← ofList_pair, one_mul]
      rfl

end
end Wick
