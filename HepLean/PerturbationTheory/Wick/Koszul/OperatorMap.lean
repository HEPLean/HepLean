/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.Species
import HepLean.Lorentz.RealVector.Basic
import HepLean.Mathematics.Fin
import HepLean.SpaceTime.Basic
import HepLean.Mathematics.SuperAlgebra.Basic
import HepLean.Mathematics.List
import HepLean.Meta.Notes.Basic
import Init.Data.List.Sort.Basic
import Mathlib.Data.Fin.Tuple.Take
import HepLean.PerturbationTheory.Wick.Koszul.SuperCommuteM
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

noncomputable section

class SuperCommuteCenterMap {A :  Type} [Semiring A] [Algebra ℂ A]
    (f : FreeAlgebra ℂ I →ₐ[ℂ] A) : Prop where
  prop : ∀ i j, f (superCommute q (FreeAlgebra.ι ℂ i) (FreeAlgebra.ι ℂ j)) ∈ Subalgebra.center ℂ A

namespace SuperCommuteCenterMap

variable {I : Type}  {A :  Type} [Semiring A] [Algebra ℂ A]
    (f : FreeAlgebra ℂ I →ₐ[ℂ] A) [SuperCommuteCenterMap f]

lemma ofList_fst (q : I → Fin 2) (i j : I) :
    f (superCommute q (ofList [i] xa) (FreeAlgebra.ι ℂ j)) ∈ Subalgebra.center ℂ A := by
  have h1 : f (superCommute q (ofList [i] xa) (FreeAlgebra.ι ℂ j)) =
      xa • f (superCommute q (FreeAlgebra.ι ℂ i) (FreeAlgebra.ι ℂ j)) := by
    rw [← map_smul]
    congr
    rw [ofList_eq_smul_one, ofList_singleton]
    rw [map_smul]
    rfl
  rw [h1]
  refine Subalgebra.smul_mem (Subalgebra.center ℂ A) ?_ xa
  exact prop i j

lemma ofList_freeAlgebraMap {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (c :  (Σ i, f i))  (x  : ℂ)
    {A :  Type} [Semiring A] [Algebra ℂ A] (F : FreeAlgebra ℂ (Σ i, f i) →ₐ[ℂ] A)
    [SuperCommuteCenterMap F] (b : I) :
    F ((superCommute fun i => q i.fst) (ofList [c] x) ((freeAlgebraMap f) (FreeAlgebra.ι ℂ b)))
    ∈ Subalgebra.center ℂ A := by
  rw [freeAlgebraMap_ι]
  rw [map_sum, map_sum]
  refine Subalgebra.sum_mem (Subalgebra.center ℂ A) ?h
  intro n hn
  exact ofList_fst F (fun i => q i.fst) c ⟨b, n⟩

end SuperCommuteCenterMap

lemma superCommuteTake_superCommuteCenterMap {I : Type} (q : I → Fin 2) (lb : List I) (xa xb : ℂ) (n : ℕ)
    (hn : n < lb.length) {A :  Type} [Semiring A] [Algebra ℂ A] (f : FreeAlgebra ℂ I →ₐ[ℂ] A)
    [SuperCommuteCenterMap f] (i : I) :
    f (superCommuteTake q [i] lb xa xb n hn) =
    f (superCommute q (ofList [i] xa) (FreeAlgebra.ι ℂ (lb.get ⟨n, hn⟩)))
    * (superCommuteCoef q [i] (List.take n lb) •
    f (ofList (List.eraseIdx lb n) xb)) := by
  have hn : f ((superCommute q) (ofList [i] xa) (FreeAlgebra.ι ℂ (lb.get ⟨n, hn⟩))) ∈
    Subalgebra.center ℂ A := SuperCommuteCenterMap.ofList_fst f q i (lb.get ⟨n, hn⟩)
  rw [Subalgebra.mem_center_iff] at hn
  rw [superCommuteTake, map_mul, map_mul, map_smul, hn, mul_assoc, smul_mul_assoc,
    ← map_mul, ← ofList_pair]
  congr
  · exact Eq.symm (List.eraseIdx_eq_take_drop_succ lb n)
  · exact one_mul xb


lemma superCommuteTakeM_F {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (c :  (Σ i, f i)) (r : List I) (x y : ℂ)  (n : ℕ)
    (hn : n < r.length)
    {A :  Type} [Semiring A] [Algebra ℂ A] (F : FreeAlgebra ℂ (Σ i, f i) →ₐ[ℂ] A)
    [SuperCommuteCenterMap F] :
    F (superCommuteTakeM q [c] r x y n hn) = superCommuteCoefM q [c] (List.take n r) •
    (F (superCommute (fun i => q i.1) (ofList [c] x) (freeAlgebraMap f (FreeAlgebra.ι ℂ (r.get ⟨n, hn⟩))))
    * F (ofListM f (List.eraseIdx r n) y)) := by
  rw [superCommuteTakeM]
  rw [map_smul]
  congr
  rw [map_mul, map_mul]
  have h1 : F ((superCommute fun i => q i.fst) (ofList [c] x) ((freeAlgebraMap f) (FreeAlgebra.ι ℂ (r.get ⟨n, hn⟩))))
    ∈ Subalgebra.center ℂ A :=
      SuperCommuteCenterMap.ofList_freeAlgebraMap q c x F (r.get ⟨n, hn⟩)
  rw [Subalgebra.mem_center_iff] at h1
  rw [h1, mul_assoc, ← map_mul]
  congr
  rw [ofListM, ofListM, ofListM, ← map_mul]
  congr
  rw [← ofList_pair, one_mul]
  congr
  exact Eq.symm (List.eraseIdx_eq_take_drop_succ r n)


lemma koszulOrder_superCommuteM_le {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (r : List I) (x : ℂ)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    (i : (Σ i, f i)) (hi : ∀ j, le1 j i)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [SuperCommuteCenterMap F] :
    F (koszulOrder le1 (fun i => q i.fst)
     (superCommute (fun i => q i.1) (FreeAlgebra.ι ℂ i) (ofListM f r x))) = 0 := by
  sorry

lemma koszulOrder_of_le_all {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (r : List I) (x : ℂ) (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    (i : (Σ i, f i)) (hi : ∀ j, le1 j i)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [SuperCommuteCenterMap F] :
    F (koszulOrder le1 (fun i => q i.fst)
    (ofListM f r x * FreeAlgebra.ι ℂ i))
    = superCommuteCoefM q [i] r • F (koszulOrder le1 (fun i => q i.fst)
      (FreeAlgebra.ι ℂ i * ofListM f r x)) := by
  conv_lhs =>
    rhs
    rhs
    rw [← ofList_singleton]
    rw [ofListM_ofList_superCommute q]
  rw [map_sub]
  rw [sub_eq_add_neg]
  rw [map_add]
  conv_lhs =>
    rhs
    rhs
    rw [map_smul]
    rw [← neg_smul]
  rw [map_smul, map_smul, map_smul]
  rw [ofList_singleton, koszulOrder_superCommuteM_le]
  · simp
  · exact fun j => hi j

lemma le_all_mul_koszulOrder {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (r : List I) (x : ℂ) (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    (i : (Σ i, f i)) (hi : ∀ j, le1 j i)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [SuperCommuteCenterMap F] :
    F (FreeAlgebra.ι ℂ i * koszulOrder le1 (fun i => q i.fst)
    (ofListM f r x)) = F ((koszulOrder le1 fun i => q i.fst) (FreeAlgebra.ι ℂ i * ofListM f r x)) +
    F (((superCommute fun i => q i.fst) (ofList [i] 1))
        ((koszulOrder le1 fun i => q i.fst) (ofListM f r x))) := by
    sorry
/-
  rw [map_smul]
  rw [Algebra.mul_smul_comm, map_smul]
  change koszulSign le1 q r • F (FreeAlgebra.ι ℂ i * (ofListM f (List.insertionSort le1 r) x)) = _
  rw [← ofList_singleton]
  rw [ofList_ofListM_superCommute q]
  rw [map_add]
  rw [smul_add]
  rw [← map_smul]
  conv_lhs =>
    lhs
    rhs
    rw [← Algebra.smul_mul_assoc]
    rw [smul_smul, mul_comm, ← smul_smul]
    rw [ ofListM, ← map_smul, ← koszulOrder_ofList, ← koszulOrder_ofListM, ofList_singleton]
    rw [Algebra.smul_mul_assoc]
  rw [koszulOrder_mul_ge]
  rw [map_smul]
  rw [koszulOrder_of_le_all]
  rw [smul_smul]
  have h1 : (superCommuteCoefM q [i] (List.insertionSort le1 r) * superCommuteCoefM q [i] r) = 1 := by
    simp [superCommuteCoefM]
    have ha (a b : Fin 2): (if a = 1 ∧ b = 1 then
      -if a = 1 ∧ b = 1 then -1 else 1
      else if a = 1 ∧ b = 1 then -1 else (1 : ℂ)) = 1 := by
      fin_cases a <;> fin_cases b
      · rfl
      · rfl
      · rfl
      · simp only [Fin.mk_one, Fin.isValue, and_self, ↓reduceIte, neg_neg]
    exact ha _ _
  rw [h1]
  simp only [one_smul]
  conv_lhs =>
    rhs
    rw [← map_smul, ← map_smul]
    rw [ ofListM, ← map_smul, ← koszulOrder_ofList, ← koszulOrder_ofListM]
  congr
  rw [ofList_singleton]
  · exact fun j => hi j
  · exact fun j => hi j.fst
-/
end
end Wick
