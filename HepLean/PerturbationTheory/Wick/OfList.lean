/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.Wick.CreateAnnilateSection
import HepLean.PerturbationTheory.Wick.KoszulOrder
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick
open HepLean.List
open FieldStatistic

noncomputable section

variable {𝓕 : Type} (q : 𝓕 → FieldStatistic) (le : 𝓕 → 𝓕 → Prop) [DecidableRel le]

/-- The element of the free algebra `FreeAlgebra ℂ I` associated with a `List I`. -/
def ofList (l : List 𝓕) (x : ℂ) : FreeAlgebra ℂ 𝓕 :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x)

lemma ofList_pair (l r : List 𝓕) (x y : ℂ) :
    ofList (l ++ r) (x * y) = ofList l x * ofList r y := by
  simp only [ofList, ← map_mul, MonoidAlgebra.single_mul_single, EmbeddingLike.apply_eq_iff_eq]
  rfl

lemma ofList_triple (la lb lc : List 𝓕) (xa xb xc : ℂ) :
    ofList (la ++ lb ++ lc) (xa * xb * xc) = ofList la xa * ofList lb xb * ofList lc xc := by
  rw [ofList_pair, ofList_pair]

lemma ofList_triple_assoc (la lb lc : List 𝓕) (xa xb xc : ℂ) :
    ofList (la ++ (lb ++ lc)) (xa * (xb * xc)) = ofList la xa * ofList lb xb * ofList lc xc := by
  rw [ofList_pair, ofList_pair]
  exact Eq.symm (mul_assoc (ofList la xa) (ofList lb xb) (ofList lc xc))

lemma ofList_cons_eq_ofList (l : List 𝓕) (i : 𝓕) (x : ℂ) :
    ofList (i :: l) x = ofList [i] 1 * ofList l x := by
  simp only [ofList, ← map_mul, MonoidAlgebra.single_mul_single, one_mul,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

lemma ofList_singleton (i : 𝓕) :
    ofList [i] 1 = FreeAlgebra.ι ℂ i := by
  simp only [ofList, FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    MonoidAlgebra.single, AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
  rfl

lemma ofList_eq_smul_one (l : List 𝓕) (x : ℂ) :
    ofList l x = x • ofList l 1 := by
  simp only [ofList]
  rw [← map_smul]
  simp

lemma ofList_empty : ofList [] 1 = (1 : FreeAlgebra ℂ 𝓕) := by
  simp only [ofList, EmbeddingLike.map_eq_one_iff]
  rfl

lemma ofList_empty' : ofList [] x = x • (1 : FreeAlgebra ℂ 𝓕) := by
  rw [ofList_eq_smul_one, ofList_empty]

lemma koszulOrder_ofList
    (l : List 𝓕) (x : ℂ) :
    koszulOrder q le (ofList l x) = (koszulSign q le l) • ofList (List.insertionSort le l) x := by
  rw [ofList]
  rw [koszulOrder_single]
  change ofList (List.insertionSort le l) _ = _
  rw [ofList_eq_smul_one]
  conv_rhs => rw [ofList_eq_smul_one]
  rw [smul_smul]

lemma ofList_insertionSort_eq_koszulOrder (l : List 𝓕) (x : ℂ) :
    ofList (List.insertionSort le l) x = (koszulSign q le l) • koszulOrder q le (ofList l x) := by
  rw [koszulOrder_ofList]
  rw [smul_smul]
  rw [koszulSign_mul_self]
  simp

/-- The map of algebras from `FreeAlgebra ℂ I` to `FreeAlgebra ℂ (Σ i, f i)` taking
  the monomial `i` to the sum of elements in `(Σ i, f i)` above `i`, i.e. the sum of the fiber
  above `i`. -/
def sumFiber (f : 𝓕 → Type) [∀ i, Fintype (f i)] :
    FreeAlgebra ℂ 𝓕 →ₐ[ℂ] FreeAlgebra ℂ (Σ i, f i) :=
  FreeAlgebra.lift ℂ fun i => ∑ (j : f i), FreeAlgebra.ι ℂ ⟨i, j⟩

lemma sumFiber_ι (f : 𝓕 → Type) [∀ i, Fintype (f i)] (i : 𝓕) :
    sumFiber f (FreeAlgebra.ι ℂ i) = ∑ (b : f i), FreeAlgebra.ι ℂ ⟨i, b⟩ := by
  simp [sumFiber]

/-- Given a list `l : List I` the corresponding element of `FreeAlgebra ℂ (Σ i, f i)`
  by mapping each `i : I` to the sum of it's fiber in `Σ i, f i` and taking the product of the
  result.
  For example, in terms of creation and annihlation opperators,
  `[φ₁, φ₂, φ₃]` gets taken to `(φ₁⁰ + φ₁¹)(φ₂⁰ + φ₂¹)(φ₃⁰ + φ₃¹)`.
  -/
def ofListLift (f : 𝓕 → Type) [∀ i, Fintype (f i)] (l : List 𝓕) (x : ℂ) :
    FreeAlgebra ℂ (Σ i, f i) :=
  sumFiber f (ofList l x)

lemma ofListLift_empty (f : 𝓕 → Type) [∀ i, Fintype (f i)] :
    ofListLift f [] 1 = 1 := by
  simp only [ofListLift, EmbeddingLike.map_eq_one_iff]
  rw [ofList_empty]
  exact map_one (sumFiber f)

lemma ofListLift_empty_smul (f : 𝓕 → Type) [∀ i, Fintype (f i)] (x : ℂ) :
    ofListLift f [] x = x • 1 := by
  simp only [ofListLift, EmbeddingLike.map_eq_one_iff]
  rw [ofList_eq_smul_one]
  rw [ofList_empty]
  simp

lemma ofListLift_cons (f : 𝓕 → Type) [∀ i, Fintype (f i)] (i : 𝓕) (r : List 𝓕) (x : ℂ) :
    ofListLift f (i :: r) x = (∑ j : f i, FreeAlgebra.ι ℂ ⟨i, j⟩) * (ofListLift f r x) := by
  rw [ofListLift, ofList_cons_eq_ofList, ofList_singleton, map_mul]
  conv_lhs => lhs; rw [sumFiber]
  rw [ofListLift]
  simp

lemma ofListLift_singleton (f : 𝓕 → Type) [∀ i, Fintype (f i)] (i : 𝓕) (x : ℂ) :
    ofListLift f [i] x = ∑ j : f i, x • FreeAlgebra.ι ℂ ⟨i, j⟩ := by
  simp only [ofListLift]
  rw [ofList_eq_smul_one, ofList_singleton, map_smul]
  rw [sumFiber_ι]
  rw [Finset.smul_sum]

lemma ofListLift_singleton_one (f : 𝓕 → Type) [∀ i, Fintype (f i)] (i : 𝓕) :
    ofListLift f [i] 1 = ∑ j : f i, FreeAlgebra.ι ℂ ⟨i, j⟩ := by
  simp only [ofListLift]
  rw [ofList_eq_smul_one, ofList_singleton, map_smul]
  rw [sumFiber_ι]
  rw [Finset.smul_sum]
  simp

lemma ofListLift_cons_eq_ofListLift (f : 𝓕 → Type) [∀ i, Fintype (f i)] (i : 𝓕)
    (r : List 𝓕) (x : ℂ) :
    ofListLift f (i :: r) x = ofListLift f [i] 1 * ofListLift f r x := by
  rw [ofListLift_cons, ofListLift_singleton]
  simp only [one_smul]

lemma ofListLift_expand (f : 𝓕 → Type) [∀ i, Fintype (f i)] (x : ℂ) :
    (l : List 𝓕) → ofListLift f l x = ∑ (a : CreateAnnilateSect f l), ofList a.toList x
  | [] => by
    simp only [ofListLift, CreateAnnilateSect, List.length_nil, List.get_eq_getElem,
      Finset.univ_unique, CreateAnnilateSect.toList, Finset.sum_const, Finset.card_singleton,
      one_smul]
    rw [ofList_eq_smul_one, map_smul, ofList_empty, ofList_eq_smul_one, ofList_empty, map_one]
  | i :: l => by
    rw [ofListLift_cons, ofListLift_expand f x l]
    conv_rhs => rw [← (CreateAnnilateSect.extractEquiv
        ⟨0, by exact Nat.zero_lt_succ l.length⟩).symm.sum_comp (α := FreeAlgebra ℂ _)]
    erw [Finset.sum_product]
    rw [Finset.sum_mul]
    conv_lhs =>
      rhs
      intro n
      rw [Finset.mul_sum]
    congr
    funext j
    congr
    funext n
    rw [← ofList_singleton, ← ofList_pair, one_mul]
    rfl

lemma koszulOrder_ofListLift {f : 𝓕 → Type} [∀ i, Fintype (f i)]
    (l : List 𝓕) (x : ℂ) :
    koszulOrder (fun i => q i.fst) (fun i j => le i.1 j.1) (ofListLift f l x) =
    sumFiber f (koszulOrder q le (ofList l x)) := by
  rw [koszulOrder_ofList]
  rw [map_smul]
  change _ = _ • ofListLift _ _ _
  rw [ofListLift_expand]
  rw [map_sum]
  conv_lhs =>
    rhs
    intro a
    rw [koszulOrder_ofList]
    rw [CreateAnnilateSect.toList_koszulSign]
  rw [← Finset.smul_sum]
  apply congrArg
  conv_lhs =>
    rhs
    intro n
    rw [← CreateAnnilateSect.sort_toList]
  rw [ofListLift_expand]
  refine Fintype.sum_equiv
    ((HepLean.List.insertionSortEquiv le l).piCongr fun i => Equiv.cast ?_) _ _ ?_
  congr 1
  · rw [← HepLean.List.insertionSortEquiv_get]
    simp
  · intro x
    rfl

lemma koszulOrder_ofListLift_eq_ofListLift {f : 𝓕 → Type} [∀ i, Fintype (f i)]
    (l : List 𝓕) (x : ℂ) : koszulOrder (fun i => q i.fst) (fun i j => le i.1 j.1)
    (ofListLift f l x) =
    koszulSign q le l • ofListLift f (List.insertionSort le l) x := by
  rw [koszulOrder_ofListLift, koszulOrder_ofList, map_smul]
  rfl

end
end Wick
