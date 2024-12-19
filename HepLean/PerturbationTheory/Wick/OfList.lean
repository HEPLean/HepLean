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

noncomputable section

/-- The element of the free algebra `FreeAlgebra ℂ I` associated with a `List I`. -/
def ofList {I : Type} (l : List I) (x : ℂ) : FreeAlgebra ℂ I :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x)

lemma ofList_pair {I : Type} (l r : List I) (x y : ℂ) :
    ofList (l ++ r) (x * y) = ofList l x * ofList r y := by
  simp only [ofList, ← map_mul, MonoidAlgebra.single_mul_single, EmbeddingLike.apply_eq_iff_eq]
  rfl

lemma ofList_triple {I : Type} (la lb lc : List I) (xa xb xc : ℂ) :
    ofList (la ++ lb ++ lc) (xa * xb * xc) = ofList la xa * ofList lb xb * ofList lc xc := by
  rw [ofList_pair, ofList_pair]

lemma ofList_triple_assoc {I : Type} (la lb lc : List I) (xa xb xc : ℂ) :
    ofList (la ++ (lb ++ lc)) (xa * (xb * xc)) = ofList la xa * ofList lb xb * ofList lc xc := by
  rw [ofList_pair, ofList_pair]
  exact Eq.symm (mul_assoc (ofList la xa) (ofList lb xb) (ofList lc xc))

lemma ofList_cons_eq_ofList {I : Type} (l : List I) (i : I) (x : ℂ) :
    ofList (i :: l) x = ofList [i] 1 * ofList l x := by
  simp only [ofList, ← map_mul, MonoidAlgebra.single_mul_single, one_mul,
    EmbeddingLike.apply_eq_iff_eq]
  rfl

lemma ofList_singleton {I : Type} (i : I) :
    ofList [i] 1 = FreeAlgebra.ι ℂ i := by
  simp only [ofList, FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    MonoidAlgebra.single, AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
  rfl

lemma ofList_eq_smul_one {I : Type} (l : List I) (x : ℂ) :
    ofList l x = x • ofList l 1 := by
  simp only [ofList]
  rw [← map_smul]
  simp

lemma ofList_empty {I : Type} : ofList [] 1 = (1 : FreeAlgebra ℂ I) := by
  simp only [ofList, EmbeddingLike.map_eq_one_iff]
  rfl

lemma ofList_empty' {I : Type} : ofList [] x = x • (1 : FreeAlgebra ℂ I) := by
  rw [ofList_eq_smul_one, ofList_empty]

lemma koszulOrder_ofList {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (l : List I) (x : ℂ) :
    koszulOrder r q (ofList l x) = (koszulSign r q l) • ofList (List.insertionSort r l) x := by
  rw [ofList]
  rw [koszulOrder_single]
  change ofList (List.insertionSort r l) _ = _
  rw [ofList_eq_smul_one]
  conv_rhs => rw [ofList_eq_smul_one]
  rw [smul_smul]

lemma ofList_insertionSort_eq_koszulOrder {I : Type} (r : I → I → Prop) [DecidableRel r]
    (q : I → Fin 2) (l : List I) (x : ℂ) :
    ofList (List.insertionSort r l) x = (koszulSign r q l) • koszulOrder r q (ofList l x) := by
  rw [koszulOrder_ofList]
  rw [smul_smul]
  rw [koszulSign_mul_self]
  simp

/-- The map of algebras from `FreeAlgebra ℂ I` to `FreeAlgebra ℂ (Σ i, f i)` taking
  the monomial `i` to the sum of elements in `(Σ i, f i)` above `i`, i.e. the sum of the fiber
  above `i`. -/
def sumFiber {I : Type} (f : I → Type) [∀ i, Fintype (f i)] :
    FreeAlgebra ℂ I →ₐ[ℂ] FreeAlgebra ℂ (Σ i, f i) :=
  FreeAlgebra.lift ℂ fun i => ∑ (j : f i), FreeAlgebra.ι ℂ ⟨i, j⟩

lemma sumFiber_ι {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) :
    sumFiber f (FreeAlgebra.ι ℂ i) = ∑ (b : f i), FreeAlgebra.ι ℂ ⟨i, b⟩ := by
  simp [sumFiber]

/-- Given a list `l : List I` the corresponding element of `FreeAlgebra ℂ (Σ i, f i)`
  by mapping each `i : I` to the sum of it's fiber in `Σ i, f i` and taking the product of the
  result.
  For example, in terms of creation and annihlation opperators,
  `[φ₁, φ₂, φ₃]` gets taken to `(φ₁⁰ + φ₁¹)(φ₂⁰ + φ₂¹)(φ₃⁰ + φ₃¹)`.
  -/
def ofListLift {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (l : List I) (x : ℂ) :
    FreeAlgebra ℂ (Σ i, f i) :=
  sumFiber f (ofList l x)

lemma ofListLift_empty {I : Type} (f : I → Type) [∀ i, Fintype (f i)] :
  ofListLift f [] 1 = 1 := by
  simp only [ofListLift, EmbeddingLike.map_eq_one_iff]
  rw [ofList_empty]
  exact map_one (sumFiber f)

lemma ofListLift_empty_smul {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (x : ℂ) :
  ofListLift f [] x = x • 1 := by
  simp only [ofListLift, EmbeddingLike.map_eq_one_iff]
  rw [ofList_eq_smul_one]
  rw [ofList_empty]
  simp

lemma ofListLift_cons {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) (r : List I) (x : ℂ) :
    ofListLift f (i :: r) x = (∑ j : f i, FreeAlgebra.ι ℂ ⟨i, j⟩) * (ofListLift f r x) := by
  rw [ofListLift, ofList_cons_eq_ofList, ofList_singleton, map_mul]
  conv_lhs => lhs; rw [sumFiber]
  rw [ofListLift]
  simp

lemma ofListLift_singleton {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) (x : ℂ) :
    ofListLift f [i] x = ∑ j : f i, x • FreeAlgebra.ι ℂ ⟨i, j⟩ := by
  simp only [ofListLift]
  rw [ofList_eq_smul_one, ofList_singleton, map_smul]
  rw [sumFiber_ι]
  rw [Finset.smul_sum]

lemma ofListLift_singleton_one {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) :
    ofListLift f [i] 1 = ∑ j : f i, FreeAlgebra.ι ℂ ⟨i, j⟩ := by
  simp only [ofListLift]
  rw [ofList_eq_smul_one, ofList_singleton, map_smul]
  rw [sumFiber_ι]
  rw [Finset.smul_sum]
  simp

lemma ofListLift_cons_eq_ofListLift {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I)
    (r : List I) (x : ℂ) :
    ofListLift f (i :: r) x = ofListLift f [i] 1 * ofListLift f r x := by
  rw [ofListLift_cons, ofListLift_singleton]
  simp only [one_smul]

lemma ofListLift_expand {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (x : ℂ) :
    (l : List I) → ofListLift f l x = ∑ (a : CreateAnnilateSect f l), ofList a.toList x
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

lemma koszulOrder_ofListLift {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (x : ℂ) :
    koszulOrder (fun i j => le1 i.1 j.1) (fun i => q i.fst) (ofListLift f l x) =
    sumFiber f (koszulOrder le1 q (ofList l x)) := by
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
    ((HepLean.List.insertionSortEquiv le1 l).piCongr fun i => Equiv.cast ?_) _ _ ?_
  congr 1
  · rw [← HepLean.List.insertionSortEquiv_get]
    simp
  · intro x
    rfl

lemma koszulOrder_ofListLift_eq_ofListLift {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (x : ℂ) : koszulOrder (fun i j => le1 i.1 j.1) (fun i => q i.fst)
    (ofListLift f l x) =
    koszulSign le1 q l • ofListLift f (List.insertionSort le1 l) x := by
  rw [koszulOrder_ofListLift, koszulOrder_ofList, map_smul]
  rfl

end
end Wick
