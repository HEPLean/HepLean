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
/-!

# Koszul signs and ordering for lists and algebras

-/

namespace Wick

/-- Gives a factor of `-1` when inserting `a` into a list `List I` in the ordered position
  for each fermion-fermion cross. -/
def koszulSignInsert {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) (a : I) :
    List I → ℂ
  | [] => 1
  | b :: l => if r a b then koszulSignInsert r q a l else
    if q a = 1 ∧ q b = 1 then - koszulSignInsert r q a l else koszulSignInsert r q a l

/-- When inserting a boson the `koszulSignInsert` is always `1`. -/
lemma koszulSignInsert_boson {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) (a : I)
    (ha : q a = 0) : (l : List I) → koszulSignInsert r q a l = 1
  | [] => by
    simp [koszulSignInsert]
  | b :: l => by
    simp only [koszulSignInsert, Fin.isValue, ite_eq_left_iff]
    rw [koszulSignInsert_boson r q a ha l, ha]
    simp only [Fin.isValue, zero_ne_one, false_and, ↓reduceIte, ite_self]

@[simp]
lemma koszulSignInsert_mul_self {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) (a : I) :
    (l : List I) → koszulSignInsert r q a l * koszulSignInsert r q a l = 1
  | [] => by
    simp [koszulSignInsert]
  | b :: l => by
    simp [koszulSignInsert]
    by_cases hr : r a b
    · simp [hr]
      rw [koszulSignInsert_mul_self]
    · simp [hr]
      by_cases hq : q a = 1 ∧ q b = 1
      · simp [hq]
        rw [koszulSignInsert_mul_self]
      · simp [hq]
        rw [koszulSignInsert_mul_self]

lemma koszulSignInsert_le_forall {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) (a : I)
    (l : List I) (hi : ∀ b, r a b) :  koszulSignInsert r q a l = 1 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [koszulSignInsert, Fin.isValue, ite_eq_left_iff]
    rw [ih]
    simp only [Fin.isValue, ite_eq_left_iff, ite_eq_right_iff, and_imp]
    intro h
    exact False.elim (h (hi j))

lemma koszulSignInsert_ge_forall_append  {I : Type} (r : I → I → Prop) [DecidableRel r]
    (q : I → Fin 2) (l : List I) (j i : I) (hi : ∀ j, r j i) :
    koszulSignInsert r q j l = koszulSignInsert r q j (l ++ [i]) := by
  induction l with
  | nil => simp [koszulSignInsert, hi]
  | cons b l ih =>
    simp only [koszulSignInsert, Fin.isValue, List.append_eq]
    by_cases hr : r j b
    · rw [if_pos hr, if_pos hr]
      rw [ih]
    · rw [if_neg hr, if_neg hr]
      rw [ih]

/-- Gives a factor of `- 1` for every fermion-fermion (`q` is `1`) crossing that occurs when sorting
  a list of based on `r`. -/
def koszulSign {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) :
    List I → ℂ
  | [] => 1
  | a :: l => koszulSignInsert r q a l * koszulSign r q l

def natTestQ : ℕ → Fin 2 := fun n => if n % 2 = 0 then 0 else 1

lemma koszulSign_mul_self {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (l : List I) : koszulSign r q l * koszulSign r q l = 1 := by
  induction l with
  | nil => simp [koszulSign]
  | cons a l ih =>
    simp [koszulSign]
    trans (koszulSignInsert r q a l * koszulSignInsert r q a l) * (koszulSign r q l * koszulSign r q l)
    ring
    rw [ih]
    rw [koszulSignInsert_mul_self, mul_one]


@[simp]
lemma koszulSign_freeMonoid_of {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (i : I) : koszulSign r q (FreeMonoid.of i) = 1 := by
  change koszulSign r q [i] = 1
  simp only [koszulSign, mul_one]
  rfl


lemma koszulSignInsert_erase_boson {I : Type} (q : I → Fin 2) (le1 :I → I → Prop)
    [DecidableRel le1] (r0 : I)  :
    (r : List I)  → (n : Fin r.length) →  (heq : q (r.get n) = 0)  →
    koszulSignInsert le1 q r0 (r.eraseIdx n) = koszulSignInsert le1 q r0 r
  | [], _, _ => by
    simp
  | r1 :: r, ⟨0, h⟩, hr => by
    simp
    simp at hr
    rw [koszulSignInsert]
    simp [hr]
  | r1 :: r, ⟨n + 1, h⟩, hr => by
    simp
    rw [koszulSignInsert, koszulSignInsert]
    rw [koszulSignInsert_erase_boson q le1 r0 r ⟨n,  Nat.succ_lt_succ_iff.mp h⟩ hr]

lemma koszulSign_erase_boson {I : Type} (q : I → Fin 2) (le1 :I → I → Prop)
    [DecidableRel le1]  :
    (r : List I) → (n : Fin r.length) →  (heq : q (r.get n) = 0) →
    koszulSign le1 q (r.eraseIdx n) = koszulSign le1 q r
  | [], _ => by
    simp
  | r0 :: r, ⟨0, h⟩ => by
    simp [koszulSign]
    intro h
    rw [koszulSignInsert_boson]
    simp
    exact h
  | r0 :: r, ⟨n + 1, h⟩ => by
    simp
    intro h'
    rw [koszulSign, koszulSign]
    rw [koszulSign_erase_boson q le1 r ⟨n,  Nat.succ_lt_succ_iff.mp h⟩]
    congr 1
    rw [koszulSignInsert_erase_boson q le1 r0 r ⟨n,  Nat.succ_lt_succ_iff.mp h⟩ h']
    exact h'


noncomputable section

/-- Given a relation `r` on `I` sorts elements of `MonoidAlgebra ℂ (FreeMonoid I)` by `r` giving it
  a signed dependent on `q`. -/
def koszulOrderMonoidAlgebra {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) :
    MonoidAlgebra ℂ (FreeMonoid I) →ₗ[ℂ] MonoidAlgebra ℂ (FreeMonoid I) :=
  Finsupp.lift (MonoidAlgebra ℂ (FreeMonoid I)) ℂ (List I)
    (fun i => Finsupp.lsingle (R := ℂ) (List.insertionSort r i) (koszulSign r q i))

lemma koszulOrderMonoidAlgebra_ofList {I : Type} (r : I → I → Prop) [DecidableRel r]
    (q : I → Fin 2) (i : List I) :
    koszulOrderMonoidAlgebra r q (MonoidAlgebra.of ℂ (FreeMonoid I) i) =
    (koszulSign r q i) • (MonoidAlgebra.of ℂ (FreeMonoid I) (List.insertionSort r i)) := by
  simp only [koszulOrderMonoidAlgebra, Finsupp.lsingle_apply, MonoidAlgebra.of_apply,
    MonoidAlgebra.smul_single', mul_one]
  rw [MonoidAlgebra.ext_iff]
  intro x
  erw [Finsupp.lift_apply]
  simp only [MonoidAlgebra.smul_single', zero_mul, Finsupp.single_zero, Finsupp.sum_single_index,
    one_mul]

@[simp]
lemma koszulOrderMonoidAlgebra_single {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (l : FreeMonoid I) (x : ℂ) :
    koszulOrderMonoidAlgebra r q (MonoidAlgebra.single l x)
    = (koszulSign r q l) • (MonoidAlgebra.single (List.insertionSort r l) x) := by
  simp only [koszulOrderMonoidAlgebra, Finsupp.lsingle_apply, MonoidAlgebra.smul_single']
  rw [MonoidAlgebra.ext_iff]
  intro x'
  erw [Finsupp.lift_apply]
  simp only [MonoidAlgebra.smul_single', zero_mul, Finsupp.single_zero, Finsupp.sum_single_index,
    one_mul, MonoidAlgebra.single]
  congr 2
  rw [NonUnitalNormedCommRing.mul_comm]

/-- Given a relation `r` on `I` sorts elements of `FreeAlgebra ℂ I` by `r` giving it
  a signed dependent on `q`. -/
def koszulOrder {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) :
    FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.toAlgHom.toLinearMap
  ∘ₗ koszulOrderMonoidAlgebra r q
  ∘ₗ FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom.toLinearMap

@[simp]
lemma koszulOrder_ι {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) (i : I) :
    koszulOrder r q (FreeAlgebra.ι ℂ i) = FreeAlgebra.ι ℂ i := by
  simp only [koszulOrder, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toLinearMap,
    koszulOrderMonoidAlgebra, Finsupp.lsingle_apply, LinearMap.coe_comp, Function.comp_apply,
    AlgEquiv.toLinearMap_apply]
  rw [AlgEquiv.symm_apply_eq]
  simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    AlgEquiv.ofAlgHom_apply, FreeAlgebra.lift_ι_apply]
  rw [@MonoidAlgebra.ext_iff]
  intro x
  erw [Finsupp.lift_apply]
  simp only [MonoidAlgebra.smul_single', List.insertionSort, List.orderedInsert,
    koszulSign_freeMonoid_of, mul_one, Finsupp.single_zero, Finsupp.sum_single_index]
  rfl


@[simp]
lemma koszulOrder_single {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (l : FreeMonoid I) :
    koszulOrder r q (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x))
    = FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
    (MonoidAlgebra.single (List.insertionSort r l) (koszulSign r q l * x)) := by
  simp [koszulOrder]

@[simp]
lemma koszulOrder_ι_pair  {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) (i j : I) :
    koszulOrder r q (FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j) =
    if r i j then FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j else
    (koszulSign r q [i, j]) • (FreeAlgebra.ι ℂ j * FreeAlgebra.ι ℂ i) := by
  have h1 : FreeAlgebra.ι ℂ i * FreeAlgebra.ι ℂ j =
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single [i, j] 1) := by
    simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
      AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
    rfl
  conv_lhs => rw [h1]
  simp only [koszulOrder, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.toAlgHom_toLinearMap,
    LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply,
    koszulOrderMonoidAlgebra_single, List.insertionSort, List.orderedInsert,
    MonoidAlgebra.smul_single', mul_one]
  by_cases hr : r i j
  · rw [if_pos hr, if_pos hr]
    simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
      AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single]
    have hKS : koszulSign r q [i, j] = 1 := by
      simp only [koszulSign, koszulSignInsert, Fin.isValue, mul_one, ite_eq_left_iff,
        ite_eq_right_iff, and_imp]
      exact fun a a_1 a_2 => False.elim (a hr)
    rw [hKS]
    simp only [one_smul]
    rfl
  · rw [if_neg hr, if_neg hr]
    simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
      AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single]
    rfl

@[simp]
lemma koszulOrder_one  {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) :
    koszulOrder r q 1 = 1 := by
  trans koszulOrder r q (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single [] 1))
  congr
  · simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
    rfl
  · simp only [koszulOrder_single, List.insertionSort, mul_one, EmbeddingLike.map_eq_one_iff]
    rfl

lemma mul_koszulOrder_le {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (i : I) (A : FreeAlgebra ℂ I) (hi : ∀ j, r i j) :
    FreeAlgebra.ι ℂ i * koszulOrder r q A = koszulOrder r q (FreeAlgebra.ι ℂ i * A) := by
  let f : FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I := {
    toFun := fun x => FreeAlgebra.ι ℂ i * x,
    map_add' := fun x y => by
      simp [mul_add],
    map_smul' := by simp}
  change (f ∘ₗ koszulOrder r q) A = (koszulOrder r q ∘ₗ f) _
  have f_single (l : FreeMonoid I) (x : ℂ) :
      f ((FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x)))
      = (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single (i :: l) x)) := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, f]
    have hf : FreeAlgebra.ι ℂ i = FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single [i] 1) := by
      simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
        AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
      rfl
    rw [hf]
    rw [@AlgEquiv.eq_symm_apply]
    simp only [map_mul, AlgEquiv.apply_symm_apply, MonoidAlgebra.single_mul_single, one_mul]
    rfl
  have h1 : f ∘ₗ koszulOrder r q = koszulOrder r q ∘ₗ f := by
    let e : FreeAlgebra ℂ I ≃ₗ[ℂ] MonoidAlgebra ℂ (FreeMonoid I) :=
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv
    apply (LinearEquiv.eq_comp_toLinearMap_iff (e₁₂ := e.symm) _ _).mp
    apply MonoidAlgebra.lhom_ext'
    intro l
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      MonoidAlgebra.lsingle_apply]
    erw [koszulOrder_single]
    rw [f_single]
    erw [f_single]
    rw [koszulOrder_single]
    congr 2
    · simp only [List.insertionSort]
      have hi (l : List I) : i :: l = List.orderedInsert r i l := by
        induction l with
        | nil => rfl
        | cons j l ih =>
          refine (List.orderedInsert_of_le r l (hi j)).symm
      exact hi _
    · congr 1
      rw [koszulSign]
      have h1 (l : List I) : koszulSignInsert r q i l = 1  := by
        exact koszulSignInsert_le_forall r q i l hi
      rw [h1]
      simp
  rw [h1]

lemma koszulOrder_mul_ge {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (i : I) (A : FreeAlgebra ℂ I) (hi : ∀ j, r j i) :
    koszulOrder r q A * FreeAlgebra.ι ℂ i  = koszulOrder r q (A * FreeAlgebra.ι ℂ i) := by
  let f : FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I := {
    toFun := fun x => x * FreeAlgebra.ι ℂ i ,
    map_add' := fun x y => by
      simp [add_mul],
    map_smul' := by simp}
  change (f ∘ₗ koszulOrder r q) A = (koszulOrder r q ∘ₗ f) A
  have f_single (l : FreeMonoid I) (x : ℂ) :
      f ((FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single l x)))
      = (FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single (l.toList ++ [i]) x)) := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, f]
    have hf : FreeAlgebra.ι ℂ i = FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single [i] 1) := by
      simp only [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
        AlgEquiv.ofAlgHom_symm_apply, MonoidAlgebra.lift_single, one_smul]
      rfl
    rw [hf]
    rw [@AlgEquiv.eq_symm_apply]
    simp only [map_mul, AlgEquiv.apply_symm_apply, MonoidAlgebra.single_mul_single, mul_one]
    rfl
  have h1 : f ∘ₗ koszulOrder r q = koszulOrder r q ∘ₗ f := by
    let e : FreeAlgebra ℂ I ≃ₗ[ℂ] MonoidAlgebra ℂ (FreeMonoid I) :=
      FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv
    apply (LinearEquiv.eq_comp_toLinearMap_iff (e₁₂ := e.symm) _ _).mp
    apply MonoidAlgebra.lhom_ext'
    intro l
    apply LinearMap.ext
    intro x
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      MonoidAlgebra.lsingle_apply]
    erw [koszulOrder_single]
    rw [f_single]
    erw [f_single]
    rw [koszulOrder_single]
    congr 3
    · change (List.insertionSort r l) ++ [i] = List.insertionSort r (l.toList ++ [i])
      have hoi (l : List I) (j : I) : List.orderedInsert r j (l ++ [i]) =
          List.orderedInsert r j l ++ [i] := by
        induction l with
        | nil => simp [hi]
        | cons b l ih =>
          simp only [List.orderedInsert, List.append_eq]
          by_cases hr : r j b
          · rw [if_pos hr, if_pos hr]
            rfl
          · rw [if_neg hr, if_neg hr]
            rw [ih]
            rfl
      have hI (l : List I) : (List.insertionSort r l) ++ [i] = List.insertionSort r (l ++ [i]) := by
        induction l with
        | nil => rfl
        | cons j l ih =>
          simp only [List.insertionSort, List.append_eq]
          rw [← ih]
          rw [hoi]
      rw [hI]
      rfl
    · have hI (l : List I) : koszulSign r q l = koszulSign r q (l ++ [i]) := by
        induction l with
        | nil => simp [koszulSign, koszulSignInsert]
        | cons j l ih =>
          simp only [koszulSign, List.append_eq]
          rw [ih]
          simp only [mul_eq_mul_right_iff]
          apply Or.inl
          rw [koszulSignInsert_ge_forall_append r q l j i hi]
      rw [hI]
      rfl
  rw [h1]

end
end Wick
