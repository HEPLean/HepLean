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
  | b :: l => if r a b then 1 else
    if q a = 1 ∧ q b = 1 then - koszulSignInsert r q a l else koszulSignInsert r q a l

/-- When inserting a boson the `koszulSignInsert` is always `1`. -/
lemma koszulSignInsert_boson {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) (a : I)
    (ha : q a = 0) : (l : List I) → koszulSignInsert r q a l = 1
  | [] => by
    simp [koszulSignInsert]
  | b :: l => by
    simp only [koszulSignInsert, Fin.isValue, ite_eq_left_iff]
    intro _
    simp only [ha, Fin.isValue, zero_ne_one, false_and, ↓reduceIte]
    exact koszulSignInsert_boson r q a ha l

/-- Gives a factor of `- 1` for every fermion-fermion (`q` is `1`) crossing that occurs when sorting
  a list of based on `r`. -/
def koszulSign {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2) :
    List I → ℂ
  | [] => 1
  | a :: l => koszulSignInsert r q a l * koszulSign r q l

@[simp]
lemma koszulSign_freeMonoid_of {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (i : I) : koszulSign r q (FreeMonoid.of i) = 1 := by
  change koszulSign r q [i] = 1
  simp only [koszulSign, mul_one]
  rfl

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
        induction l with
        | nil => rfl
        | cons j l ih =>
          simp only [koszulSignInsert, Fin.isValue, ite_eq_left_iff]
          intro h
          exact False.elim (h (hi j))
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
          have hKI (l : List I) (j : I) : koszulSignInsert r q j l = koszulSignInsert r q j (l ++ [i]) := by
            induction l with
            | nil => simp [koszulSignInsert, hi]
            | cons b l ih =>
              simp only [koszulSignInsert, Fin.isValue, List.append_eq]
              by_cases hr : r j b
              · rw [if_pos hr, if_pos hr]
              · rw [if_neg hr, if_neg hr]
                rw [ih]
          rw [hKI]
      rw [hI]
      rfl
  rw [h1]

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

def grade {I : Type} (q : I → Fin 2) : (l : List I) → Fin 2
  | [] => 0
  | a :: l => if q a = grade q l then 0 else 1

@[simp]
lemma grade_freeMonoid  {I : Type} (q : I → Fin 2) (i : I) : grade q (FreeMonoid.of i) = q i := by
  simp only [grade, Fin.isValue]
  have ha (a : Fin 2) : (if a = 0 then 0 else 1) = a := by
    fin_cases a <;> rfl
  rw [ha]

@[simp]
lemma grade_empty {I : Type} (q : I → Fin 2) : grade q [] = 0 := by
  simp [grade]

@[simp]
lemma grade_append {I : Type} (q : I → Fin 2) (l r : List I) :
    grade q (l ++ r) = if grade q l = grade q r then 0 else 1 := by
  induction l with
  | nil =>
    simp only [List.nil_append, grade_empty, Fin.isValue]
    have ha (a : Fin 2) : (if 0 = a then 0 else 1) = a := by
      fin_cases a <;> rfl
    exact Eq.symm (Fin.eq_of_val_eq (congrArg Fin.val (ha (grade q r))))
  | cons a l ih =>
    simp only [grade, List.append_eq, Fin.isValue]
    erw [ih]
    have hab (a b c : Fin 2) : (if a = if b = c then 0 else 1 then (0 : Fin 2) else 1) =
         if (if a = b then 0 else 1) = c then 0 else 1 := by
      fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
    exact hab (q a) (grade q l) (grade q r)

lemma grade_orderedInsert {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (l : List I) ( i : I ) :
    grade q (List.orderedInsert le1 i l) = grade q (i :: l) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp
    by_cases hij : le1 i j
    · simp [hij]
    · simp [hij]
      rw [grade]
      rw [ih]
      simp [grade]
      have h1 (a b c : Fin 2) : (if a = if b = c then 0 else 1 then (0 : Fin 2) else 1) = if b = if a = c then 0 else 1 then 0 else 1 := by
        fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl
      exact h1 _ _ _

@[simp]
lemma grade_insertionSort {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1] (l : List I) :
    grade q (List.insertionSort le1 l) = grade q l := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp [grade]
    rw [grade_orderedInsert]
    simp [grade]
    rw [ih]

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

lemma equivMonoidAlgebraFreeMonoid_freeAlgebra  {I : Type}  (i  : I) :
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (FreeAlgebra.ι ℂ i)) = Finsupp.single (FreeMonoid.of i) 1  := by
  simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.single]

@[simp]
lemma superCommute_ι {I : Type} (q : I → Fin 2)  (i j  : I)  :
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

lemma superCommute_ofList_ofList  {I : Type} (q : I → Fin 2)  (l r  : List I) (x y : ℂ) :
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
  have h1 : FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single [] 1) = (1 : FreeAlgebra ℂ I) := by
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

def superCommuteCoef {I : Type} (q : I → Fin 2) (la lb : List I) : ℂ :=
  if grade q la = 1 ∧ grade q lb = 1 then - 1 else  1

lemma superCommuteCoef_empty {I : Type} (q : I → Fin 2) (la : List I) :
    superCommuteCoef q la [] = 1 := by
  simp only [superCommuteCoef, Fin.isValue, grade_empty, zero_ne_one, and_false, ↓reduceIte]

lemma superCommuteCoef_append {I : Type} (q : I → Fin 2) (la lb lc  : List I) :
    superCommuteCoef q la (lb ++ lc) = superCommuteCoef q la lb * superCommuteCoef q la lc := by
  simp only [superCommuteCoef, Fin.isValue, grade_append, ite_eq_right_iff, zero_ne_one, imp_false,
    mul_ite, mul_neg, mul_one]
  by_cases hla : grade q la = 1
  · by_cases hlb : grade q lb = 1
    · by_cases hlc : grade q lc = 1
      · simp [hlc, hlb, hla]
      · have hc : grade q lc = 0 := by
          omega
        simp [hc, hlb, hla]
    · have hb : grade q lb = 0 := by
        omega
      by_cases hlc : grade q lc = 1
      · simp [hlc, hb]
      · have hc : grade q lc = 0 := by
          omega
        simp [hc, hb]
  · have ha : grade q la = 0 := by
      omega
    simp [ha]

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
      · have hc : grade q lc  = 0 := by
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
      · have hc : grade q lc  = 0 := by
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

lemma superCommute_ofList_cons {I : Type} (q : I → Fin 2) (la lb : List I) (xa xb : ℂ) (b1 : I) :
    superCommute q (ofList la xa) (ofList (b1 :: lb) xb) =
    superCommute q (ofList la xa) (FreeAlgebra.ι ℂ b1) * ofList lb xb +
    superCommuteCoef q la [b1] •
    (ofList [b1] 1) * superCommute q (ofList la xa) (ofList lb xb) := by
  rw [ofList_cons_eq_ofList]
  rw [superCommute_ofList_mul]
  congr
  · exact ofList_singleton b1

lemma superCommute_ofList_sum  {I : Type} (q : I → Fin 2) (la lb : List I) (xa xb : ℂ) :
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
    have h0 :  ((superCommute q) (ofList la xa)) (FreeAlgebra.ι ℂ b) * ofList lb xb  =
        superCommuteTake q la (b :: lb) xa xb 0 (Nat.zero_lt_succ lb.length) := by
      simp [superCommuteTake, superCommuteCoef_empty, ofList_empty]
    rw [h0]
    have hf (f : Fin (b :: lb).length → FreeAlgebra ℂ I) : ∑ n, f n =  f ⟨0,
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

lemma koszulOrder_superCommute_le {I : Type} (r : I → I → Prop) [DecidableRel r] (q : I → Fin 2)
    (i j : I) (hle : r i j) (a1 a2 : FreeAlgebra ℂ I) :
    koszulOrder r q (a1 * superCommute q (FreeAlgebra.ι ℂ i) (FreeAlgebra.ι ℂ j) * a2) =
    0 := by
  sorry

def freeAlgebraMap {I : Type} (f : I → Type) [∀ i, Fintype (f i)] :
    FreeAlgebra ℂ I →ₐ[ℂ] FreeAlgebra ℂ (Σ i, f i) :=
  FreeAlgebra.lift ℂ fun i => ∑ (j : f i), FreeAlgebra.ι ℂ ⟨i, j⟩

lemma freeAlgebraMap_ι {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I)  :
    freeAlgebraMap f (FreeAlgebra.ι ℂ i) = ∑ (b : f i), FreeAlgebra.ι ℂ ⟨i, b⟩ := by
  simp [freeAlgebraMap]

def ofListM {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (l : List I) (x : ℂ) :
    FreeAlgebra ℂ (Σ i, f i) :=
  freeAlgebraMap f (ofList l x)

lemma ofListM_empty  {I : Type} (f : I → Type) [∀ i, Fintype (f i)] :
  ofListM f [] 1 = 1 := by
  simp only [ofListM, EmbeddingLike.map_eq_one_iff]
  rw [ofList_empty]
  exact map_one (freeAlgebraMap f)

def liftM {I : Type} (f : I → Type) [∀ i, Fintype (f i)]  :
    (l : List I) →  (a : Π i, f (l.get i)) →  List (Σ i, f i)
  | [], _ => []
  | i :: l, a => ⟨i, a ⟨0, Nat.zero_lt_succ l.length⟩⟩ :: liftM f l (fun i => a (Fin.succ i))

@[simp]
lemma liftM_length {I : Type} (f : I → Type) [∀ i, Fintype (f i)]  (r : List I) (a : Π i, f (r.get i)) :
    (liftM f r a).length = r.length := by
  induction r with
  | nil => rfl
  | cons i r ih =>
    simp only [liftM, List.length_cons, Fin.zero_eta, add_left_inj]
    rw [ih]


lemma liftM_get {I : Type} (f : I → Type) [∀ i, Fintype (f i)]  (r : List I) (a : Π i, f (r.get i)) :
    (liftM f r a).get = (fun i => ⟨r.get i, a i⟩) ∘ Fin.cast (by simp) := by
  induction r with
  | nil =>
    funext i
    exact Fin.elim0 i
  | cons i l ih =>
    simp only [liftM, List.length_cons, Fin.zero_eta, List.get_eq_getElem]
    funext x
    match x with
    | ⟨0, h⟩ => rfl
    | ⟨x + 1, h⟩ =>
      simp only [List.length_cons, List.get_eq_getElem, Prod.mk.eta, List.getElem_cons_succ,
        Function.comp_apply, Fin.cast_mk]
      change (liftM f _ _).get _ = _
      rw [ih]
      simp


@[simp]
lemma liftM_grade {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (r : List I) (a : Π i, f (r.get i))  :
    grade (fun i => q i.fst) (liftM f r a) = 1 ↔ grade q r = 1 := by
  induction r with
  | nil =>
    simp [liftM]
  | cons i r ih =>
    simp only [grade, Fin.isValue, ite_eq_right_iff, zero_ne_one, imp_false]
    have ih' := ih (fun i => a i.succ)
    have h1 : grade (fun i => q i.fst) (liftM f r fun i => a i.succ) = grade q r  := by
      by_cases h : grade q r = 1
      · simp_all
      · have h0 : grade q r = 0 := by
          omega
        rw [h0] at ih'
        simp only [Fin.isValue, zero_ne_one, iff_false] at ih'
        have h0' : grade (fun i => q i.fst) (liftM f r fun i => a i.succ)  = 0 := by
          omega
        rw [h0, h0']
    rw [h1]

lemma liftM_grade_take {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) : (r : List I) →  (a : Π i, f (r.get i)) → (n : ℕ) →
    grade (fun i => q i.fst) (List.take n (liftM f r a)) = grade q (List.take n r)
  | [], _, _ => by
    simp [liftM]
  | i :: r, a, 0 => by
    simp
  | i :: r, a, Nat.succ n => by
    simp only [grade, Fin.isValue]
    have ih : grade (fun i => q i.fst) (List.take n (liftM f r fun i => a i.succ))  = grade q (List.take n r) := by
      refine (liftM_grade_take q r (fun i => a i.succ) n)
    rw [ih]



lemma ofListM_cons {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) (r : List I)  (x : ℂ) :
    ofListM f (i :: r) x = (∑ j : f i, FreeAlgebra.ι ℂ ⟨i, j⟩) * (ofListM f r x) := by
  rw [ofListM, ofList_cons_eq_ofList, ofList_singleton, map_mul]
  conv_lhs => lhs; rw [freeAlgebraMap]
  rw [ofListM]
  simp

lemma ofListM_singleton {I : Type} (f : I → Type) [∀ i, Fintype (f i)] (i : I) (x : ℂ) :
    ofListM f [i] x = ∑ j : f i, x • FreeAlgebra.ι ℂ ⟨i, j⟩ := by
  simp only [ofListM]
  rw [ofList_eq_smul_one, ofList_singleton, map_smul]
  rw [freeAlgebraMap_ι]
  rw [Finset.smul_sum]

lemma ofListM_expand {I : Type} (f : I → Type) [∀ i, Fintype (f i)]  (x : ℂ) :
    (l : List I) → ofListM f l x = ∑ (a : Π i, f (l.get i)), ofList (liftM f l a) x
  | [] => by
    simp only [ofListM, List.length_nil, List.get_eq_getElem, Finset.univ_unique, liftM,
      Finset.sum_const, Finset.card_singleton, one_smul]
    rw [ofList_eq_smul_one, map_smul, ofList_empty, ofList_eq_smul_one, ofList_empty, map_one]
  | i :: l => by
    rw [ofListM_cons, ofListM_expand f x l]
    let e1 :  f i × (Π j, f (l.get j)) ≃ (Π j, f ((i :: l).get j)) :=
      (Fin.insertNthEquiv (fun j => f ((i :: l).get j)) 0)
    rw [← e1.sum_comp (α := FreeAlgebra ℂ _)]
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

lemma superCommute_ofList_ofListM  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
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
  · exact ofList_pair l (liftM f r a) x y
  congr 1
  · simp
  · exact ofList_pair (liftM f r a) l y x
  · rw [ofList_pair]
    simp only [neg_mul]

def superCommuteCoefM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) : ℂ :=
    (if grade (fun i => q i.fst) l = 1 ∧ grade q r = 1 then -1 else 1)

lemma superCommuteCoefM_empty  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)):
    superCommuteCoefM q l [] = 1 := by
  simp [superCommuteCoefM]

lemma superCommute_ofList_ofListM_superCommuteCoefM  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    superCommute (fun i => q i.1) (ofList l x) (ofListM f r y) =
    ofList l x * ofListM f r y - superCommuteCoefM q l r • ofListM f r y * ofList l x := by
  rw [superCommute_ofList_ofListM, superCommuteCoefM]
  by_cases hq : grade (fun i => q i.fst) l = 1 ∧ grade q r = 1
  · simp [hq]
  · simp [hq]
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
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ)  (n : ℕ)
    (hn : n < r.length) : FreeAlgebra ℂ (Σ i, f i) :=
  superCommuteCoefM q l (List.take n r) •
  (ofListM f (List.take n r) 1 *
  superCommute (fun i => q i.1) (ofList l x) (freeAlgebraMap f (FreeAlgebra.ι ℂ (r.get ⟨n, hn⟩)))
  * ofListM f (List.drop (n + 1) r) y)

lemma SuperCommuteCenterMap.ofList_freeAlgebraMap {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
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


lemma superCommuteM_ofList_cons {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) (b1 : I) :
    superCommute (fun i => q i.1) (ofList l x) (ofListM f (b1 :: r) y) =
    superCommute (fun i => q i.1) (ofList l x) (freeAlgebraMap f (FreeAlgebra.ι ℂ b1)) * ofListM f r y +
    superCommuteCoefM q l [b1] •
    (ofListM f [b1] 1) * superCommute (fun i => q i.1) (ofList l x) (ofListM f r y) := by
  rw [ofListM_cons]
  conv_lhs =>
    rhs
    rw [ofListM_expand]
    rw [Finset.mul_sum]
  rw [map_sum]
  trans ∑ n, ∑ j : f b1, ((superCommute fun i => q i.fst) (ofList l x)) (( FreeAlgebra.ι ℂ ⟨b1, j⟩) * ofList (liftM f r n) y)
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
  trans ((superCommute fun i => q i.fst) (ofList l x)) (ofList (⟨b1, b⟩ :: liftM f r n) y)
  · congr
    rw [ofList_cons_eq_ofList]
    rw [ofList_singleton]
  rw [superCommute_ofList_cons]
  congr
  rw [ofList_singleton]
  simp


lemma superCommute_ofList_ofListM_sum  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (l : List (Σ i, f i)) (r : List I) (x y : ℂ) :
    superCommute (fun i => q i.1) (ofList l x) (ofListM f r y) =
    ∑ (n : Fin r.length), superCommuteTakeM q l r x y n n.prop  := by
  induction r with
  | nil =>
    simp only [superCommute_ofList_ofListM, Fin.isValue, grade_empty, zero_ne_one, and_false,
      ↓reduceIte, neg_mul, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
    rw [ofListM, ofList_empty']
    simp
  | cons b r ih =>
    rw [superCommuteM_ofList_cons]
    have h0 :  ((superCommute fun i => q i.fst) (ofList l x)) ((freeAlgebraMap f) (FreeAlgebra.ι ℂ b)) * ofListM f r y  =
        superCommuteTakeM q l (b :: r) x y 0 (Nat.zero_lt_succ r.length) := by
      simp [superCommuteTakeM, superCommuteCoefM_empty, ofListM_empty]
    rw [h0]
    have hf (g : Fin (b :: r).length → FreeAlgebra ℂ ((i : I) × f i)) : ∑ n, g n =  g ⟨0,
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

def contract {I : Type} (q : I → Fin 2) (le1 : I → I → Prop) (le2 : I → I → Prop)
    [DecidableRel le1] [DecidableRel le2] :
    FreeAlgebra ℂ I →ₗ[ℂ] FreeAlgebra ℂ I :=
  koszulOrder le1 q - koszulOrder le2 q


lemma koszulSignInsert_liftM  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (a : (j : Fin l.length) → f (l.get j)) (x : (i : I) × f i):
    koszulSignInsert (fun i j => le1 i.fst j.fst) (fun i => q i.fst) x
      (liftM f l a)  =
    koszulSignInsert le1 q x.1 l := by
  induction l with
  | nil => simp [koszulSignInsert]
  | cons b l ih =>
    simp [koszulSignInsert]
    rw [ih]


lemma koszulSign_liftM  {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (a : (i : Fin l.length) → f (l.get i)) :
    koszulSign (fun i j => le1 i.fst j.fst) (fun i => q i.fst) (liftM f l a) =
    koszulSign le1 q l := by
  induction l with
  | nil => simp [koszulSign]
  | cons i l ih =>
    simp [koszulSign, liftM]
    rw [ih]
    congr 1
    rw [koszulSignInsert_liftM]

lemma insertionSortEquiv_liftM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (le1 : I → I → Prop) [DecidableRel le1](l : List I)  (a : (i : Fin l.length) → f (l.get i))  :
    (HepLean.List.insertionSortEquiv (fun i j => le1 i.fst j.fst) (liftM f l a)) =
    (Fin.castOrderIso (by simp)).toEquiv.trans ((HepLean.List.insertionSortEquiv le1 l).trans
    (Fin.castOrderIso (by simp)).toEquiv) := by
  induction l with
  | nil =>
    simp [liftM, HepLean.List.insertionSortEquiv]
  | cons i l ih =>
    simp only [liftM, List.length_cons, Fin.zero_eta, List.insertionSort]
    conv_lhs => simp [HepLean.List.insertionSortEquiv]
    have h1 (l' : List (Σ i, f i)) :
        (HepLean.List.insertEquiv  (fun i j => le1 i.fst j.fst) ⟨i, a ⟨0, by simp⟩⟩ l') =
        (Fin.castOrderIso (by simp)).toEquiv.trans
        ((HepLean.List.insertEquiv le1 i (List.map (fun i => i.1) l')).trans
        (Fin.castOrderIso (by simp [List.orderedInsert_length])).toEquiv) := by
      induction l' with
      | nil =>
        simp only [List.length_cons, Nat.add_zero, Nat.zero_eq, Fin.zero_eta, List.length_singleton,
          List.orderedInsert, HepLean.List.insertEquiv, Fin.castOrderIso_refl,
          OrderIso.refl_toEquiv, Equiv.trans_refl]
        rfl
      | cons j l' ih' =>
        by_cases hr : (fun (i j : Σ i, f i) => le1 i.fst j.fst) ⟨i, a ⟨0, by simp⟩⟩  j
        · rw [HepLean.List.insertEquiv_cons_pos]
          · erw [HepLean.List.insertEquiv_cons_pos]
            · rfl
            · exact hr
          · exact hr
        · rw [HepLean.List.insertEquiv_cons_neg]
          · erw [HepLean.List.insertEquiv_cons_neg]
            · simp only [List.length_cons, Nat.add_zero, Nat.zero_eq, Fin.zero_eta,
              List.orderedInsert, Prod.mk.eta, Fin.mk_one]
              erw [ih']
              ext x
              simp only [Prod.mk.eta, List.length_cons, Nat.add_zero, Nat.zero_eq, Fin.zero_eta,
                HepLean.Fin.equivCons_trans, Nat.succ_eq_add_one,
                HepLean.Fin.equivCons_castOrderIso, Equiv.trans_apply, RelIso.coe_fn_toEquiv,
                Fin.castOrderIso_apply, Fin.cast_trans, Fin.coe_cast]
              congr 2
              match x with
              | ⟨0, h⟩ => rfl
              | ⟨1, h⟩ => rfl
              | ⟨Nat.succ (Nat.succ x), h⟩ => rfl
            · exact hr
          · exact hr
    erw [h1]
    rw [ih]
    simp only [HepLean.Fin.equivCons_trans, Nat.succ_eq_add_one,
      HepLean.Fin.equivCons_castOrderIso, List.length_cons, Nat.add_zero, Nat.zero_eq,
      Fin.zero_eta]
    ext x
    conv_rhs => simp [HepLean.List.insertionSortEquiv]
    simp only [Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply, Fin.cast_trans,
      Fin.coe_cast]
    have h2' (i : Σ i, f i) (l' : List ( Σ i, f i)) :
      List.map (fun i => i.1) (List.orderedInsert (fun i j => le1 i.fst j.fst) i l') =
      List.orderedInsert le1 i.1 (List.map (fun i => i.1) l') := by
      induction l' with
      | nil =>
        simp [HepLean.List.insertEquiv]
      | cons j l' ih' =>
        by_cases hij : (fun i j => le1 i.fst j.fst)  i j
        · rw [List.orderedInsert_of_le]
          · erw [List.orderedInsert_of_le]
            · simp
            · exact hij
          · exact hij
        · simp only [List.orderedInsert, hij, ↓reduceIte, List.unzip_snd, List.map_cons]
          have hn : ¬ le1 i.1 j.1 := hij
          simp only [hn, ↓reduceIte, List.cons.injEq, true_and]
          simpa using ih'
    have h2 (l' : List ( Σ i, f i)) :
        List.map (fun i => i.1) (List.insertionSort (fun i j => le1 i.fst j.fst) l') =
        List.insertionSort le1 (List.map (fun i => i.1) l') := by
      induction l' with
      | nil =>
        simp [HepLean.List.insertEquiv]
      | cons i l' ih' =>
        simp only [List.insertionSort, List.unzip_snd]
        simp only [List.unzip_snd] at h2'
        rw [h2']
        congr
    rw [HepLean.List.insertEquiv_congr _ _ _ (h2 _)]
    simp only [List.length_cons, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.coe_cast]
    have h3 : (List.insertionSort le1 (List.map (fun i => i.1) (liftM f l (fun i => a i.succ)))) =
      List.insertionSort le1 l := by
      congr
      have h3' (l : List I) (a : Π (i : Fin l.length), f (l.get i)) :
        List.map (fun i => i.1) (liftM f l a) = l := by
        induction l with
        | nil => rfl
        | cons i l ih' =>
          simp only [liftM, List.length_cons, Fin.zero_eta, Prod.mk.eta,
            List.unzip_snd, List.map_cons, List.cons.injEq, true_and]
          simpa using ih' _
      rw [h3']
    rw [HepLean.List.insertEquiv_congr _ _ _ h3]
    simp only [List.length_cons, Equiv.trans_apply, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.cast_eq_self, Fin.coe_cast]

lemma insertionSort_liftM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (le1 : I → I → Prop) [DecidableRel le1](l : List I)  (a : (i : Fin l.length) → f (l.get i))
    :
    List.insertionSort (fun i j => le1 i.fst j.fst) (liftM f l a) =
    liftM f (List.insertionSort le1 l)
    (Equiv.piCongr (HepLean.List.insertionSortEquiv le1 l) (fun i => (Equiv.cast (by
      congr 1
      rw [← HepLean.List.insertionSortEquiv_get]
      simp))) a) := by
  let l1 := List.insertionSort (fun i j => le1 i.fst j.fst) (liftM f l a)
  let l2 := liftM f (List.insertionSort le1 l)
    (Equiv.piCongr (HepLean.List.insertionSortEquiv le1 l) (fun i => (Equiv.cast (by
      congr 1
      rw [← HepLean.List.insertionSortEquiv_get]
      simp))) a)
  change l1 = l2
  have hlen : l1.length = l2.length := by
    simp [l1, l2]
  have hget : l1.get = l2.get ∘ Fin.cast hlen := by
    rw [← HepLean.List.insertionSortEquiv_get]
    rw [liftM_get, liftM_get]
    funext i
    rw [insertionSortEquiv_liftM]
    simp only [ Function.comp_apply, Equiv.symm_trans_apply,
      OrderIso.toEquiv_symm, Fin.symm_castOrderIso, RelIso.coe_fn_toEquiv, Fin.castOrderIso_apply,
      Fin.cast_trans, Fin.cast_eq_self, id_eq, eq_mpr_eq_cast, Fin.coe_cast, Sigma.mk.inj_iff]
    apply And.intro
    · have h1 := congrFun (HepLean.List.insertionSortEquiv_get (r := le1) l) (Fin.cast (by simp) i)
      rw [← h1]
      simp
    · simp [Equiv.piCongr]
      exact (cast_heq _ _).symm
  apply List.ext_get hlen
  rw [hget]
  simp

lemma koszulOrder_ofListM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (x : ℂ) : koszulOrder (fun i j => le1 i.1 j.1) (fun i => q i.fst) (ofListM f l x) =
    freeAlgebraMap f (koszulOrder le1 q (ofList l x)) := by
  rw [koszulOrder_ofList]
  rw [map_smul]
  change _ = _ • ofListM _ _ _
  rw [ofListM_expand]
  rw [map_sum]
  conv_lhs =>
    rhs
    intro a
    rw [koszulOrder_ofList]
    rw [koszulSign_liftM]
  rw [← Finset.smul_sum]
  apply congrArg
  conv_lhs =>
    rhs
    intro n
    rw [insertionSort_liftM]
  rw [ofListM_expand]
  refine Fintype.sum_equiv ((HepLean.List.insertionSortEquiv le1 l).piCongr fun i => Equiv.cast ?_) _ _ ?_
  congr 1
  · rw [← HepLean.List.insertionSortEquiv_get]
    simp
  · intro x
    rfl

lemma koszulOrder_ofListM_eq_ofListM {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (le1 : I → I → Prop) [DecidableRel le1]
    (l : List I) (x : ℂ) : koszulOrder (fun i j => le1 i.1 j.1) (fun i => q i.fst) (ofListM f l x) =
    koszulSign le1 q l • ofListM f (List.insertionSort le1 l) x := by
  rw [koszulOrder_ofListM, koszulOrder_ofList, map_smul]
  rfl

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


def optionErase {I : Type} (l : List I) (i : Option (Fin l.length)) : List I :=
  match i with
  | none => l
  | some i => List.eraseIdx l i

inductive ContractionsAux {I : Type} : (l : List I) → (aux : List I) → Type
  | nil : ContractionsAux [] []
  | single {a : I} : ContractionsAux [a] [a]
  | cons {l : List I} {aux : List I} {a b: I} (i : Option (Fin (b :: aux).length)) :
    ContractionsAux (b :: l) aux → ContractionsAux (a :: b :: l) (optionErase (b :: aux) i)

def Contractions {I : Type} (l : List I) : Type := Σ aux, ContractionsAux l aux

namespace Contractions

variable {I : Type} {l : List I} (c : Contractions l)

def normalize : List I := c.1

lemma normalize_length_le : c.normalize.length ≤ l.length := by
  cases c
  rename_i aux c
  induction c with
  | nil =>
    simp [normalize]
  | single =>
    simp [normalize]
  | cons i c ih =>
    simp [normalize, optionErase]
    match i with
    | none =>
      simpa using ih
    | some i =>
      simp
      rw [List.length_eraseIdx]
      simp [normalize] at ih
      simp
      exact Nat.le_add_right_of_le ih

lemma contractions_nil (a : Contractions ([] : List I)) : a = ⟨[], ContractionsAux.nil⟩ := by
  cases a
  rename_i aux c
  cases c
  rfl

lemma contractions_single {i : I} (a : Contractions [i]) : a = ⟨[i], ContractionsAux.single⟩ := by
  cases a
  rename_i aux c
  cases c
  rfl

def consConsEquiv {a b : I} {l : List I} :
    Contractions (a :: b :: l) ≃ (c : Contractions (b :: l)) × Option (Fin (b :: c.normalize).length) where
  toFun c :=
    match c with
    | ⟨aux, c⟩ =>
    match c with
    | ContractionsAux.cons (aux := aux') i c => ⟨⟨aux', c⟩, i⟩
  invFun ci :=
    ⟨(optionErase (b :: ci.fst.normalize) ci.2), ContractionsAux.cons (a := a) ci.2 ci.1.2⟩
  left_inv c := by
    match c with
    | ⟨aux, c⟩ =>
    match c with
    | ContractionsAux.cons (aux := aux') i c => rfl
  right_inv ci := by rfl


instance decidable : (l : List I) → DecidableEq (Contractions l)
  | [] => fun a b =>
    match a, b with
    | ⟨_, a⟩, ⟨_, b⟩ =>
    match a, b with
    | ContractionsAux.nil , ContractionsAux.nil => isTrue rfl
  | _ :: [] => fun a b =>
    match a, b with
    | ⟨_, a⟩, ⟨_, b⟩ =>
    match a, b with
    | ContractionsAux.single , ContractionsAux.single => isTrue rfl
  | _ :: b :: l =>
    haveI : DecidableEq (Contractions (b :: l)) := decidable (b :: l)
    haveI : DecidableEq ((c : Contractions (b :: l)) × Option (Fin (b :: c.normalize).length)) :=
      Sigma.instDecidableEqSigma
    Equiv.decidableEq consConsEquiv


instance fintype  : (l : List I) → Fintype (Contractions l)
  | [] => {
    elems := {⟨[], ContractionsAux.nil⟩}
    complete := by
      intro a
      rw [Finset.mem_singleton]
      exact contractions_nil a}
  | a :: [] => {
    elems := {⟨[a], ContractionsAux.single⟩}
    complete := by
      intro a
      rw [Finset.mem_singleton]
      exact contractions_single a}
  | a :: b :: l =>
    haveI : Fintype (Contractions (b :: l)) := fintype (b :: l)
    haveI : Fintype ((c : Contractions (b :: l)) × Option (Fin (b :: c.normalize).length)) :=
      Sigma.instFintype
    Fintype.ofEquiv _ consConsEquiv.symm

end Contractions

lemma wick_nil {I : Type} {f : I → Type} [∀ i, Fintype (f i)]
    (q : I → Fin 2) (r : List I) (x : ℂ)
    (le1 : (Σ i, f i) → (Σ i, f i) → Prop) [DecidableRel le1]
    (tle : I → I → Prop) [DecidableRel tle]
    (i : (Σ i, f i)) (hi : ∀ j, le1 j i)
    {A : Type} [Semiring A] [Algebra ℂ A]
    (F : FreeAlgebra ℂ (Σ i, f i) →ₐ A) [SuperCommuteCenterMap F] :
    F (koszulOrder (fun i j => tle i.1 j.1) (fun i => q i.fst) (ofListM f [] x)) =
    ∑ (c : Contractions (I := I) []), c.toTerm  := by
end
end Wick
